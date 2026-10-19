/*
  AmbientMapper v2 - ESP32-S3

  Learns a graph of familiar places from passive Wi-Fi AP fingerprints.
  - Dynamic place and edge vectors (no fixed 12-place limit).
  - Persists the database in the LittleFS flash filesystem.
  - Stores hashes of BSSIDs and RSSI values, not SSIDs or raw BSSIDs.
  - Confirms a different known place over multiple scans before changing location.
  - Requires repeated, mutually similar unknown scans before creating a new place.
  - Counts visits on confirmed entries, not on every scan.
  - Keeps the original AmbientMapper BLE service UUIDs and command names.

  Important limits:
  There is no literally unlimited storage. Available flash, RAM, and the selected
  partition scheme limit the database. The code refuses new records when it cannot
  safely grow its in-memory index instead of deliberately running out of memory.

  Arduino IDE: select your ESP32-S3 board and a partition scheme that includes
  a SPIFFS/LittleFS data partition. Uses only the ESP32 Arduino core libraries.
*/

#include <Arduino.h>
#include <WiFi.h>
#include <LittleFS.h>
#include <Preferences.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>
#include <vector>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include "esp_heap_caps.h"

static const char *BLE_NAME = "AmbientMapper";
static const char *SERVICE_UUID = "6e400001-b5a3-f393-e0a9-e50e24dcca9e";
static const char *RX_UUID      = "6e400002-b5a3-f393-e0a9-e50e24dcca9e";
static const char *TX_UUID      = "6e400003-b5a3-f393-e0a9-e50e24dcca9e";

static const char *DB_PATH  = "/ambient.db";
static const char *TMP_PATH = "/ambient.tmp";
static const char *BAK_PATH = "/ambient.bak";

static constexpr uint8_t MAX_APS = 10;
static constexpr uint32_t SCAN_INTERVAL_MS = 30000UL;
static constexpr uint32_t SAVE_INTERVAL_MS = 120000UL;
static constexpr float MATCH_THRESHOLD = 0.44f;
static constexpr float PENDING_SIMILARITY = 0.32f;
static constexpr uint8_t KNOWN_CONFIRM_SCANS = 2;
static constexpr uint8_t NEW_PLACE_CONFIRM_SCANS = 5;
static constexpr uint8_t NEW_PLACE_BORDERLINE_SCANS = 6;
static constexpr uint32_t NEW_PLACE_MIN_STABLE_MS = 180000UL; // 3 minutes
static constexpr size_t BLE_PACKET_BYTES = 20;

struct APReading {
  uint32_t hash = 0;
  int8_t rssi = -100;
};

struct Fingerprint {
  APReading aps[MAX_APS];
  uint8_t count = 0;
};

struct Place {
  uint32_t id = 0;
  uint32_t visits = 0;
  uint32_t lastSeenMs = 0;   // Runtime-only: millis() resets after reboot.
  uint32_t lastVisitMs = 0;  // Runtime-only.
  char label[32] = {0};
  Fingerprint fp;
};

struct Edge {
  uint32_t from = 0;
  uint32_t to = 0;
  uint32_t count = 0;
  uint32_t lastSeenMs = 0;   // Runtime-only.
};

static std::vector<Place> places;
static std::vector<Edge> edges;
static uint32_t nextPlaceId = 1;
static uint32_t currentPlaceId = 0;
static bool trackingPaused = false;
static bool storageOK = false;
static bool databaseDirty = false;
static bool memoryLimitHit = false;
static bool forceSaveNow = false;
static uint32_t lastScanMs = 0;
static uint32_t lastSaveMs = 0;
static uint8_t lastScanAPCount = 0;
static uint32_t totalScans = 0;

static Fingerprint pendingNewFingerprint;
static uint8_t pendingNewCount = 0;
static uint32_t pendingNewSinceMs = 0;
static uint32_t pendingKnownPlaceId = 0;
static uint8_t pendingKnownCount = 0;

static BLEServer *bleServer = nullptr;
static BLECharacteristic *txCharacteristic = nullptr;
static volatile bool bleConnected = false;
static portMUX_TYPE commandMux = portMUX_INITIALIZER_UNLOCKED;
static char pendingCommand[96] = {0};
static volatile bool commandPending = false;

// ----- Small helpers -----

static void copySanitized(char *dest, size_t capacity, const char *src) {
  if (!dest || capacity == 0) return;
  size_t out = 0;
  if (src) {
    for (size_t i = 0; src[i] && out + 1 < capacity; ++i) {
      char c = src[i];
      if (c == '\t' || c == '\r' || c == '\n' || c == '|') c = ' ';
      if ((uint8_t)c < 32) continue;
      dest[out++] = c;
    }
  }
  while (out > 0 && dest[out - 1] == ' ') --out;
  dest[out] = '\0';
}

static uint32_t hashBssid(const uint8_t *mac) {
  // FNV-1a 32-bit hash. Raw access-point addresses are never persisted or sent.
  uint32_t h = 2166136261UL;
  for (uint8_t i = 0; i < 6; ++i) {
    h ^= mac[i];
    h *= 16777619UL;
  }
  return h == 0 ? 1 : h;
}

static int findPlaceIndex(uint32_t id) {
  for (size_t i = 0; i < places.size(); ++i) {
    if (places[i].id == id) return (int)i;
  }
  return -1;
}

static Place *findPlace(uint32_t id) {
  int i = findPlaceIndex(id);
  return i >= 0 ? &places[(size_t)i] : nullptr;
}

static bool ensurePlaceCapacity() {
  if (places.size() < places.capacity()) return true;
  size_t newCapacity = places.capacity() == 0 ? 8 : places.capacity() * 2;
  size_t required = newCapacity * sizeof(Place);
  // Reallocation needs room for the new block before the old block can be freed.
  size_t largest = heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
  if (largest < required + 4096 || ESP.getFreeHeap() < required + 12000) {
    memoryLimitHit = true;
    return false;
  }
  places.reserve(newCapacity);
  return places.capacity() >= newCapacity;
}

static bool ensureEdgeCapacity() {
  if (edges.size() < edges.capacity()) return true;
  size_t newCapacity = edges.capacity() == 0 ? 16 : edges.capacity() * 2;
  size_t required = newCapacity * sizeof(Edge);
  size_t largest = heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
  if (largest < required + 2048 || ESP.getFreeHeap() < required + 10000) {
    memoryLimitHit = true;
    return false;
  }
  edges.reserve(newCapacity);
  return edges.capacity() >= newCapacity;
}


static bool addReading(Fingerprint &fp, uint32_t hash, int rssi) {
  if (hash == 0) return false;
  for (uint8_t i = 0; i < fp.count; ++i) {
    if (fp.aps[i].hash == hash) {
      fp.aps[i].rssi = (int8_t)rssi;
      return true;
    }
  }
  if (fp.count < MAX_APS) {
    fp.aps[fp.count].hash = hash;
    fp.aps[fp.count].rssi = (int8_t)rssi;
    ++fp.count;
    return true;
  }
  // Keep the ten strongest distinct APs in the fingerprint.
  uint8_t weakest = 0;
  for (uint8_t i = 1; i < fp.count; ++i) {
    if (fp.aps[i].rssi < fp.aps[weakest].rssi) weakest = i;
  }
  if (rssi > fp.aps[weakest].rssi + 6) {
    fp.aps[weakest].hash = hash;
    fp.aps[weakest].rssi = (int8_t)rssi;
    return true;
  }
  return false;
}

static Fingerprint scanFingerprint() {
  Fingerprint fp;
  int n = WiFi.scanNetworks(false, true, true, 110);
  if (n < 0) {
    Serial.printf("Wi-Fi passive scan failed: %d\n", n);
    WiFi.scanDelete();
    return fp;
  }
  for (int i = 0; i < n; ++i) {
    const uint8_t *mac = WiFi.BSSID(i);
    if (!mac) continue;
    addReading(fp, hashBssid(mac), WiFi.RSSI(i));
  }
  WiFi.scanDelete();
  return fp;
}

static int commonAPs(const Fingerprint &a, const Fingerprint &b, float &rssiQuality) {
  int common = 0;
  float qualitySum = 0.0f;
  for (uint8_t i = 0; i < a.count; ++i) {
    for (uint8_t j = 0; j < b.count; ++j) {
      if (a.aps[i].hash == b.aps[j].hash) {
        ++common;
        int delta = abs((int)a.aps[i].rssi - (int)b.aps[j].rssi);
        float q = 1.0f - ((float)delta / 50.0f);
        if (q < 0.0f) q = 0.0f;
        qualitySum += q;
        break;
      }
    }
  }
  rssiQuality = common ? qualitySum / (float)common : 0.0f;
  return common;
}

static float matchScore(const Fingerprint &a, const Fingerprint &b) {
  if (a.count == 0 || b.count == 0) return 0.0f;
  float rssiQuality = 0.0f;
  int common = commonAPs(a, b, rssiQuality);
  if (common == 0) return 0.0f;
  uint8_t denominator = a.count > b.count ? a.count : b.count;
  float coverage = (float)common / (float)denominator;
  // AP overlap carries most of the score; RSSI helps distinguish nearby places.
  return coverage * (0.70f + 0.30f * rssiQuality);
}

static void updateFingerprint(Fingerprint &known, const Fingerprint &observed) {
  for (uint8_t i = 0; i < observed.count; ++i) {
    bool found = false;
    for (uint8_t j = 0; j < known.count; ++j) {
      if (known.aps[j].hash == observed.aps[i].hash) {
        // Smooth RSSI noise instead of letting one scan rewrite the fingerprint.
        known.aps[j].rssi = (int8_t)(((int)known.aps[j].rssi * 3 + (int)observed.aps[i].rssi) / 4);
        found = true;
        break;
      }
    }
    if (!found) addReading(known, observed.aps[i].hash, observed.aps[i].rssi);
  }
}

static void clearPendingCandidates() {
  pendingNewCount = 0;
  pendingNewSinceMs = 0;
  pendingNewFingerprint.count = 0;
  pendingKnownPlaceId = 0;
  pendingKnownCount = 0;
}

static bool addOrIncrementEdge(uint32_t from, uint32_t to) {
  if (!from || !to || from == to) return true;
  for (size_t i = 0; i < edges.size(); ++i) {
    if (edges[i].from == from && edges[i].to == to) {
      if (edges[i].count < UINT32_MAX) ++edges[i].count;
      edges[i].lastSeenMs = millis();
      databaseDirty = true;
      return true;
    }
  }
  if (!ensureEdgeCapacity()) {
    Serial.println("Memory guard: no room for another route edge.");
    return false;
  }
  Edge e;
  e.from = from;
  e.to = to;
  e.count = 1;
  e.lastSeenMs = millis();
  edges.push_back(e);
  databaseDirty = true;
  return true;
}

static void enterPlace(uint32_t id) {
  if (!id) return;
  Place *target = findPlace(id);
  if (!target) return;
  if (currentPlaceId == id) {
    target->lastSeenMs = millis();
    return;
  }
  uint32_t previous = currentPlaceId;
  currentPlaceId = id;
  target->lastSeenMs = millis();
  target->lastVisitMs = millis();
  if (target->visits < UINT32_MAX) ++target->visits;
  databaseDirty = true;
  if (previous && previous != id) addOrIncrementEdge(previous, id);
  Serial.printf("Recognized location: id=%lu label=%s (visits=%lu)\n",
                (unsigned long)target->id, target->label,
                (unsigned long)target->visits);
}

static uint32_t createPlace(const Fingerprint &fp) {
  if (fp.count == 0 || !ensurePlaceCapacity()) return 0;
  Place p;
  p.id = nextPlaceId++;
  if (nextPlaceId == 0) nextPlaceId = 1;
  p.visits = 0;
  p.lastSeenMs = millis();
  p.lastVisitMs = 0;
  snprintf(p.label, sizeof(p.label), "Place %lu", (unsigned long)p.id);
  p.fp = fp;
  places.push_back(p);
  databaseDirty = true;
  forceSaveNow = true; // Newly learned places should survive an immediate power-off.
  Serial.printf("Created new learned place: id=%lu, APs=%u\n",
                (unsigned long)p.id, (unsigned)p.fp.count);
  enterPlace(p.id);
  return p.id;
}

static void processFingerprint(const Fingerprint &observed) {
  if (observed.count == 0) {
    // An empty scan cannot prove that an unknown fingerprint stayed stable.
    pendingNewCount = 0;
    pendingNewSinceMs = 0;
    pendingNewFingerprint.count = 0;
    pendingKnownPlaceId = 0;
    pendingKnownCount = 0;
    Serial.println("No access points in this scan; keeping current location and clearing pending candidates.");
    return;
  }

  int bestIndex = -1;
  float bestScore = 0.0f;
  float currentScore = 0.0f;
  for (size_t i = 0; i < places.size(); ++i) {
    float score = matchScore(places[i].fp, observed);
    if (places[i].id == currentPlaceId) currentScore = score;
    if (score > bestScore) {
      bestScore = score;
      bestIndex = (int)i;
    }
  }

  if (bestIndex >= 0 && bestScore >= MATCH_THRESHOLD) {
    uint32_t bestId = places[(size_t)bestIndex].id;
    pendingNewCount = 0;
    pendingNewSinceMs = 0;
    pendingNewFingerprint.count = 0;
    if (bestId == currentPlaceId) {
      pendingKnownPlaceId = 0;
      pendingKnownCount = 0;
      Place &p = places[(size_t)bestIndex];
      updateFingerprint(p.fp, observed);
      p.lastSeenMs = millis();
      databaseDirty = true;
      Serial.printf("Current place match score %.2f (place %lu)\n", bestScore, (unsigned long)bestId);
      return;
    }

    // Do not switch locations on one noisy scan: confirm the same candidate twice.
    if (pendingKnownPlaceId == bestId) {
      if (pendingKnownCount < 255) ++pendingKnownCount;
    } else {
      pendingKnownPlaceId = bestId;
      pendingKnownCount = 1;
    }
    if (pendingKnownCount >= KNOWN_CONFIRM_SCANS) {
      Place *p = findPlace(bestId);
      if (p) updateFingerprint(p->fp, observed);
      enterPlace(bestId);
      clearPendingCandidates();
    } else if (currentPlaceId) {
      Serial.printf("Possible move to place %lu (score %.2f); confirming...\n",
                    (unsigned long)bestId, bestScore);
    } else {
      Serial.printf("Possible place %lu (score %.2f); confirming...\n",
                    (unsigned long)bestId, bestScore);
    }
    return;
  }

  // No known place is convincing. If the current fingerprint is still moderately
  // similar, require extra stable scans before allowing a new place to be created.
  pendingKnownPlaceId = 0;
  pendingKnownCount = 0;
  if (pendingNewCount == 0 || matchScore(pendingNewFingerprint, observed) < PENDING_SIMILARITY) {
    pendingNewFingerprint = observed;
    pendingNewCount = 1;
    pendingNewSinceMs = millis();
  } else {
    updateFingerprint(pendingNewFingerprint, observed);
    if (pendingNewCount < 255) ++pendingNewCount;
  }

  uint8_t required = (currentPlaceId && currentScore >= 0.28f)
                       ? NEW_PLACE_BORDERLINE_SCANS
                       : NEW_PLACE_CONFIRM_SCANS;
  uint32_t stableForMs = pendingNewSinceMs ? (uint32_t)(millis() - pendingNewSinceMs) : 0;
  Serial.printf("Unmatched scan (best %.2f/current %.2f); stable samples %u/%u, stable for %lu/180 sec\n",
                bestScore, currentScore, pendingNewCount, required,
                (unsigned long)(stableForMs / 1000UL));
  if (pendingNewCount >= required && stableForMs >= NEW_PLACE_MIN_STABLE_MS) {
    Fingerprint confirmed = pendingNewFingerprint;
    uint32_t newId = createPlace(confirmed);
    if (newId) clearPendingCandidates();
  }
}

// ----- LittleFS database -----

static char *nextTabField(char *&cursor) {
  if (!cursor) return nullptr;
  char *out = cursor;
  char *tab = strchr(cursor, '\t');
  if (tab) {
    *tab = '\0';
    cursor = tab + 1;
  } else {
    cursor = nullptr;
  }
  return out;
}

static void parseAPList(Fingerprint &fp, char *apText) {
  fp.count = 0;
  if (!apText || !*apText) return;
  char *save = nullptr;
  for (char *item = strtok_r(apText, ";", &save); item; item = strtok_r(nullptr, ";", &save)) {
    char *comma = strchr(item, ',');
    if (!comma) continue;
    *comma = '\0';
    uint32_t hash = (uint32_t)strtoul(item, nullptr, 10);
    int rssi = atoi(comma + 1);
    if (hash) addReading(fp, hash, rssi);
  }
}

static void loadDbLine(char *line) {
  if (!line || !*line || line[0] == '#') return;
  if (strncmp(line, "AMBIENTMAP\t2", 12) == 0) return;

  char *cursor = line;
  char *kind = nextTabField(cursor);
  if (!kind) return;
  if (strcmp(kind, "P") == 0) {
    char *idText = nextTabField(cursor);
    char *visitsText = nextTabField(cursor);
    char *labelText = nextTabField(cursor);
    char *apsText = nextTabField(cursor);
    if (!idText || !visitsText || !labelText || !apsText) return;
    if (!ensurePlaceCapacity()) return;
    Place p;
    p.id = (uint32_t)strtoul(idText, nullptr, 10);
    p.visits = (uint32_t)strtoul(visitsText, nullptr, 10);
    copySanitized(p.label, sizeof(p.label), labelText);
    parseAPList(p.fp, apsText);
    if (p.id == 0 || p.fp.count == 0 || findPlaceIndex(p.id) >= 0) return;
    places.push_back(p);
    if (p.id >= nextPlaceId) nextPlaceId = p.id + 1;
  } else if (strcmp(kind, "E") == 0) {
    char *fromText = nextTabField(cursor);
    char *toText = nextTabField(cursor);
    char *countText = nextTabField(cursor);
    if (!fromText || !toText || !countText || !ensureEdgeCapacity()) return;
    Edge e;
    e.from = (uint32_t)strtoul(fromText, nullptr, 10);
    e.to = (uint32_t)strtoul(toText, nullptr, 10);
    e.count = (uint32_t)strtoul(countText, nullptr, 10);
    if (e.from && e.to && e.from != e.to && e.count) edges.push_back(e);
  }
}

static bool loadDatabase() {
  places.clear();
  edges.clear();
  nextPlaceId = 1;
  currentPlaceId = 0; // Must be relearned after reboot; don't invent a transition across power-off.
  if (!storageOK || !LittleFS.exists(DB_PATH)) return true;
  File f = LittleFS.open(DB_PATH, "r");
  if (!f) return false;
  char line[512];
  size_t used = 0;
  bool overflow = false;
  while (f.available()) {
    int c = f.read();
    if (c == '\n') {
      if (!overflow) {
        line[used] = '\0';
        if (used && line[used - 1] == '\r') line[used - 1] = '\0';
        loadDbLine(line);
      }
      used = 0;
      overflow = false;
    } else if (used + 1 < sizeof(line)) {
      line[used++] = (char)c;
    } else {
      overflow = true;
    }
  }
  if (used && !overflow) {
    line[used] = '\0';
    if (used && line[used - 1] == '\r') line[used - 1] = '\0';
    loadDbLine(line);
  }
  f.close();
  Serial.printf("Loaded %u places and %u route edges from flash.\n",
                (unsigned)places.size(), (unsigned)edges.size());
  return true;
}

static bool saveDatabase() {
  if (!storageOK) return false;
  File f = LittleFS.open(TMP_PATH, "w");
  if (!f) {
    Serial.println("Could not open temporary database file.");
    return false;
  }
  f.println("AMBIENTMAP\t2");
  for (const Place &p : places) {
    f.print("P\t"); f.print((unsigned long)p.id);
    f.print('\t'); f.print((unsigned long)p.visits);
    f.print('\t'); f.print(p.label);
    f.print('\t');
    for (uint8_t i = 0; i < p.fp.count; ++i) {
      if (i) f.print(';');
      f.print((unsigned long)p.fp.aps[i].hash);
      f.print(','); f.print((int)p.fp.aps[i].rssi);
    }
    f.println();
  }
  for (const Edge &e : edges) {
    f.print("E\t"); f.print((unsigned long)e.from);
    f.print('\t'); f.print((unsigned long)e.to);
    f.print('\t'); f.print((unsigned long)e.count);
    f.println();
  }
  f.flush();
  bool writeError = f.getWriteError();
  f.close();
  if (writeError) {
    LittleFS.remove(TMP_PATH);
    Serial.println("Flash write failed; previous database was kept.");
    return false;
  }

  LittleFS.remove(BAK_PATH);
  bool hadOld = LittleFS.exists(DB_PATH);
  if (hadOld && !LittleFS.rename(DB_PATH, BAK_PATH)) {
    LittleFS.remove(TMP_PATH);
    Serial.println("Could not rotate database backup; previous database was kept.");
    return false;
  }
  if (!LittleFS.rename(TMP_PATH, DB_PATH)) {
    if (hadOld && LittleFS.exists(BAK_PATH)) LittleFS.rename(BAK_PATH, DB_PATH);
    LittleFS.remove(TMP_PATH);
    Serial.println("Could not install new database; attempted to restore backup.");
    return false;
  }
  LittleFS.remove(BAK_PATH);
  databaseDirty = false;
  lastSaveMs = millis();
  Serial.printf("Saved database: %u places, %u edges, flash used %u/%u bytes.\n",
                (unsigned)places.size(), (unsigned)edges.size(),
                (unsigned)LittleFS.usedBytes(), (unsigned)LittleFS.totalBytes());
  return true;
}

// ----- BLE streaming JSON writer -----

class NotifyWriter {
public:
  void append(const char *s) {
    if (!s) return;
    while (*s) appendChar(*s++);
  }
  void appendChar(char c) {
    buffer[length++] = (uint8_t)c;
    if (length >= BLE_PACKET_BYTES) flush();
  }
  void appendUInt(uint32_t n) {
    char text[16]; snprintf(text, sizeof(text), "%lu", (unsigned long)n); append(text);
  }
  void appendInt(int n) {
    char text[16]; snprintf(text, sizeof(text), "%d", n); append(text);
  }
  void appendFloat(float n) {
    char text[16]; snprintf(text, sizeof(text), "%.2f", n); append(text);
  }
  void appendBool(bool b) { append(b ? "true" : "false"); }
  void appendJsonString(const char *s) {
    append("\"");
    if (s) {
      for (const unsigned char *p = (const unsigned char *)s; *p; ++p) {
        switch (*p) {
          case '\"': append("\\\""); break;
          case '\\': append("\\\\"); break;
          case '\n': append("\\n"); break;
          case '\r': append("\\r"); break;
          case '\t': append("\\t"); break;
          default:
            if (*p >= 32) appendChar((char)*p);
        }
      }
    }
    append("\"");
  }
  void endLine() { appendChar('\n'); flush(); }
  void flush() {
    if (length == 0) return;
    if (bleConnected && txCharacteristic) {
      txCharacteristic->setValue(buffer, length);
      txCharacteristic->notify();
      delay(12); // Gives the BLE stack time between default-MTU notifications.
    }
    length = 0;
  }
private:
  uint8_t buffer[BLE_PACKET_BYTES];
  size_t length = 0;
};

static NotifyWriter out;

static const char *nameForPlace(uint32_t id) {
  Place *p = findPlace(id);
  return p ? p->label : "Unknown";
}

static void sendStatus() {
  out.append("{\"type\":\"status\",\"places\":"); out.appendUInt((uint32_t)places.size());
  out.append(",\"placeCount\":"); out.appendUInt((uint32_t)places.size());
  out.append(",\"edges\":"); out.appendUInt((uint32_t)edges.size());
  out.append(",\"edgeCount\":"); out.appendUInt((uint32_t)edges.size());
  out.append(",\"current\":"); out.appendUInt(currentPlaceId);
  out.append(",\"currentPlace\":"); out.appendUInt(currentPlaceId);
  out.append(",\"currentName\":"); out.appendJsonString(nameForPlace(currentPlaceId));
  out.append(",\"paused\":"); out.appendBool(trackingPaused);
  out.append(",\"storageOk\":"); out.appendBool(storageOK);
  out.append(",\"memoryWarning\":"); out.appendBool(memoryLimitHit);
  out.append(",\"apsSeen\":"); out.appendUInt(lastScanAPCount);
  out.append(",\"lastScanMs\":"); out.appendUInt(lastScanMs);
  out.append(",\"freeHeap\":"); out.appendUInt(ESP.getFreeHeap());
  out.append(",\"flashUsed\":"); out.appendUInt(storageOK ? LittleFS.usedBytes() : 0);
  out.append(",\"flashTotal\":"); out.appendUInt(storageOK ? LittleFS.totalBytes() : 0);
  out.append(",\"scans\":"); out.appendUInt(totalScans);
  out.append("}"); out.endLine();
}

static void sendMap() {
  out.append("{\"type\":\"map\",\"places\":[");
  for (size_t i = 0; i < places.size(); ++i) {
    const Place &p = places[i];
    if (i) out.append(",");
    out.append("{\"id\":"); out.appendUInt(p.id);
    out.append(",\"name\":"); out.appendJsonString(p.label);
    out.append(",\"label\":"); out.appendJsonString(p.label);
    out.append(",\"visits\":"); out.appendUInt(p.visits);
    out.append(",\"lastSeen\":"); out.appendUInt(p.lastSeenMs);
    out.append(",\"apCount\":"); out.appendUInt(p.fp.count);
    out.append(",\"current\":"); out.appendBool(p.id == currentPlaceId);
    out.append("}");
  }
  out.append("],\"duplicates\":[");
  bool firstDuplicate = true;
  for (size_t i = 0; i < places.size(); ++i) {
    for (size_t j = i + 1; j < places.size(); ++j) {
      float score = matchScore(places[i].fp, places[j].fp);
      float rq = 0.0f;
      int common = commonAPs(places[i].fp, places[j].fp, rq);
      // Suggestions only: never merge places without explicit user confirmation.
      if (common >= 3 && score >= 0.62f) {
        if (!firstDuplicate) out.append(",");
        firstDuplicate = false;
        out.append("{\"a\":"); out.appendUInt(places[i].id);
        out.append(",\"b\":"); out.appendUInt(places[j].id);
        out.append(",\"score\":"); out.appendFloat(score);
        out.append(",\"commonAPs\":"); out.appendUInt((uint32_t)common);
        out.append("}");
      }
    }
  }
  out.append("],\"edges\":[");
  for (size_t i = 0; i < edges.size(); ++i) {
    const Edge &e = edges[i];
    if (i) out.append(",");
    out.append("{\"from\":"); out.appendUInt(e.from);
    out.append(",\"to\":"); out.appendUInt(e.to);
    out.append(",\"count\":"); out.appendUInt(e.count);
    out.append(",\"lastSeen\":"); out.appendUInt(e.lastSeenMs);
    out.append("}");
  }
  out.append("],\"current\":"); out.appendUInt(currentPlaceId);
  out.append(",\"currentPlace\":"); out.appendUInt(currentPlaceId);
  out.append(",\"paused\":"); out.appendBool(trackingPaused);
  out.append(",\"storageOk\":"); out.appendBool(storageOK);
  out.append(",\"memoryWarning\":"); out.appendBool(memoryLimitHit);
  out.append("}"); out.endLine();
}

static void sendPrediction() {
  uint32_t bestTo = 0;
  uint32_t bestCount = 0;
  uint64_t totalOut = 0;
  for (const Edge &e : edges) {
    if (e.from == currentPlaceId) {
      totalOut += e.count;
      if (e.count > bestCount) {
        bestCount = e.count;
        bestTo = e.to;
      }
    }
  }
  float relative = totalOut ? (float)bestCount / (float)totalOut : 0.0f;
  out.append("{\"type\":\"prediction\",\"current\":"); out.appendUInt(currentPlaceId);
  out.append(",\"currentName\":"); out.appendJsonString(nameForPlace(currentPlaceId));
  out.append(",\"next\":"); out.appendUInt(bestTo);
  out.append(",\"nextPlace\":"); out.appendUInt(bestTo);
  out.append(",\"nextName\":"); out.appendJsonString(bestTo ? nameForPlace(bestTo) : "Not enough route history");
  out.append(",\"count\":"); out.appendUInt(bestCount);
  out.append(",\"confidence\":"); out.appendFloat(relative);
  out.append(",\"message\":");
  out.appendJsonString(bestTo ? "Prediction based on observed transitions, not a guarantee." : "Visit more places and repeat routes to build prediction history.");
  out.append("}"); out.endLine();
}

static void sendAck(const char *message) {
  out.append("{\"type\":\"ack\",\"message\":");
  out.appendJsonString(message);
  out.append(",\"places\":"); out.appendUInt((uint32_t)places.size());
  out.append(",\"edges\":"); out.appendUInt((uint32_t)edges.size());
  out.append("}"); out.endLine();
}

static bool deletePlace(uint32_t id) {
  int index = findPlaceIndex(id);
  if (index < 0) return false;

  // Remove every route that references the deleted place.
  for (size_t i = edges.size(); i > 0; --i) {
    const Edge &e = edges[i - 1];
    if (e.from == id || e.to == id) edges.erase(edges.begin() + (i - 1));
  }
  places.erase(places.begin() + index);
  if (currentPlaceId == id) currentPlaceId = 0;
  clearPendingCandidates();
  databaseDirty = true;
  forceSaveNow = true;
  if (storageOK && !saveDatabase()) {
    Serial.println("WARNING: place deleted in RAM, but database save failed.");
  }
  return true;
}

static bool mergePlaces(uint32_t sourceId, uint32_t targetId) {
  if (!sourceId || !targetId || sourceId == targetId) return false;
  int sourceIndex = findPlaceIndex(sourceId);
  int targetIndex = findPlaceIndex(targetId);
  if (sourceIndex < 0 || targetIndex < 0) return false;

  Place &source = places[(size_t)sourceIndex];
  Place &target = places[(size_t)targetIndex];
  uint64_t visits = (uint64_t)target.visits + source.visits;
  target.visits = visits > UINT32_MAX ? UINT32_MAX : (uint32_t)visits;
  // Keep the target's fingerprint as the canonical one; the source was only
  // merged after the user confirmed the duplicate suggestion.
  if (currentPlaceId == sourceId) currentPlaceId = targetId;

  for (Edge &e : edges) {
    if (e.from == sourceId) e.from = targetId;
    if (e.to == sourceId) e.to = targetId;
  }
  // Remove self-loops created by redirecting edges, and combine duplicate routes.
  for (size_t i = edges.size(); i > 0; --i) {
    if (edges[i - 1].from == edges[i - 1].to) edges.erase(edges.begin() + (i - 1));
  }
  for (size_t i = 0; i < edges.size(); ++i) {
    for (size_t j = i + 1; j < edges.size();) {
      if (edges[i].from == edges[j].from && edges[i].to == edges[j].to) {
        uint64_t count = (uint64_t)edges[i].count + edges[j].count;
        edges[i].count = count > UINT32_MAX ? UINT32_MAX : (uint32_t)count;
        if ((int32_t)(edges[j].lastSeenMs - edges[i].lastSeenMs) > 0) edges[i].lastSeenMs = edges[j].lastSeenMs;
        edges.erase(edges.begin() + (j));
      } else ++j;
    }
  }
  places.erase(places.begin() + sourceIndex);
  clearPendingCandidates();
  databaseDirty = true;
  forceSaveNow = true;
  if (storageOK && !saveDatabase()) Serial.println("WARNING: merge applied in RAM, but database save failed.");
  return true;
}

static bool deleteEdge(uint32_t from, uint32_t to) {
  for (size_t i = 0; i < edges.size(); ++i) {
    if (edges[i].from == from && edges[i].to == to) {
      edges.erase(edges.begin() + i);
      databaseDirty = true;
      forceSaveNow = true;
      if (storageOK && !saveDatabase()) Serial.println("WARNING: route deleted in RAM, but database save failed.");
      return true;
    }
  }
  return false;
}

static void resetDatabase() {
  places.clear();
  edges.clear();
  nextPlaceId = 1;
  currentPlaceId = 0;
  clearPendingCandidates();
  memoryLimitHit = false;
  forceSaveNow = false;
  databaseDirty = true;
  if (storageOK) {
    LittleFS.remove(DB_PATH);
    LittleFS.remove(TMP_PATH);
    LittleFS.remove(BAK_PATH);
    saveDatabase();
  }
}

static void handleCommand(char *raw) {
  String cmd(raw ? raw : "");
  cmd.trim();
  if (!cmd.length()) return;
  String upper = cmd;
  upper.toUpperCase();
  Serial.printf("BLE command: %s\n", cmd.c_str());

  if (upper == "STATUS") {
    sendStatus();
  } else if (upper == "MAP") {
    sendMap();
  } else if (upper == "PREDICT") {
    sendPrediction();
  } else if (upper == "PAUSE") {
    trackingPaused = true;
    sendStatus();
  } else if (upper == "RESUME") {
    trackingPaused = false;
    sendStatus();
  } else if (upper == "RESET") {
    resetDatabase();
    sendAck("Database reset. A new map will be learned from the next scans.");
    sendStatus();
  } else if (upper.startsWith("DELETE ")) {
    String idText = cmd.substring(7);
    idText.trim();
    if (!idText.length()) {
      sendAck("Usage: DELETE <id>");
      return;
    }
    char *end = nullptr;
    unsigned long parsed = strtoul(idText.c_str(), &end, 10);
    if (!end || *end != '\0' || parsed == 0 || parsed > UINT32_MAX) {
      sendAck("Delete failed: invalid place ID.");
      return;
    }
    if (!deletePlace((uint32_t)parsed)) {
      sendAck("Delete failed: place ID not found.");
      return;
    }
    sendAck("Place and its route connections deleted.");
    sendMap();
    sendStatus();
  } else if (upper.startsWith("MERGE ")) {
    String args = cmd.substring(6); args.trim();
    int split = args.indexOf(' ');
    if (split < 0) { sendAck("Usage: MERGE <sourceId> <targetId>"); return; }
    String sourceText = args.substring(0, split); String targetText = args.substring(split + 1); targetText.trim();
    char *end1 = nullptr; char *end2 = nullptr;
    unsigned long sourceId = strtoul(sourceText.c_str(), &end1, 10);
    unsigned long targetId = strtoul(targetText.c_str(), &end2, 10);
    if (!end1 || *end1 || !end2 || *end2 || !sourceId || !targetId || sourceId > UINT32_MAX || targetId > UINT32_MAX) {
      sendAck("Merge failed: invalid place IDs."); return;
    }
    if (!mergePlaces((uint32_t)sourceId, (uint32_t)targetId)) { sendAck("Merge failed: IDs must exist and be different."); return; }
    sendAck("Places merged; routes and visit counts combined."); sendMap(); sendStatus();
  } else if (upper.startsWith("DELETEEDGE ")) {
    String args = cmd.substring(11); args.trim(); int split = args.indexOf(' ');
    if (split < 0) { sendAck("Usage: DELETEEDGE <fromId> <toId>"); return; }
    String fromText = args.substring(0, split); String toText = args.substring(split + 1); toText.trim();
    char *end1 = nullptr; char *end2 = nullptr;
    unsigned long fromId = strtoul(fromText.c_str(), &end1, 10); unsigned long toId = strtoul(toText.c_str(), &end2, 10);
    if (!end1 || *end1 || !end2 || *end2 || !fromId || !toId || fromId > UINT32_MAX || toId > UINT32_MAX) { sendAck("Route deletion failed: invalid IDs."); return; }
    if (!deleteEdge((uint32_t)fromId, (uint32_t)toId)) { sendAck("Route deletion failed: route not found."); return; }
    sendAck("Directed route deleted."); sendMap();
  } else if (upper.startsWith("LABEL ")) {
    int firstSpace = cmd.indexOf(' ');
    int secondSpace = cmd.indexOf(' ', firstSpace + 1);
    if (secondSpace < 0) {
      sendAck("Usage: LABEL <id> <name>");
      return;
    }
    uint32_t id = (uint32_t)strtoul(cmd.substring(firstSpace + 1, secondSpace).c_str(), nullptr, 10);
    String labelString = cmd.substring(secondSpace + 1);
    labelString.trim();
    char cleanLabel[32];
    copySanitized(cleanLabel, sizeof(cleanLabel), labelString.c_str());
    Place *p = findPlace(id);
    if (!p || !cleanLabel[0]) {
      sendAck("Label not changed: place ID not found or name empty.");
      return;
    }
    copySanitized(p->label, sizeof(p->label), cleanLabel);
    databaseDirty = true;
    saveDatabase();
    sendAck("Place label updated.");
    sendMap();
  } else {
    sendAck("Unknown command. Use STATUS, MAP, PREDICT, PAUSE, RESUME, LABEL <id> <name>, DELETE <id>, MERGE <sourceId> <targetId>, DELETEEDGE <fromId> <toId>, or RESET.");
  }
}

class ServerCallbacks : public BLEServerCallbacks {
  void onConnect(BLEServer *server) override {
    bleConnected = true;
    Serial.println("BLE client connected.");
  }
  void onDisconnect(BLEServer *server) override {
    bleConnected = false;
    Serial.println("BLE client disconnected; advertising again.");
    delay(80);
    BLEDevice::startAdvertising();
  }
};

class RXCallbacks : public BLECharacteristicCallbacks {
  void onWrite(BLECharacteristic *characteristic) override {
    // Arduino-ESP32 core 3.x returns an Arduino String from getValue().
    String value = characteristic->getValue();
    if (!value.length()) return;
    portENTER_CRITICAL(&commandMux);
    size_t n = value.length();
    if (n >= sizeof(pendingCommand)) n = sizeof(pendingCommand) - 1;
    memcpy(pendingCommand, value.c_str(), n);
    pendingCommand[n] = '\0';
    commandPending = true;
    portEXIT_CRITICAL(&commandMux);
  }
};

static void setupBLE() {
  BLEDevice::init(BLE_NAME);
  bleServer = BLEDevice::createServer();
  bleServer->setCallbacks(new ServerCallbacks());
  BLEService *service = bleServer->createService(SERVICE_UUID);
  txCharacteristic = service->createCharacteristic(TX_UUID, BLECharacteristic::PROPERTY_NOTIFY);
  txCharacteristic->addDescriptor(new BLE2902());
  BLECharacteristic *rx = service->createCharacteristic(
    RX_UUID, BLECharacteristic::PROPERTY_WRITE | BLECharacteristic::PROPERTY_WRITE_NR);
  rx->setCallbacks(new RXCallbacks());
  service->start();
  BLEAdvertising *advertising = BLEDevice::getAdvertising();
  advertising->addServiceUUID(SERVICE_UUID);
  advertising->setScanResponse(true);
  advertising->setMinPreferred(0x06);
  advertising->setMinPreferred(0x12);
  BLEDevice::startAdvertising();
}

static bool mountDatabaseFilesystem() {
  // Use a tiny NVS marker only to distinguish a first-time blank filesystem from
  // a filesystem that had already been initialized. Never auto-format a known
  // initialized filesystem just because a later mount fails.
  Preferences meta;
  bool markerReadable = meta.begin("ambient_meta", false);
  bool wasInitialized = markerReadable ? meta.getBool("fs_ready", false) : true;
  if (markerReadable) meta.end();

  storageOK = LittleFS.begin(false);
  if (!storageOK && markerReadable && !wasInitialized) {
    Serial.println("First run: initializing the LittleFS data partition...");
    storageOK = LittleFS.begin(true);
  }

  if (storageOK && markerReadable && !wasInitialized) {
    if (meta.begin("ambient_meta", false)) {
      meta.putBool("fs_ready", true);
      meta.end();
    }
  }
  if (!storageOK) {
    Serial.println("LittleFS mount failed. Refusing to auto-format an initialized filesystem.");
  }
  return storageOK;
}

void setup() {
  Serial.begin(115200);
  delay(250);
  Serial.println();
  Serial.println("AmbientMapper v2 booting...");

  // The map is stored in the board's LittleFS flash partition.
  storageOK = mountDatabaseFilesystem();
  if (!storageOK) {
    Serial.println("WARNING: LittleFS unavailable; map will only be kept in RAM this session.");
  } else {
    Serial.printf("LittleFS mounted (%u bytes total).\n", (unsigned)LittleFS.totalBytes());
    if (!loadDatabase()) Serial.println("WARNING: database read failed; starting with an empty in-memory map.");
  }

  WiFi.mode(WIFI_STA);
  WiFi.disconnect(false, true);
  WiFi.setSleep(false);
  delay(100);

  setupBLE();
  lastScanMs = millis() - SCAN_INTERVAL_MS; // Scan soon after boot.
  lastSaveMs = millis();
  Serial.printf("Ready. Loaded %u places and %u directed route edges.\n",
                (unsigned)places.size(), (unsigned)edges.size());
  Serial.println("Commands: STATUS, MAP, PREDICT, PAUSE, RESUME, LABEL <id> <name>, DELETE <id>, MERGE <sourceId> <targetId>, DELETEEDGE <fromId> <toId>, RESET");
}

void loop() {
  char localCommand[sizeof(pendingCommand)] = {0};
  bool haveCommand = false;
  portENTER_CRITICAL(&commandMux);
  if (commandPending) {
    memcpy(localCommand, pendingCommand, sizeof(localCommand));
    pendingCommand[0] = '\0';
    commandPending = false;
    haveCommand = true;
  }
  portEXIT_CRITICAL(&commandMux);
  if (haveCommand) handleCommand(localCommand);

  uint32_t now = millis();
  if (!trackingPaused && (uint32_t)(now - lastScanMs) >= SCAN_INTERVAL_MS) {
    lastScanMs = now;
    ++totalScans;
    Fingerprint observed = scanFingerprint();
    lastScanAPCount = observed.count;
    processFingerprint(observed);
    if (forceSaveNow && storageOK) {
      saveDatabase();
      forceSaveNow = false;
    }
    if (databaseDirty && storageOK && (uint32_t)(now - lastSaveMs) >= SAVE_INTERVAL_MS) {
      saveDatabase();
    }
  }

  // Persist soon after any change, but no more frequently than the save interval.
  if (databaseDirty && storageOK && (uint32_t)(millis() - lastSaveMs) >= SAVE_INTERVAL_MS) {
    saveDatabase();
  }
  delay(8);
}
