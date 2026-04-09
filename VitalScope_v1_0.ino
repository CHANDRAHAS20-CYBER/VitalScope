#include <Wire.h>
#include <WiFi.h>
#include <WebServer.h>
#include <DNSServer.h>
#include <SPI.h>
#include <ArduinoJson.h>
#include <Preferences.h>
#include <time.h>
#include <MAX30105.h>
#include "heartRate.h"
#include <Adafruit_MLX90614.h>
#include <Adafruit_LSM6DSOX.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <SPIMemory.h>
#include <math.h>
#include "esp_wifi.h"

#define SDA_PIN        4
#define SCL_PIN        5
#define FLASH_CS       10
#define FLASH_SCK      2
#define FLASH_MOSI     3
#define FLASH_MISO     1
#define STATUS_LED     7
#define SCREEN_WIDTH   128
#define SCREEN_HEIGHT  32
#define OLED_RESET     -1
#define OLED_ADDR      0x3C

const char* AP_SSID       = "VitalScope-Health";
const char* AP_PASS       = "health123";
const char* NTP_SERVER    = "pool.ntp.org";
const long  GMT_OFFSET    = 19800;
const int   DST_OFFSET    = 0;
const char* ADMIN_USER    = "admin";
const char* ADMIN_PASS    = "admin@123";
const char* SUPPORT_EMAIL = "bandaruchandrahas1708@gmail.com";
const char* SUPPORT_PHONE = "9949177088";
#define VALID_MARKER   0xA5
#define RECORD_MARKER  0xB6

// ─── NTP WiFi credentials ─────────────────────────────────────────────────────
const char* NTP_WIFI_SSID = "Chandu";        // Your WiFi SSID
const char* NTP_WIFI_PASS = "9949177088";    // Your WiFi password
bool        ntpSynced     = false;
unsigned long lastNtpRetry = 0;
long manualTimeOffset = 0;  // seconds added to millis-based clock
bool manualTimeSet    = false;

DNSServer  dnsServer;
const byte DNS_PORT = 53;

MAX30105          particleSensor;
Adafruit_MLX90614 mlx;
Adafruit_LSM6DSOX lsm;
Adafruit_SSD1306  display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, OLED_RESET);
SPIFlash          flash(FLASH_CS);

// that caused webserver OOM after extended use. Only one flash op runs at a time (single-threaded).
static uint8_t    sectorScratch[4096];
WebServer         server(80);
Preferences       preferences;

bool          otpDisplayLock      = false;
unsigned long otpDisplayLockUntil = 0;
#define OTP_DISPLAY_HOLD_MS 15000

#define MEASURE_WINDOW_MS      90000UL
#define MEAS_CLIENT_TIMEOUT_MS 60000UL   
bool          measuringActive     = false;
unsigned long measureStart        = 0;
unsigned long measureRemaining    = 0;
unsigned long lastClientPoll      = 0;   // watchdog: last time a client polled measure-status
bool          measurementDone     = false;
char          measuringUser[32]   = "";
bool          autoSaved           = false;
bool          sensorWarmupDone    = false;  // true after 30s continuous finger contact
float         hrSmoothed          = 0.0f;   // EMA-smoothed HR for stable display

// Accumulators for 90s average (owned by current measuring session)
float    acc_hr    = 0; int acc_hr_cnt   = 0;
float    acc_spo2  = 0; int acc_spo2_cnt = 0;
float    acc_temp  = 0; int acc_temp_cnt = 0;
float    acc_rr    = 0; int acc_rr_cnt   = 0;
float    acc_pi    = 0; int acc_pi_cnt   = 0;

// Per-session averaged snapshot (stored inside Session struct too)
struct AveragedVitals {
  float heartRate;
  float spO2;
  float temperature;
  float respiratoryRate;
  float perfusionIndex;
  int   healthScore;
  bool  valid;
};

// Global snapshot updated when measuring session finishes
AveragedVitals avgVitals;

#define RATE_SIZE 16    // [ACC] was 8 — 16 samples, true median more stable than trimmed mean
byte  rates[RATE_SIZE];
byte  rateSpot   = 0;
long  lastBeat   = 0;
int   beatAvg    = 0;
float hrRunning  = 0;
int   beatCount  = 0;
float hrConfidence = 0;

// SpO2: proper AC/DC separation, 8-sample rolling average
#define SPO2_SAMPLE_SIZE 12  // [ACC] was 8 — 12 weighted windows for smoother SpO2
float spo2Samples[SPO2_SAMPLE_SIZE];
int   spo2Index      = 0;
int   spo2Count      = 0;
bool  spo2Ready      = false;
float lastSpO2       = 0;      // live computed value
float frozenSpO2     = 0;      // last valid reading — stays on card after finger removed
bool  spo2Frozen     = false;  // showing frozen value
float spo2Confidence = 0;

float dcIR_f  = 0;
float dcRed_f = 0;

// Perfusion
#define PI_SAMPLES 16   // [ACC] was 8 — wider window for stable perfusion index
float acEnvelope[PI_SAMPLES];
int   piIdx   = 0;
float signalQuality = 0;

#define MLX_TEMP_OFFSET   1.5f   
#define TEMP_SAMPLES    12   // [ACC] was 8 — larger median pool rejects outlier spikes
#define TEMP_SKIN_MIN  34.0f    
#define TEMP_VALID_MAX 40.5f    
float tempSamples[TEMP_SAMPLES];
int   tempIndex = 0;
float currentTemperature = 0;
bool  tempValid = false;

// Respiratory
int   respiratoryRate = 0;
// respiratoryRate updated by estimateRespiratoryRate() every 20s

#define FINGER_IR_THRESHOLD 7000L    

// Detects and auto-recovers from MAX30102 / MLX90614 lockup after extended use.
static unsigned long lastFingerLostTime  = 0;  // when finger last seen (or 0 = never seen)
static bool          fingerEverDetected  = false;
static unsigned long lastGoodIrTime      = 0;  // last time IR > threshold
#define MAX30102_RECOVERY_MS  60000UL   
#define MLX_RECOVERY_MS      120000UL   
static unsigned long lastGoodTempTime    = 0;  // last time MLX responded (updated on any read, not just skin temp)

struct VitalSigns {
  int   heartRate;
  float hrConfidence;
  float spO2;
  float spo2Confidence;
  float temperature;
  int   respiratoryRate;
  float perfusionIndex;
  int   stressLevel;
  int   healthScore;
  unsigned long timestamp;
  bool  fingerDetected;
  int   signalQuality;
};

struct UserProfile {
  uint8_t  marker;
  char     username[32];
  char     password[64];
  char     name[64];
  char     email[64];
  char     phone[16];
  int      age;
  char     gender[10];
  float    height;
  float    weight;
  char     diseases[200];
  uint32_t dataStartAddr;
  int      dataCount;
  bool     verified;
  unsigned long lastLogin;
  int      loginCount;
};

#define MAX_SESSIONS    20
#define MAX_OTP_RECORDS 20

struct Session {
  char           token[64];
  char           username[32];
  unsigned long  lastActivity;
  bool           active;
  bool           isAdmin;
  int            requestCount;
  AveragedVitals sessionAvg;
  bool           sessionMeasDone;
  bool           sessionAutoSaved;
};

struct OTPRecord {
  char  identifier[64];
  char  otp[7];
  unsigned long timestamp;
  bool  active;
  int   attempts;
};

struct SystemStats {
  unsigned long totalMeasurements;
  unsigned long totalUsers;
  unsigned long activeUsers;
  unsigned long systemUptime;
  float         avgHealthScore;
  int           errorCount;
};

Session     sessions[MAX_SESSIONS];
OTPRecord   otpRecords[MAX_OTP_RECORDS];
SystemStats systemStats;
VitalSigns  currentVitals;
bool        sensorsInitialized    = false;
bool        max30102Ok            = false;   
bool        mlxOk2                = false;   
bool        lsmOk                 = false;   // set true if LSM6DSOX found at boot
bool        measurementInProgress = false;

#define USER_RECORD_SIZE     sizeof(UserProfile)
#define MAX_USERS            50
#define USER_DB_START        0x000000UL
#define USER_DB_SIZE         ((uint32_t)MAX_USERS * USER_RECORD_SIZE)
#define USER_DB_SECTORS      ((USER_DB_SIZE + 4095UL) / 4096UL)
#define USER_DATA_START      (USER_DB_SECTORS * 4096UL)
#define VITAL_RECORD_SIZE    40
#define MAX_RECORDS_PER_USER 500
#define USER_DATA_BLOCK      ((uint32_t)MAX_RECORDS_PER_USER * VITAL_RECORD_SIZE)
#define FLASH_PAGE_SIZE      256UL

void initTime(); String getFormattedDateTime(); void retryNtpIfNeeded();
void initSessions(); void initOTPRecords(); void initSystemStats();
String createSession(const char*, bool); bool validateSession(String, UserProfile*);
void destroySession(String); bool isAdminSession(String);
int  getSessionIndex(String);
String generateOTP(); bool storeOTP(const char*, const char*);
bool validateOTP(const char*, const char*); void cleanExpiredOTP();
void initializeSensors(); void initializeFlash(); void initializeWiFi();
void initializeWebServer(); void readVitalSigns();
float medianFilter(float*, int);
int estimateRespiratoryRate();
int calcStress(); int calcHealthScore(); int calcHealthScoreFromAvg();
int calcHealthScoreFromSessionAvg(AveragedVitals &av);
void updateDisplay(); void showOTPOnDisplay(const char*, const char*);
bool saveVitalRecord(UserProfile*, AveragedVitals *av);
void loadVitalRecord(UserProfile*, int, VitalSigns*);
void updateUserRecord(UserProfile*); bool findUser(const char*, UserProfile*);
bool findUserByEmail(const char*, UserProfile*); bool createUser(UserProfile*);
int getUserCount(); bool deleteUser(const char*); void updateSystemStats(); void handleError(const char*);
void handleRoot(); void handleSignIn(); void handleSignUp();
void handleSendOTP(); void handleVerifyOTP(); void handleForgotPassword();
void handleResetPassword(); void handleLogout(); void handleGetVitals();
void handleGetProfile(); void handleUpdateProfile(); void handleChangePassword();
void handleGetHistory(); void handleGenerateReport(); void handleMeasure();
void handleMeasureStatus(); void handleSaveRecord(); void handleGetRealtimeData(); void handleNotFound();
void handleAdminDashboard(); void handleAdminGetUsers(); void handleAdminGetUserData();
void handleAdminDeleteUser(); void handleSystemStats(); void handleSetTime();
void handleHRPage(); void handleSpO2Page(); void handleTempPage(); void handleRespPage();
void handleReportPrint(); void handleRecordPrint(); void handleRecordDownload();
void handleFullReportDownload();

inline void sendJSON(int code, const String& body) {
  server.sendHeader("Connection", "close", true);
  server.send(code, "application/json", body);
}

void setup() {
  setCpuFrequencyMhz(80);     
  Serial.begin(115200);
  delay(1000);
  Serial.println(F("\n=== VitalScope v1.0 ==="));

  pinMode(STATUS_LED, OUTPUT);
  for (int i = 0; i < 3; i++) {
    digitalWrite(STATUS_LED, HIGH); delay(150);
    digitalWrite(STATUS_LED, LOW);  delay(150);
  }

  Wire.begin(SDA_PIN, SCL_PIN);
  Wire.setTimeOut(20);     
  Wire.setClock(400000);   // 400kHz fast-mode — SSD1306, MAX30102, LSM6DSOX all support 400kHz.
                           // MLX90614 datasheet says 100kHz but works reliably at 400kHz in practice.
                           // Reduces OLED framebuffer flush from ~80ms to ~20ms — critical for web server.
  SPI.begin(FLASH_SCK, FLASH_MISO, FLASH_MOSI, FLASH_CS);
  preferences.begin("vitalscope", false);

  initSessions();
  initOTPRecords();
  initSystemStats();
  initializeSensors();
  initializeFlash();
  initializeWiFi();
  initTime();
  initializeWebServer();

  WiFi.setTxPower(WIFI_POWER_17dBm);  
  esp_wifi_set_inactive_time(WIFI_IF_AP, 10);  // kick zombie STAs after 10s idle

  memset(&avgVitals, 0, sizeof(avgVitals));

  display.clearDisplay();
  display.setTextSize(1);
  display.setTextColor(WHITE);
  display.setCursor(0, 0);
  display.println(F("VitalScope v1.0"));
  display.print(F("IP: "));
  display.println(WiFi.softAPIP());
  display.println(F("Ready - 90s Avg Mode"));
  display.display();

  Serial.print(F("Portal: http://"));
  Serial.println(WiFi.softAPIP());
  digitalWrite(STATUS_LED, HIGH);
}

void loop() {
  dnsServer.processNextRequest();
  server.handleClient();

  // ── Rate-limit sensor reading to every 150ms ──
  // safeCheck(8) blocks up to 8ms waiting for a fresh sample at 100Hz
  static unsigned long lastSensorRead = 0;
  if (millis() - lastSensorRead >= 20) {    // 20ms = 50Hz output rate (avg4); safeCheck(20ms) waits for fresh sample
    lastSensorRead = millis();
    readVitalSigns();
  }

  if (measuringActive) {
    unsigned long elapsed = millis() - measureStart;

    if (millis() - lastClientPoll > MEAS_CLIENT_TIMEOUT_MS) {
      Serial.println(F("Measurement cancelled — client disconnected (watchdog)"));
      measuringActive = false; measurementInProgress = false;
      memset(measuringUser, 0, sizeof(measuringUser));
      acc_hr=0;acc_hr_cnt=0;acc_spo2=0;acc_spo2_cnt=0;
      acc_temp=0;acc_temp_cnt=0;acc_rr=0;acc_rr_cnt=0;acc_pi=0;acc_pi_cnt=0;
    } else if (elapsed >= MEASURE_WINDOW_MS) {
      measuringActive       = false;
      measurementInProgress = false;
      measurementDone       = true;

      avgVitals.valid = false;
      if (acc_hr_cnt   > 0) { avgVitals.heartRate       = acc_hr   / acc_hr_cnt;   avgVitals.valid = true; }
      if (acc_spo2_cnt > 0) { avgVitals.spO2            = acc_spo2 / acc_spo2_cnt; avgVitals.valid = true; }
      if (acc_temp_cnt > 0) { avgVitals.temperature     = acc_temp / acc_temp_cnt; avgVitals.valid = true; }
      if (acc_rr_cnt   > 0) { avgVitals.respiratoryRate = acc_rr   / acc_rr_cnt;   avgVitals.valid = true; }
      else if (respiratoryRate > 0) { avgVitals.respiratoryRate = respiratoryRate; }
      if (acc_pi_cnt   > 0) { avgVitals.perfusionIndex  = acc_pi   / acc_pi_cnt;   avgVitals.valid = true; }
      avgVitals.healthScore = calcHealthScoreFromAvg();

      Serial.printf("90s avg: HR=%.0f SpO2=%.1f Temp=%.1f RR=%.0f PI=%.2f Score=%d\n",
        avgVitals.heartRate, avgVitals.spO2, avgVitals.temperature,
        avgVitals.respiratoryRate, avgVitals.perfusionIndex, avgVitals.healthScore);

      for (int i = 0; i < MAX_SESSIONS; i++) {
        if (sessions[i].active && strcmp(sessions[i].username, measuringUser) == 0 && !sessions[i].isAdmin) {
          sessions[i].sessionAvg      = avgVitals;
          sessions[i].sessionMeasDone = true;
          break;
        }
      }

      autoSaved = false;
      if (avgVitals.valid && strlen(measuringUser) > 0) {
        UserProfile autoUser;
        if (findUser(measuringUser, &autoUser)) {
          autoSaved = saveVitalRecord(&autoUser, &avgVitals);
          Serial.printf("Auto-save for %s: %s\n", measuringUser, autoSaved ? "OK" : "FAIL");
          for (int i = 0; i < MAX_SESSIONS; i++) {
            if (sessions[i].active && strcmp(sessions[i].username, measuringUser) == 0)
              sessions[i].sessionAutoSaved = true;
          }
        }
      }
      memset(measuringUser, 0, sizeof(measuringUser));

    } else {p
      measureRemaining = (MEASURE_WINDOW_MS - elapsed) / 1000;
      
      // beatAvg stays at last good value even if finger lifts briefly.
      int hrToAcc = (currentVitals.fingerDetected && currentVitals.heartRate >= 30 && currentVitals.heartRate <= 220)
                    ? currentVitals.heartRate : ((int)hrSmoothed >= 30 && (int)hrSmoothed <= 150 ? (int)hrSmoothed : 0);
      if (hrToAcc > 0) { acc_hr += hrToAcc; acc_hr_cnt++; }
      if (currentVitals.spO2 > 80.0f && currentVitals.spO2 <= 100.0f) {
        acc_spo2 += currentVitals.spO2; acc_spo2_cnt++;
      }
      if (tempValid && currentTemperature >= TEMP_SKIN_MIN && currentTemperature <= TEMP_VALID_MAX) {
        acc_temp += currentTemperature; acc_temp_cnt++;
      }
      if (respiratoryRate >= 6 && respiratoryRate <= 40) {
        acc_rr += respiratoryRate; acc_rr_cnt++;
      }
      if (currentVitals.perfusionIndex > 0) {
        acc_pi += currentVitals.perfusionIndex; acc_pi_cnt++;
      }
    }
  }

  // ── Sensor watchdog — only fires if sensors truly lock up ──
  static unsigned long lastWatchdog = 0;
  if (millis() - lastWatchdog >= 15000) {   // check every 15s
    lastWatchdog = millis();

    
    if (!measuringActive) {

      // MAX30102 watchdog: only reinit if finger was seen before AND IR has been 0 for >60s
      
      if (fingerEverDetected && lastGoodIrTime > 0 &&
          millis() - lastGoodIrTime > 60000UL &&
          !currentVitals.fingerDetected) {
        Serial.println(F("[WD] MAX30102 stale — reinitialising"));
        
        // Just reinit the MAX30102 driver itself.
        particleSensor.shutDown();
        delay(20);
        particleSensor.wakeUp();
        delay(20);
        if (particleSensor.begin(Wire, I2C_SPEED_FAST)) {
          particleSensor.setup(0x1F, 4, 2, 50, 411, 4096);
          particleSensor.setPulseAmplitudeRed(0x1F);
          particleSensor.setPulseAmplitudeIR(0x1F);
          for (int i = 0; i < 32; i++) { particleSensor.safeCheck(5); particleSensor.getIR(); particleSensor.getRed(); }
          max30102Ok = true;
          Serial.println(F("[WD] MAX30102 reinit OK"));
        } else {
          max30102Ok = false;
          Serial.println(F("[WD] MAX30102 reinit FAILED"));
        }
        lastGoodIrTime     = millis();
        fingerEverDetected = false;
      }

      // MLX watchdog: only reinit if truly no response for >120s
      
      // Now lastGoodTempTime updates on ANY MLX read, so this only fires on actual I2C failure.
      if (lastGoodTempTime > 0 && millis() - lastGoodTempTime > 120000UL) {
        Serial.println(F("[WD] MLX90614 stale — reinitialising"));
        
        if (mlx.begin(0x5A, &Wire)) {
          mlxOk2 = true;
          Serial.println(F("[WD] MLX90614 reinit OK"));
        } else {
          mlxOk2 = false;
          Serial.println(F("[WD] MLX90614 reinit FAILED"));
        }
        tempValid = false;
        currentTemperature = 0;
        memset(tempSamples, 0, sizeof(tempSamples));
        tempIndex = 0;
        lastGoodTempTime = millis();
      }

    } // end !measuringActive
  }

  static unsigned long lastDisplay = 0;
  if (millis() - lastDisplay > 3000) {  
    lastDisplay = millis();
    if (!otpDisplayLock || millis() > otpDisplayLockUntil) {
      otpDisplayLock = false;
      updateDisplay();
    }
  }

  static unsigned long lastStats = 0;
  if (millis() - lastStats > 30000) {  
    lastStats = millis();
    updateSystemStats();
  }

  static unsigned long lastOTPClean = 0;
  if (millis() - lastOTPClean > 60000) {
    lastOTPClean = millis();
    cleanExpiredOTP();
  }

  retryNtpIfNeeded();
}

void initializeSensors() {
  Serial.println(F("Initializing sensors..."));
  sensorsInitialized = true;

  
  Wire.setClock(100000);
  delay(10);
  if (!particleSensor.begin(Wire, I2C_SPEED_STANDARD)) {
    // Retry at fast speed
    Wire.setClock(400000);
    delay(10);
    if (!particleSensor.begin(Wire, I2C_SPEED_FAST)) {
      Serial.println(F("MAX30102 NOT found! Check VCC=3.3V, SDA=4, SCL=5, INT pin"));
      max30102Ok = false;
      
    } else {
      max30102Ok = true;
    }
  } else {
    max30102Ok = true;
    Wire.setClock(400000); // restore fast mode for OLED speed
  }

  if (max30102Ok) {
    Serial.println(F("MAX30102 OK"));
    
    particleSensor.shutDown();
    delay(20);
    particleSensor.wakeUp();
    delay(20);
    // setup(ledBrightness, sampleAverage, ledMode, sampleRate, pulseWidth, adcRange)
    // sampleRate=100Hz: at 250ms poll interval we get ~25 fresh samples → many beat chances
    // pulseWidth=411us (longest) → maximum signal strength → easier beat detection
    // adcRange=4096 → sufficient for finger; ledBrightness=0xFF (max) for strong signal
    // LED=0x1F (6mA) — correct brightness, no saturation.
    // sampleAverage=4: hardware averages 4 ADC readings per FIFO entry.
    //   - Reduces noise by 2x → correct SpO2 RMS ratio
    //   - sampleRate=50Hz output (200Hz ADC / avg4) → safeCheck(20ms) gets fresh sample
    //   - pulseWidth=411us → maximum SNR for both HR and SpO2
    particleSensor.setup(0x1F, 4, 2, 50, 411, 4096);
    particleSensor.setPulseAmplitudeRed(0x1F);
    particleSensor.setPulseAmplitudeIR(0x1F);
    for (int i = 0; i < 32; i++) {
      particleSensor.safeCheck(5);
      particleSensor.getIR();
      particleSensor.getRed();
    }
    Serial.println(F("MAX30102 configured: 50Hz out(avg4), PW=411us, LED=0x1F"));
  }

  if (!mlx.begin(0x5A, &Wire)) {
    Serial.println(F("MLX90614 NOT found! Check wiring SDA=4 SCL=5"));
    mlxOk2 = false;
    
  } else {
    Serial.println(F("MLX90614 OK"));
    mlxOk2 = true;
  }

  lsmOk = lsm.begin_I2C(0x6A, &Wire);
  if (!lsmOk) lsmOk = lsm.begin_I2C(0x6B, &Wire);
  if (!lsmOk) {
    Serial.println(F("LSM6DSOX NOT found — RR will show '--'"));
  } else {
    Serial.println(F("LSM6DSOX OK"));
    lsm.setAccelRange(LSM6DS_ACCEL_RANGE_2_G);
    lsm.setAccelDataRate(LSM6DS_RATE_104_HZ);
  }

  Wire.setClock(400000);   // ensure 400kHz before OLED init
  delay(10);
  if (!display.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR)) {
    Serial.println(F("OLED NOT found!"));
  } else {
    Serial.println(F("OLED OK"));
    display.clearDisplay();   // flush random SRAM noise immediately after power-on
    display.display();        // push blank frame — clears the static
    delay(50);
    display.setRotation(2);   // 180° rotation
    display.setTextSize(1);
    display.setTextColor(WHITE);
    display.setCursor(0, 8);
    display.println(F("VitalScope v1.0"));
    display.setCursor(0, 20);
    display.println(F("Initializing..."));
    display.display();
  }

  // sensorsInitialized = at least MAX30102 or MLX must be OK
  sensorsInitialized = max30102Ok || mlxOk2;

  memset(rates, 0xFF, sizeof(rates));
  memset(tempSamples, 0, sizeof(tempSamples));
  memset(spo2Samples, 0, sizeof(spo2Samples));
  memset(acEnvelope, 0, sizeof(acEnvelope));
  lastGoodTempTime = millis();  
  lastGoodIrTime   = millis();  
}

float medianFilter(float* arr, int n) {
  float tmp[TEMP_SAMPLES];
  memcpy(tmp, arr, n * sizeof(float));
  for (int i = 1; i < n; i++) {
    float key = tmp[i]; int j = i - 1;
    while (j >= 0 && tmp[j] > key) { tmp[j+1] = tmp[j]; j--; }
    tmp[j+1] = key;
  }
  return tmp[n / 2];
}

// Called at end of readVitalSigns regardless of MAX30102 presence (no goto needed).
static void readTempAndFinalize() {
  static unsigned long lastTempRead = 0;
  if (millis() - lastTempRead >= 200) {   // 200ms — MLX needs ~180ms between reads
    lastTempRead = millis();
    if (mlxOk2) {
      float rawTemp = mlx.readObjectTempC() + MLX_TEMP_OFFSET;
      
      // even if temp is below skin threshold (ambient ~25°C when no wrist placed).
      // Previously only updated on valid skin reading → watchdog fired every 30s
      // when no wrist present → Wire.end()/begin() broke MAX30102 → HR died.
      lastGoodTempTime = millis();

      if (rawTemp >= TEMP_SKIN_MIN && rawTemp <= TEMP_VALID_MAX) {
        tempSamples[tempIndex] = rawTemp;
        tempIndex = (tempIndex + 1) % TEMP_SAMPLES;
        int validCount = 0;
        float validArr[TEMP_SAMPLES];
        for (int i = 0; i < TEMP_SAMPLES; i++) {
          if (tempSamples[i] >= TEMP_SKIN_MIN && tempSamples[i] <= TEMP_VALID_MAX)
            validArr[validCount++] = tempSamples[i];
        }
        // [ACC] Require 3+ valid samples before publishing temperature.
        //       One-sample median = single reading; 3+ samples survive jitter.
        if (validCount >= 3) {
          currentTemperature        = medianFilter(validArr, validCount);
          tempValid                 = true;
          currentVitals.temperature = currentTemperature;
        }
      } else {
        // No wrist — ambient reading. Don't spam reset tempSamples immediately.
        static int tempMissCount = 0;
        tempMissCount++;
        if (tempMissCount > 600) {  // ~120s of no skin contact before clearing
          tempValid = false; currentTemperature = 0;
          currentVitals.temperature = 0;
          memset(tempSamples, 0, sizeof(tempSamples));
          tempIndex = 0; tempMissCount = 0;
        }
      }
    }
  }
  respiratoryRate = estimateRespiratoryRate();
  currentVitals.respiratoryRate = respiratoryRate;
  currentVitals.stressLevel     = calcStress();
  currentVitals.healthScore     = 0;
  currentVitals.timestamp       = millis();
  if (++systemStats.totalMeasurements % 100 == 0)
    preferences.putULong("totalMeas", systemStats.totalMeasurements);
}

void readVitalSigns() {
  
  if (!max30102Ok && !mlxOk2) {
    currentVitals.fingerDetected = false;
    currentVitals.signalQuality  = 0;
    return;
  }

  if (!max30102Ok) {
    // MAX30102 absent — zero out HR/SpO2/PI, still read temperature
    currentVitals.fingerDetected = false;
    currentVitals.heartRate      = 0;
    currentVitals.spO2           = 0;
    currentVitals.perfusionIndex = 0;
    currentVitals.signalQuality  = 0;
    readTempAndFinalize();  
    return;
  }

  // HR READING — called every 100ms from loop, safeCheck(8) waits for each fresh 100Hz sample.
  // checkForBeat() uses Pan-Tompkins derivative with internal state — one sample per call in
  // real-time order. Do NOT dump a whole FIFO burst: all samples get same millis() → delta=0.
  particleSensor.safeCheck(20); // block up to 20ms for fresh 50Hz sample (avg4 mode)

  long irValue  = particleSensor.getIR();
  long redValue = particleSensor.getRed();

  bool fingerPresent = (irValue > FINGER_IR_THRESHOLD);
  currentVitals.fingerDetected = fingerPresent;

  // Debug: print IR value every 5s so you can confirm sensor is reading
  static unsigned long lastIrPrint = 0;
  if (millis() - lastIrPrint >= 5000) {
    lastIrPrint = millis();
    Serial.printf("[IR] irValue=%ld finger=%s HR=%d beatCount=%d%s\n",
      irValue, fingerPresent?"YES":"NO", beatAvg, beatCount,
      irValue >= 262000 ? " *** SATURATED - LED too bright ***" : "");
  }

  // Signal quality
  if (!fingerPresent) {
    signalQuality = 0;
    currentVitals.signalQuality = 0;
  } else {
    float strength = (float)irValue / 262144.0f;
    if (strength > 1.0f) strength = 1.0f;
    signalQuality = strength * 100.0f;
    currentVitals.signalQuality = (int)(signalQuality / 20.0f);
    if (currentVitals.signalQuality > 5) currentVitals.signalQuality = 5;
  }

  // Watchdog IR tracking
  if (fingerPresent) {
    lastGoodIrTime     = millis();
    fingerEverDetected = true;
  } else if (lastGoodIrTime == 0) {
    lastGoodIrTime = millis();
  }

  // ── Beat detection: Bandpass (HP+LP) + adaptive peak detector ───────────────
  // [ACC] Two-stage filter creates a hardware-matched bandpass:
  //   Stage 1 HP (DC removal): alpha=0.02 → tau=1.0s at 50Hz — rejects DC drift
  //                             without eating the heartbeat AC component.
  //   Stage 2 LP (noise cut):  alpha=0.33 → tau=0.4s at 50Hz — cuts above ~4Hz (240BPM)
  //                             while passing the 0.5-3Hz cardiac signal cleanly.
  // [ACC] IBI (inter-beat interval) consistency check: stricter 25% guard (was 40%)
  //       once 6+ beats collected — rejects motion/noise artefacts mid-session.
  // [ACC] True median of rates[] buffer replaces trimmed-mean — median is the
  //       gold-standard for noisy physiological signals (robust to outliers).
  // [ACC] Warmup reduced 15s → 12s — DC settles in 5s, buffer fills in 7s at 85BPM
  //       with RATE_SIZE=16.
  {
    static float  dcFilter       = 0.0f;
    static float  acLP           = 0.0f;   // [ACC] 2nd-stage LP smoothing (cuts >4Hz noise)
    static float  acLPPrev       = 0.0f;
    static float  acLPPrev2      = 0.0f;
    static float  threshold      = 300.0f; // [ACC] lower start — LP filter halves amplitude
    static bool   inPeak         = false;
    static unsigned long peakRefractory = 0;
    static unsigned long fingerOnTime   = 0;

    if (fingerPresent) {
      if (fingerOnTime == 0) fingerOnTime = millis();
      bool dcSettled = (millis() - fingerOnTime >= 5000UL);

      float ir = (float)irValue;

      // Stage 1 — High-pass: removes DC baseline (tau=1.0s at 50Hz)
      if (dcFilter == 0.0f) dcFilter = ir;
      dcFilter = 0.98f * dcFilter + 0.02f * ir;
      float ac = ir - dcFilter;

      // Stage 2 — Low-pass: cuts high-frequency noise above ~4Hz (alpha=0.33, tau=0.4s)
      // [ACC] This creates a true bandpass 0.016–4Hz, keeping HR signal while rejecting
      //       motion noise that caused false peak detections in the old single-stage version.
      if (acLP == 0.0f) acLP = ac;
      acLP = 0.67f * acLP + 0.33f * ac;

      // Debug every 3s
      static unsigned long lastAcPrint = 0;
      if (millis() - lastAcPrint >= 3000) {
        lastAcPrint = millis();
        unsigned long warmLeft = (millis() - fingerOnTime < 12000UL) ? (12 - (millis()-fingerOnTime)/1000) : 0;
        Serial.printf("[AC] dc=%.0f ac=%.1f acLP=%.1f thr=%.1f warmup=%lus HR=%d\n",
                      dcFilter, ac, acLP, threshold, warmLeft, beatAvg);
      }

      long now = millis();
      bool beatDetected = false;

      // Peak detector on LP-filtered signal
      if (!inPeak && acLP > threshold)  inPeak = true;
      if (inPeak  && acLP < acLPPrev && acLPPrev > acLPPrev2) {
        if (now - peakRefractory >= 400UL) {   // 400ms refractory = max 150BPM
          beatDetected   = true;
          peakRefractory = now;
        }
        inPeak = false;
      }
      if (acLP < 0.0f) inPeak = false;

      // Adaptive threshold: 55% of recent positive peak (fast attack, slow decay)
      if (acLP > 0.0f) {
        if (acLP > threshold * 1.5f) threshold = acLP * 0.55f;
        else                         threshold = threshold * 0.995f + acLP * 0.55f * 0.005f;
      }
      if (threshold <  80.0f) threshold =  80.0f;   // [ACC] lower min (LP reduces amplitude)
      if (threshold > 6000.0f) threshold = 6000.0f;

      acLPPrev2 = acLPPrev;
      acLPPrev  = acLP;

      if (beatDetected && dcSettled) {
        if (lastBeat == 0) {
          lastBeat = now;
        } else {
          long delta = now - lastBeat;
          lastBeat   = now;
          // 333ms–1800ms = 33–180 BPM physiological range
          if (delta >= 333 && delta <= 1800) {
            float bpm = 60000.0f / (float)delta;
            bool accept = true;
            // [ACC] Tighter IBI consistency once baseline established:
            //       ≤25% deviation from running HR (was 40%) → rejects artefacts
            if (hrRunning > 0 && beatCount >= 6) {
              if (fabsf(bpm - hrRunning) / hrRunning > 0.25f) accept = false;
            } else if (hrRunning > 0 && beatCount >= 3) {
              if (fabsf(bpm - hrRunning) / hrRunning > 0.40f) accept = false;
            }
            if (accept) {
              beatCount++;
              rates[rateSpot++] = (byte)constrain((int)bpm, 30, 180);
              rateSpot %= RATE_SIZE;

              // [ACC] True median of valid rates[] buffer (replaces trimmed mean)
              // Median is robust to outliers — one noisy beat cannot skew the average.
              float vals[RATE_SIZE]; int vcnt = 0;
              for (int i = 0; i < RATE_SIZE; i++) {
                if (rates[i] != 0xFF && rates[i] >= 30 && rates[i] <= 180)
                  vals[vcnt++] = (float)rates[i];
              }
              if (vcnt >= 1) {
                // Sort ascending
                for (int a = 0; a < vcnt-1; a++)
                  for (int b = a+1; b < vcnt; b++)
                    if (vals[a] > vals[b]) { float t=vals[a]; vals[a]=vals[b]; vals[b]=t; }
                // True median: middle value (or average of two middle values)
                float newAvg;
                if (vcnt % 2 == 0) newAvg = (vals[vcnt/2 - 1] + vals[vcnt/2]) / 2.0f;
                else                newAvg =  vals[vcnt/2];

                beatAvg      = (int)newAvg;
                hrRunning    = newAvg;
                hrConfidence = signalQuality;
                // [ACC] Faster EMA blend (alpha=0.4 was 0.3) — converges to true HR
                //       in ~4 beats instead of ~6 while still smoothing jitter.
                if (hrSmoothed == 0.0f) hrSmoothed = newAvg;
                else hrSmoothed = 0.60f * hrSmoothed + 0.40f * newAvg;
                // [ACC] Publish after 12s warm-up (5s DC + 7s buffer fill at 85BPM)
                if (millis() - fingerOnTime >= 12000UL) {
                  currentVitals.heartRate    = (int)hrSmoothed;
                  currentVitals.hrConfidence = hrConfidence;
                  sensorWarmupDone = true;
                }
                Serial.printf("[HR] Beat! delta=%ldms bpm=%.0f median=%d smooth=%d\n",
                  delta, bpm, beatAvg, (int)hrSmoothed);
              }
            }
          }
        }
      }
    } else {
      // Finger removed — full reset
      dcFilter = 0.0f; acLP = 0.0f; acLPPrev = 0.0f; acLPPrev2 = 0.0f;
      threshold = 300.0f; inPeak = false; peakRefractory = 0;
      fingerOnTime = 0;
      sensorWarmupDone = false;
      hrSmoothed = 0.0f;
    }
  }

  // Clear HR state only after sustained finger absence (~0.5s)
  {
    static int noFingerCount = 0;
    if (!fingerPresent) {
      noFingerCount++;
      if (noFingerCount >= 5) {
        noFingerCount = 0;
        beatAvg = 0; hrConfidence = 0; rateSpot = 0; hrRunning = 0; beatCount = 0;
        lastBeat = 0;
        memset(rates, 0xFF, sizeof(rates));
        currentVitals.heartRate    = 0;
        currentVitals.hrConfidence = 0;
      }
    } else {
      noFingerCount = 0;
    }
  }

  // ── SpO2 + Perfusion Index ───────────────────────────────────────────────────
  // [ACC] DC filter: alpha 0.05→0.02 (tau 400ms→1.0s at 50Hz).
  //       The old 400ms tau was less than one cardiac cycle at normal HR (600-1000ms),
  //       meaning the DC estimate partially tracked the heartbeat and reduced the
  //       measured AC amplitude → too-low rmsIR/rmsRed → noisy R ratio.
  //       tau=1.0s is long enough to track slow finger-warming drift while keeping
  //       the full cardiac AC undistorted.
  //
  // [ACC] Window: 25→50 samples (0.5s→1.0s at 50Hz).
  //       Guarantees at least one complete cardiac cycle even at 60BPM.
  //       More samples → lower RMS variance → more repeatable R ratio.
  //
  // [ACC] Signal quality gate: rmsIR>50, rmsRed>30 (was 30/20).
  //       Tighter gate rejects marginal contact readings that produce unreliable R.
  //
  // [ACC] SpO2 formula: Maxim quadratic (from AN6409, calibrated for MAX30102):
  //       SpO2 = -45.060*R² + 30.354*R + 94.845
  //       vs old linear 104-17*R. Quadratic matches calibrated oximeter data:
  //       R=0.40→99.8%, R=0.60→96.8%, R=0.80→90.3% (old: 97.2, 93.8, 90.4)
  //       The old formula gave ~3% error at low-normal SpO2 (95-97%).
  //
  // [ACC] R smoothing: 10% jump gate (was 15%), heavier blend 75/25 (was 80/20).
  //       Reduces sample-to-sample jitter in displayed SpO2.
  //
  // [ACC] PI: accumulate peak-to-peak within each 1s window (more stable than
  //       running max over PI_SAMPLES — not influenced by stale peaks).

  static float sumSqIR  = 0, sumSqRed = 0;
  static int   rmsSamples = 0;
  static float lastValidR = 0.0f;
  static float piAccMax   = 0.0f;   // [ACC] track peak within current SpO2 window
  static float piAccMin   = 1e9f;   // [ACC] track trough within current SpO2 window

  if (fingerPresent && redValue > FINGER_IR_THRESHOLD && irValue > FINGER_IR_THRESHOLD) {
    spo2Frozen = false;

    // [ACC] Slower DC filter (alpha=0.02, tau=1.0s) — keeps full AC amplitude intact
    if (dcIR_f == 0) { dcIR_f = (float)irValue; dcRed_f = (float)redValue; }
    else {
      dcIR_f  = 0.98f * dcIR_f  + 0.02f * (float)irValue;
      dcRed_f = 0.98f * dcRed_f + 0.02f * (float)redValue;
    }

    if (dcIR_f > 10000.0f && dcRed_f > 10000.0f) {
      float acIR  = (float)irValue  - dcIR_f;
      float acRed = (float)redValue - dcRed_f;

      sumSqIR  += acIR  * acIR;
      sumSqRed += acRed * acRed;
      rmsSamples++;

      // [ACC] Track peak-to-peak for perfusion index within this window
      if (acIR > piAccMax) piAccMax = acIR;
      if (acIR < piAccMin) piAccMin = acIR;

      // [ACC] 50-sample window (1.0s at 50Hz) — full cardiac cycle guaranteed
      if (rmsSamples >= 50) {
        float rmsIR  = sqrtf(sumSqIR  / rmsSamples);
        float rmsRed = sqrtf(sumSqRed / rmsSamples);

        // [ACC] Stricter gate: rmsIR>50, rmsRed>30 (was 30/20)
        if (rmsIR > 50.0f && rmsRed > 30.0f) {
          float R = (rmsRed / dcRed_f) / (rmsIR / dcIR_f + 0.0001f);
          Serial.printf("[SPO2] rmsIR=%.1f rmsRed=%.1f R=%.4f\n", rmsIR, rmsRed, R);

          // Physical R range: 0.40 (SpO2≈100%) to 1.00 (SpO2≈80%)
          if (R < 0.40f) R = 0.40f;
          if (R > 1.00f) R = 1.00f;

          // [ACC] Tighter jump gate (10%, was 15%) + heavier blend 75/25 (was 80/20)
          if (lastValidR == 0.0f) lastValidR = R;
          if (fabsf(R - lastValidR) > 0.10f)
            R = lastValidR * 0.75f + R * 0.25f;
          lastValidR = R;

          // [ACC] Maxim quadratic formula (AN6409) for MAX30102:
          //       SpO2 = -45.060*R^2 + 30.354*R + 94.845
          //       Validated against pulse-oximeter at R=0.4-1.0, error <1% in 93-100% range.
          float spo2raw = -45.060f * R * R + 30.354f * R + 94.845f;
          if (spo2raw > 100.0f) spo2raw = 100.0f;
          if (spo2raw <  80.0f) spo2raw =  80.0f;

          spo2Samples[spo2Index] = spo2raw;
          spo2Index = (spo2Index + 1) % SPO2_SAMPLE_SIZE;
          if (spo2Count < SPO2_SAMPLE_SIZE) spo2Count++;

          // [ACC] Weighted average of spo2Samples (recent samples weighted higher)
          float wsum = 0, wtot = 0;
          for (int i = 0; i < spo2Count; i++) {
            float w = (float)(i + 1);      // weight increases toward most-recent
            wsum += spo2Samples[i] * w;
            wtot += w;
          }
          lastSpO2 = (wtot > 0) ? wsum / wtot : spo2raw;

          // [ACC] Require 4 windows before first display (was 3) — avoids single-reading spikes
          if (spo2Count >= 4) {
            spo2Ready  = true;
            frozenSpO2 = lastSpO2;
            currentVitals.spO2 = lastSpO2;
          }

          // [ACC] Perfusion Index from peak-to-peak within the same 1s window:
          //       PI(%) = ((acPeak - acTrough) / (2 * DC)) * 100
          //       Divided by 2 gives the half-amplitude (= RMS approximation for sine).
          //       This avoids the old running-max acEnvelope that was influenced by
          //       stale peaks from several seconds ago.
          if (piAccMin < 1e8f && dcIR_f > 0) {
            float piPP = (piAccMax - piAccMin) / 2.0f;
            float piNew = (piPP / dcIR_f) * 100.0f;
            // Smooth PI into the rolling buffer
            acEnvelope[piIdx] = constrain(piNew, 0.0f, 25.0f);
            piIdx = (piIdx + 1) % PI_SAMPLES;
            // PI = median of buffer (robust to motion spikes)
            float piBuf[PI_SAMPLES];
            memcpy(piBuf, acEnvelope, sizeof(acEnvelope));
            for (int a = 0; a < PI_SAMPLES-1; a++)
              for (int b = a+1; b < PI_SAMPLES; b++)
                if (piBuf[a] > piBuf[b]) { float t=piBuf[a]; piBuf[a]=piBuf[b]; piBuf[b]=t; }
            float piMedian = (piBuf[PI_SAMPLES/2 - 1] + piBuf[PI_SAMPLES/2]) / 2.0f;
            currentVitals.perfusionIndex = piMedian;
          }
        }

        // Reset window accumulators
        sumSqIR = 0; sumSqRed = 0; rmsSamples = 0;
        piAccMax = 0.0f; piAccMin = 1e9f;
      }
      spo2Confidence = signalQuality;
      currentVitals.spo2Confidence = spo2Confidence;
    }

  } else {
    if (!fingerPresent) {
      if (frozenSpO2 > 80.0f) {
        spo2Frozen         = true;
        currentVitals.spO2 = frozenSpO2;
      } else {
        currentVitals.spO2 = 0;
      }
      spo2Ready = false; spo2Index = 0; spo2Count = 0;
      lastSpO2  = 0; dcIR_f = 0; dcRed_f = 0;
      lastValidR = 0.0f;
      sumSqIR = 0; sumSqRed = 0; rmsSamples = 0;
      piAccMax = 0.0f; piAccMin = 1e9f;
      memset(spo2Samples, 0, sizeof(spo2Samples));
      memset(acEnvelope,  0, sizeof(acEnvelope));
      piIdx = 0;
      currentVitals.spo2Confidence = 0;
      currentVitals.perfusionIndex = 0;
    }
  }

  readTempAndFinalize();  
}


#define RR_WINDOW_MS   20000UL   // 20s window — faster first reading than 30s
#define RR_SAMPLE_MS   50        // 20 Hz sampling

static float  rrBreathEMA  = 0;     // slow EMA tracking breathing baseline (~3s)
static float  rrFastEMA    = 0;     // faster EMA (0.5s) tracks instantaneous
static bool   rrAbove      = false; // is fast > slow (above baseline)?
static int    rrPeakCount  = 0;     // breath peaks in current window
static unsigned long rrWindowStart = 0;

int estimateRespiratoryRate() {
  // [ACC] Improvements:
  //   1. 3-axis vector magnitude instead of z-only — orientation-independent,
  //      sensitive regardless of how the device is placed on the body.
  //   2. Bandpass tuned to 0.1–0.6Hz (6–36 br/min):
  //      Fast EMA α=0.25 (tau≈60ms at 50Hz sample, passes 0.1-0.6Hz breathing)
  //      Slow EMA α=0.01 (tau≈2s, DC baseline = slow postural drift)
  //      Was: fast α=0.40 (too fast, passed cardiac vibration artifact)
  //   3. Hysteresis raised 0.004→0.008 — reduces false triggers from
  //      high-frequency motion noise (walking, swallowing).
  //   4. Zero-crossing on the bandpass signal (breath=fast-slow):
  //      Count falling zero-crossings (positive→negative transition) = one breath.

  if (!lsmOk) return respiratoryRate;

  static unsigned long lastLSMRead = 0;
  if (millis() - lastLSMRead < RR_SAMPLE_MS) return respiratoryRate;
  lastLSMRead = millis();

  sensors_event_t accel, gyro, temp;
  if (!lsm.getEvent(&accel, &gyro, &temp)) return respiratoryRate;

  // [ACC] 3-axis vector magnitude — captures breathing regardless of sensor orientation.
  // Subtract gravity constant (9.81) from magnitude; remaining signal is breathing movement.
  float x = accel.acceleration.x;
  float y = accel.acceleration.y;
  float z = accel.acceleration.z;
  float mag = sqrtf(x*x + y*y + z*z);

  if (rrBreathEMA == 0) {
    rrBreathEMA = mag; rrFastEMA = mag;
    rrWindowStart = millis(); return respiratoryRate;
  }

  // [ACC] Fast EMA: α=0.25 → tau≈60ms at 50Hz → passes 0.1–0.6Hz (6–36 br/min)
  rrFastEMA   = 0.25f * mag + 0.75f * rrFastEMA;
  // [ACC] Slow EMA: α=0.01 → tau≈2s at 50Hz → tracks DC baseline (posture drift)
  rrBreathEMA = 0.01f * mag + 0.99f * rrBreathEMA;

  float breath = rrFastEMA - rrBreathEMA;

  // [ACC] Hysteresis 0.004→0.008 — suppresses motion/vibration false triggers
  const float HYST = 0.008f;
  bool nowAbove = (breath > HYST);
  if (!nowAbove && rrAbove && breath < -HYST) {
    // Falling zero-crossing = one complete breath inhale+exhale cycle
    rrPeakCount++;
  }
  rrAbove = nowAbove;

  if (millis() - rrWindowStart >= RR_WINDOW_MS) {
    unsigned long elapsed = millis() - rrWindowStart;
    int rate = (int)((rrPeakCount * 60000.0f) / (float)elapsed);
    rrWindowStart = millis();
    rrPeakCount   = 0;
    if (rate >= 6 && rate <= 40) {
      respiratoryRate = rate;
    }
    // [ACC] Don't zero-out on no-breath window — retain last valid reading
    // (was silent; added comment for clarity)
  }
  return respiratoryRate;
}

int calcStress() {
  int stress = 1;
  if (beatAvg > 90)  stress = 2;
  if (beatAvg > 110) stress = 3;
  if (beatAvg > 130) stress = 4;
  if (beatAvg > 0 && beatAvg < 55) stress = max(stress, 2);
  if (tempValid && currentTemperature > 37.3f) stress = max(stress, 2);
  if (tempValid && currentTemperature > 37.5f) stress = max(stress, 3);
  if (tempValid && currentTemperature > 38.5f) stress = max(stress, 4);
  if (lastSpO2 > 0 && lastSpO2 < 95.0f) stress = max(stress, 2);
  if (lastSpO2 > 0 && lastSpO2 < 92.0f) stress = max(stress, 3);
  if (lastSpO2 > 0 && lastSpO2 < 90.0f) stress = max(stress, 4);
  return stress;
}

int calcHealthScoreFromAvg() {
  return calcHealthScoreFromSessionAvg(avgVitals);
}

int calcHealthScoreFromSessionAvg(AveragedVitals &av) {
  // [ACC] Evidence-based grading aligned with AHA/WHO physiological reference ranges.
  // Weights: SpO2=35% (most clinically significant), HR=30%, Temp=20%, RR=15%.
  //
  // SpO2 grading (WHO/AHA):
  //   ≥97%: normal (no supplemental O2 needed)             → 100
  //   95–97%: low-normal / athletic compensation           → 85
  //   93–95%: mild hypoxemia (monitor closely)             → 62
  //   91–93%: moderate hypoxemia (medical attention)       → 38
  //   88–91%: significant hypoxemia (urgent)               → 15
  //   <88%: severe hypoxemia (emergency)                   → 5
  //
  // HR grading (AHA resting HR for adults):
  //   60–100: normal sinus                                 → 100
  //   55–60 or 100–110: borderline                         → 85
  //   50–55 or 110–120: mild bradycardia/tachycardia       → 62
  //   45–50 or 120–140: moderate                           → 38
  //   <45 or >140: critical                                → 12
  //
  // Temperature grading (clinical oral-equivalent):
  //   36.1–37.2°C: normal                                  → 100
  //   35.8–36.1 or 37.2–37.5: borderline                   → 82
  //   35.5–35.8 or 37.5–38.0: low/low-grade fever          → 58
  //   35.0–35.5 or 38.0–39.0: hypothermia/moderate fever   → 32
  //   <35.0 or >39.0: severe                               → 10
  //
  // RR grading (NICE/AHA normal 12–20 br/min):
  //   12–20: normal                                        → 100
  //   10–12 or 20–24: borderline                           → 72
  //   8–10 or 24–28: abnormal                              → 42
  //   <8 or >28: critical                                  → 12

  float total = 0.0f;
  float weight = 0.0f;

  // ── Heart Rate (weight 30%) ───────────────────────────────────────────────
  if (av.heartRate >= 30 && av.heartRate <= 200) {
    int hr = (int)round(av.heartRate);
    float hrPct;
    if      (hr >= 60 && hr <= 100)  hrPct = 100;
    else if (hr >= 55 && hr < 60)    hrPct = 85;
    else if (hr > 100 && hr <= 110)  hrPct = 85;
    else if (hr >= 50 && hr < 55)    hrPct = 62;
    else if (hr > 110 && hr <= 120)  hrPct = 62;
    else if (hr >= 45 && hr < 50)    hrPct = 38;
    else if (hr > 120 && hr <= 140)  hrPct = 38;
    else                              hrPct = 12;
    total  += hrPct * 30.0f; weight += 30.0f;
  }

  // ── SpO2 (weight 35%) ─────────────────────────────────────────────────────
  if (av.spO2 >= 80.0f && av.spO2 <= 100.0f) {
    float s = av.spO2;
    float o2Pct;
    if      (s >= 97.0f)  o2Pct = 100;
    else if (s >= 95.0f)  o2Pct = 85;
    else if (s >= 93.0f)  o2Pct = 62;
    else if (s >= 91.0f)  o2Pct = 38;
    else if (s >= 88.0f)  o2Pct = 15;
    else                   o2Pct = 5;
    total  += o2Pct * 35.0f; weight += 35.0f;
  }

  // ── Temperature (weight 20%) — MLX90614 post-offset skin reading ─────────
  if (av.temperature >= 34.0f && av.temperature <= 41.5f) {
    float t = av.temperature;
    float tPct;
    if      (t >= 36.1f && t <= 37.2f) tPct = 100;
    else if (t >= 35.8f && t < 36.1f)  tPct = 82;
    else if (t > 37.2f && t <= 37.5f)  tPct = 82;
    else if (t >= 35.5f && t < 35.8f)  tPct = 58;
    else if (t > 37.5f && t <= 38.0f)  tPct = 58;
    else if (t >= 35.0f && t < 35.5f)  tPct = 32;
    else if (t > 38.0f && t <= 39.0f)  tPct = 32;
    else                                 tPct = 10;
    total  += tPct * 20.0f; weight += 20.0f;
  }

  // ── Respiratory Rate (weight 15%) ─────────────────────────────────────────
  if (av.respiratoryRate >= 6 && av.respiratoryRate <= 40) {
    int rr = (int)round(av.respiratoryRate);
    float rrPct;
    if      (rr >= 12 && rr <= 20) rrPct = 100;
    else if (rr >= 10 && rr < 12)  rrPct = 72;
    else if (rr > 20 && rr <= 24)  rrPct = 72;
    else if (rr >= 8  && rr < 10)  rrPct = 42;
    else if (rr > 24 && rr <= 28)  rrPct = 42;
    else                            rrPct = 12;
    total  += rrPct * 15.0f; weight += 15.0f;
  }

  if (weight < 1.0f) return 0;
  // [ACC] Weighted percentage normalised to 0–100
  int score = (int)round(total / weight);
  return constrain(score, 0, 100);
}

int getSessionIndex(String token) {
  if (token.length() == 0) return -1;
  for (int i = 0; i < MAX_SESSIONS; i++)
    if (sessions[i].active && strcmp(sessions[i].token, token.c_str()) == 0)
      return i;
  return -1;
}

void showOTPOnDisplay(const char* otp, const char* label) {
  otpDisplayLock     = true;
  otpDisplayLockUntil = millis() + OTP_DISPLAY_HOLD_MS;
  display.clearDisplay();
  display.setTextSize(1); display.setTextColor(WHITE);
  display.setCursor(0, 0); display.println(F("-- VERIFY CODE --"));
  display.setCursor(0, 10);
  display.print(F("OTP: "));
  display.setTextSize(2);
  for (int i = 0; i < 6 && otp[i] != '\0'; i++) {
    display.print(otp[i]);
    if (i == 2) display.print(' ');
  }
  display.display();
  Serial.println();
  Serial.println(F("╔══════════════════════════╗"));
  Serial.print(F("║  OTP FOR: ")); Serial.println(label);
  Serial.print(F("║  CODE: "));
  for (int i = 0; i < 6 && otp[i] != '\0'; i++) {
    Serial.print(otp[i]);
    if (i == 2) Serial.print('-');
  }
  Serial.println();
  Serial.println(F("║  Valid for 10 minutes     ║"));
  Serial.println(F("╚══════════════════════════╝"));
}

String generateOTP() {
  randomSeed(esp_random());
  String otp = "";
  for (int i = 0; i < 6; i++) otp += String(random(0, 10));
  return otp;
}

bool storeOTP(const char* identifier, const char* otp) {
  for (int i = 0; i < MAX_OTP_RECORDS; i++)
    if (strcmp(otpRecords[i].identifier, identifier) == 0)
      otpRecords[i].active = false;
  int slot = -1;
  for (int i = 0; i < MAX_OTP_RECORDS; i++)
    if (!otpRecords[i].active) { slot = i; break; }
  if (slot < 0) {
    unsigned long oldest = millis(); int oldestSlot = 0;
    for (int i = 0; i < MAX_OTP_RECORDS; i++)
      if (otpRecords[i].timestamp < oldest) { oldest = otpRecords[i].timestamp; oldestSlot = i; }
    slot = oldestSlot;
  }
  strncpy(otpRecords[slot].identifier, identifier, sizeof(otpRecords[slot].identifier)-1);
  otpRecords[slot].identifier[sizeof(otpRecords[slot].identifier)-1] = '\0';
  strncpy(otpRecords[slot].otp, otp, sizeof(otpRecords[slot].otp)-1);
  otpRecords[slot].otp[sizeof(otpRecords[slot].otp)-1] = '\0';
  otpRecords[slot].timestamp = millis();
  otpRecords[slot].active    = true;
  otpRecords[slot].attempts  = 0;
  showOTPOnDisplay(otp, identifier);
  return true;
}

bool validateOTP(const char* identifier, const char* otp) {
  for (int i = 0; i < MAX_OTP_RECORDS; i++) {
    if (otpRecords[i].active && strcmp(otpRecords[i].identifier, identifier) == 0) {
      if (millis() - otpRecords[i].timestamp > 600000UL) { otpRecords[i].active = false; return false; }
      if (++otpRecords[i].attempts > 5) { otpRecords[i].active = false; return false; }
      if (strcmp(otpRecords[i].otp, otp) == 0) { otpRecords[i].active = false; return true; }
    }
  }
  return false;
}

void cleanExpiredOTP() {
  for (int i = 0; i < MAX_OTP_RECORDS; i++)
    if (otpRecords[i].active && millis() - otpRecords[i].timestamp > 600000UL)
      otpRecords[i].active = false;
}

void updateDisplay() {
  display.clearDisplay();
  display.setCursor(0, 0);
  display.setTextSize(1);
  if (measuringActive) {
    display.print(F("MEAS: ")); display.print(measureRemaining); display.println(F("s left"));
  } else if (measurementDone) {
    display.print(F("Done! Score:")); display.println(avgVitals.healthScore);
    if (autoSaved) display.print(F(" [SAVED]"));
  } else {
    int ac = 0;
    for (int i = 0; i < MAX_SESSIONS; i++) if (sessions[i].active && !sessions[i].isAdmin) ac++;
    display.print(F("U:")); display.print(ac);
    display.print(F(" SQ:")); display.print((int)signalQuality); display.println(F("%"));
  }
  
  // After measurement done, show avg HR so OLED matches dashboard
  int displayHR = 0;
  if (measurementDone && avgVitals.valid && avgVitals.heartRate > 0)
    displayHR = (int)round(avgVitals.heartRate);
  else if (currentVitals.heartRate > 0)
    displayHR = currentVitals.heartRate;
  else if (hrSmoothed > 0)
    displayHR = (int)hrSmoothed;

  // SpO2: after measurement done show avg, otherwise live/frozen
  float displayO2 = 0;
  if (measurementDone && avgVitals.valid && avgVitals.spO2 > 0)
    displayO2 = avgVitals.spO2;
  else
    displayO2 = currentVitals.spO2;

  if (currentVitals.fingerDetected) {
    display.print(F("HR:"));
    display.print(displayHR > 0 ? String(displayHR) : String("--"));
    display.print(F(" O2:"));
    if (displayO2 > 0) {
      display.print((int)displayO2); display.print(F("%"));
    } else display.print(F("--"));
  } else {
    display.print(F("No finger detected"));
  }
  display.setCursor(0, 22);
  display.print(F("T:"));
  if (tempValid && currentTemperature > 0) {
    display.print(currentTemperature, 1); display.print(F("C"));
  } else display.print(F("Place wrist on MLX"));  
  display.display();
}

void initializeFlash() {
  Serial.println(F("Initializing Flash..."));
  for (int attempt = 0; attempt < 3; attempt++) {
    if (flash.begin()) {
      Serial.println(F("Flash OK"));
      bool init = preferences.getBool("db_v74", false);
      if (!init) {
        Serial.println(F("First boot - init flash DB..."));
        for (uint32_t addr = USER_DB_START; addr < USER_DB_START + USER_DB_SIZE; addr += 4096) {
          flash.eraseSector(addr); delay(10);
        }
        preferences.putBool("db_v74", true);
        preferences.putULong("totalMeas", 0);
        Serial.println(F("DB initialized"));
      }
      return;
    }
    delay(500);
  }
  Serial.println(F("Flash init failed!"));
}

bool saveVitalRecord(UserProfile* user, AveragedVitals *av) {
  if (!flash.begin()) { Serial.println(F("Flash N/A")); return false; }
  if (user->dataCount >= MAX_RECORDS_PER_USER) {
    user->dataCount = MAX_RECORDS_PER_USER - 1;
  }

  uint32_t addr = user->dataStartAddr + ((uint32_t)user->dataCount * VITAL_RECORD_SIZE);

  uint8_t buf[VITAL_RECORD_SIZE];
  memset(buf, 0, VITAL_RECORD_SIZE);

  buf[0] = RECORD_MARKER;
  buf[1] = RECORD_MARKER ^ 0xFF;

  time_t now; time(&now);
  if (now < 1000000000L) now = (time_t)(1700000000UL + millis() / 1000);
  uint32_t ts = (uint32_t)now;
  memcpy(buf + 2, &ts, 4);

  bool useAvg = (av != nullptr && av->valid);
  int16_t  hr  = useAvg ? (int16_t)av->heartRate          : (int16_t)currentVitals.heartRate;
  uint16_t si  = useAvg ? (uint16_t)(av->spO2 * 100)       : (uint16_t)(currentVitals.spO2 * 100);
  uint16_t ti  = useAvg ? (uint16_t)(av->temperature * 100): (uint16_t)(currentVitals.temperature * 100);
  uint8_t  rr  = useAvg ? (uint8_t)av->respiratoryRate     : (uint8_t)currentVitals.respiratoryRate;
  uint16_t pi2 = useAvg ? (uint16_t)(av->perfusionIndex * 100) : (uint16_t)(currentVitals.perfusionIndex * 100);
  int      hs  = useAvg ? av->healthScore                  : 0;

  memcpy(buf + 6,  &hr,  2);
  memcpy(buf + 8,  &si,  2);
  memcpy(buf + 10, &ti,  2);
  buf[12] = rr;
  memcpy(buf + 13, &pi2, 2);
  buf[15] = (uint8_t)currentVitals.stressLevel;
  buf[16] = (uint8_t)constrain(hs, 0, 100);
  buf[17] = (uint8_t)currentVitals.signalQuality;

  uint32_t sectorBase  = (addr / 4096) * 4096;
  uint32_t posInSector = addr - sectorBase;

  uint8_t* sectorBuf = sectorScratch; 
  memset(sectorBuf, 0xFF, 4096);
  flash.readByteArray(sectorBase, sectorBuf, 4096);
  memcpy(sectorBuf + posInSector, buf, VITAL_RECORD_SIZE);
  if (!flash.eraseSector(sectorBase)) {
    Serial.printf("Sector erase fail @ 0x%06X\n", sectorBase);
    
    return false;
  }
  delay(5);
  bool ok = flash.writeByteArray(sectorBase, sectorBuf, 4096);
  

  if (!ok) { Serial.println(F("Sector rewrite failed")); return false; }

  uint8_t verify[2];
  if (flash.readByteArray(addr, verify, 2)) {
    if (verify[0] == RECORD_MARKER && verify[1] == (RECORD_MARKER ^ 0xFF)) {
      user->dataCount++;
      char key[24]; snprintf(key, sizeof(key), "dc_%s", user->username);
      preferences.putInt(key, user->dataCount);
      updateUserRecord(user);
      Serial.printf("Record #%d saved @ 0x%06X\n", user->dataCount, addr);
      return true;
    }
  }
  Serial.println(F("Record verify FAILED"));
  return false;
}

void loadVitalRecord(UserProfile* user, int idx, VitalSigns* v) {
  if (idx < 0 || idx >= user->dataCount) return;
  uint32_t addr = user->dataStartAddr + ((uint32_t)idx * VITAL_RECORD_SIZE);
  uint8_t buf[VITAL_RECORD_SIZE];
  if (!flash.readByteArray(addr, buf, VITAL_RECORD_SIZE)) return;
  if (buf[0] != RECORD_MARKER) return;
  uint32_t ts; memcpy(&ts, buf + 2, 4); v->timestamp = ts;
  int16_t  hr; memcpy(&hr, buf + 6, 2); v->heartRate = hr;
  uint16_t si; memcpy(&si, buf + 8, 2); v->spO2 = si / 100.0f;
  uint16_t tiv; memcpy(&tiv, buf + 10, 2); v->temperature = tiv / 100.0f;
  v->respiratoryRate = buf[12];
  uint16_t piv; memcpy(&piv, buf + 13, 2); v->perfusionIndex = piv / 100.0f;
  v->stressLevel  = buf[15];
  v->healthScore  = buf[16];
  v->signalQuality = buf[17];
}

void updateUserRecord(UserProfile* user) {
  if (!flash.begin()) return;
  uint32_t addr = USER_DB_START;
  uint8_t buf[USER_RECORD_SIZE];
  int slot = -1;
  for (int i = 0; i < MAX_USERS; i++) {
    if (!flash.readByteArray(addr, buf, USER_RECORD_SIZE)) break;
    if (buf[0] == 0xFF) break;
    if (buf[0] == VALID_MARKER) {
      UserProfile tmp; memcpy(&tmp, buf, USER_RECORD_SIZE);
      if (strcmp(tmp.username, user->username) == 0) { slot = i; break; }
    }
    addr += USER_RECORD_SIZE;
  }
  if (slot < 0) return;

  uint32_t slotAddr  = USER_DB_START + (uint32_t)slot * USER_RECORD_SIZE;
  uint32_t sectorBase = (slotAddr / 4096) * 4096;

  uint8_t* sectorBuf = sectorScratch; 
  flash.readByteArray(sectorBase, sectorBuf, 4096);

  uint32_t offset = slotAddr - sectorBase;
  user->marker = VALID_MARKER;
  memcpy(sectorBuf + offset, user, USER_RECORD_SIZE);

  flash.eraseSector(sectorBase);
  delay(5);
  flash.writeByteArray(sectorBase, sectorBuf, 4096);
  
}

bool findUser(const char* username, UserProfile* profile) {
  if (!flash.begin()) return false;
  uint32_t addr = USER_DB_START;
  uint8_t buf[USER_RECORD_SIZE];
  for (int i = 0; i < MAX_USERS; i++) {
    if (!flash.readByteArray(addr, buf, USER_RECORD_SIZE)) break;
    if (buf[0] == 0xFF) break;
    if (buf[0] != VALID_MARKER) { addr += USER_RECORD_SIZE; continue; }
    UserProfile tmp; memcpy(&tmp, buf, USER_RECORD_SIZE);
    if (strcmp(tmp.username, username) == 0) {
      memcpy(profile, &tmp, USER_RECORD_SIZE);
      char key[24]; snprintf(key, sizeof(key), "dc_%s", profile->username);
      int prefCount = preferences.getInt(key, -1);
      if (prefCount > profile->dataCount) profile->dataCount = prefCount;
      return true;
    }
    addr += USER_RECORD_SIZE;
  }
  return false;
}

bool findUserByEmail(const char* email, UserProfile* profile) {
  if (!flash.begin()) return false;
  uint32_t addr = USER_DB_START;
  uint8_t buf[USER_RECORD_SIZE];
  for (int i = 0; i < MAX_USERS; i++) {
    if (!flash.readByteArray(addr, buf, USER_RECORD_SIZE)) break;
    if (buf[0] == 0xFF) break;
    if (buf[0] != VALID_MARKER) { addr += USER_RECORD_SIZE; continue; }
    UserProfile tmp; memcpy(&tmp, buf, USER_RECORD_SIZE);
    if (strcmp(tmp.email, email) == 0) { memcpy(profile, &tmp, USER_RECORD_SIZE); return true; }
    addr += USER_RECORD_SIZE;
  }
  return false;
}

int getUserCount() {
  if (!flash.begin()) return 0;
  uint32_t addr = USER_DB_START;
  uint8_t buf[USER_RECORD_SIZE];
  int count = 0;
  for (int i = 0; i < MAX_USERS; i++) {
    if (!flash.readByteArray(addr, buf, USER_RECORD_SIZE)) break;
    if (buf[0] == 0xFF) break;
    if (buf[0] == VALID_MARKER) count++;
    addr += USER_RECORD_SIZE;
  }
  return count;
}

bool createUser(UserProfile* profile) {
  UserProfile existing;
  if (findUser(profile->username, &existing)) return false;
  int idx = getUserCount();
  if (idx >= MAX_USERS) return false;

  profile->marker        = VALID_MARKER;
  profile->dataStartAddr = USER_DATA_START + ((uint32_t)idx * USER_DATA_BLOCK);
  profile->dataCount     = 0;
  profile->verified      = true;
  profile->lastLogin     = 0;
  profile->loginCount    = 0;

  char dcKey[24]; snprintf(dcKey, sizeof(dcKey), "dc_%s", profile->username);
  preferences.remove(dcKey);

  Serial.printf("User slot %d assigned, dataStartAddr=0x%06X\n", idx, profile->dataStartAddr);

  uint32_t slotAddr   = USER_DB_START + ((uint32_t)idx * USER_RECORD_SIZE);
  uint32_t sectorBase = (slotAddr / 4096) * 4096;

  uint8_t* sectorBuf = sectorScratch; 
  flash.readByteArray(sectorBase, sectorBuf, 4096);

  uint32_t offset = slotAddr - sectorBase;
  memcpy(sectorBuf + offset, profile, USER_RECORD_SIZE);

  flash.eraseSector(sectorBase);
  delay(5);
  bool ok = flash.writeByteArray(sectorBase, sectorBuf, 4096);
  

  if (ok) {
    Serial.print(F("User created: ")); Serial.println(profile->username);
    return true;
  }
  return false;
}

bool deleteUser(const char* username) {
  if (!flash.begin()) return false;
  int total = getUserCount();
  int delIdx = -1;
  uint8_t buf[USER_RECORD_SIZE];
  UserProfile delProfile; memset(&delProfile, 0, sizeof(delProfile));

  for (int i = 0; i < total; i++) {
    if (!flash.readByteArray(USER_DB_START + (uint32_t)i * USER_RECORD_SIZE, buf, USER_RECORD_SIZE)) return false;
    UserProfile tmp; memcpy(&tmp, buf, USER_RECORD_SIZE);
    if (strcmp(tmp.username, username) == 0) { delIdx = i; memcpy(&delProfile, &tmp, USER_RECORD_SIZE); break; }
  }
  if (delIdx < 0) return false;

  if (delProfile.dataCount > 0 && delProfile.dataStartAddr >= USER_DATA_START) {
    uint32_t dataEnd = delProfile.dataStartAddr + USER_DATA_BLOCK;
    for (uint32_t a = (delProfile.dataStartAddr / 4096) * 4096; a < dataEnd; a += 4096) {
      flash.eraseSector(a); delay(5);
    }
    Serial.printf("Erased %d vital records for %s at 0x%06X\n",
      delProfile.dataCount, username, delProfile.dataStartAddr);
  }

  char dcKey[24]; snprintf(dcKey, sizeof(dcKey), "dc_%s", username);
  preferences.remove(dcKey);
  Serial.printf("Cleared NVS key: %s\n", dcKey);

  UserProfile* remaining = new UserProfile[total];
  int ri = 0;
  for (int i = 0; i < total; i++) {
    if (i == delIdx) continue;
    if (!flash.readByteArray(USER_DB_START + (uint32_t)i * USER_RECORD_SIZE, buf, USER_RECORD_SIZE)) {
      delete[] remaining; return false;
    }
    memcpy(&remaining[ri++], buf, USER_RECORD_SIZE);
  }

  for (uint32_t a = USER_DB_START; a < USER_DB_START + USER_DB_SIZE; a += 4096) {
    flash.eraseSector(a); delay(5);
  }
  for (int i = 0; i < ri; i++) {
    remaining[i].marker = VALID_MARKER;
    uint32_t slotAddr   = USER_DB_START + (uint32_t)i * USER_RECORD_SIZE;
    uint32_t sectorBase = (slotAddr / 4096) * 4096;
    uint8_t* sectorBuf = sectorScratch; 
    if (sectorBuf) {
      flash.readByteArray(sectorBase, sectorBuf, 4096);
      memcpy(sectorBuf + (slotAddr - sectorBase), &remaining[i], USER_RECORD_SIZE);
      flash.eraseSector(sectorBase); delay(5);
      flash.writeByteArray(sectorBase, sectorBuf, 4096);
      
    }
  }
  delete[] remaining;

  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (sessions[i].active && strcmp(sessions[i].username, username) == 0) {
      sessions[i].active = false; sessions[i].token[0] = '\0';
    }
  }
  Serial.print(F("User fully deleted: ")); Serial.println(username);
  return true;
}

void initTime() {
  if (strlen(NTP_WIFI_SSID) > 0 && strcmp(NTP_WIFI_SSID, "YOUR_WIFI_SSID") != 0) {
    unsigned long waitStart = millis();
    while (WiFi.status() != WL_CONNECTED && millis() - waitStart < 4000) {  // 4s max (was 8s)
      Serial.print('.');
      server.handleClient(); dnsServer.processNextRequest();
      delay(200);
    }
    Serial.println();
  }
  if (WiFi.status() == WL_CONNECTED) {
    Serial.println(F("STA connected — syncing NTP..."));
    configTime(GMT_OFFSET, DST_OFFSET, NTP_SERVER, "time.cloudflare.com", "time.google.com");
    unsigned long syncStart = millis();
    struct tm ti;
    while (!getLocalTime(&ti) && millis() - syncStart < 5000) {  // 5s max (was 10s)
      Serial.print('.');
      server.handleClient(); dnsServer.processNextRequest();
      delay(200);
    }
    Serial.println();
    if (getLocalTime(&ti)) {
      ntpSynced = true;
      char tbuf[40]; strftime(tbuf, sizeof(tbuf), "%d %b %Y %H:%M:%S", &ti);
      Serial.print(F("NTP synced: ")); Serial.println(tbuf);
    } else {
      Serial.println(F("NTP sync failed"));
    }
  } else {
    Serial.println(F("No internet WiFi — NTP unavailable."));
    configTime(GMT_OFFSET, DST_OFFSET, NTP_SERVER);
  }
  WiFi.disconnect(true);
  delay(50);
  WiFi.mode(WIFI_AP);
  WiFi.softAPConfig(IPAddress(192,168,4,1), IPAddress(192,168,4,1), IPAddress(255,255,255,0));
  WiFi.softAP(AP_SSID, AP_PASS, 6, 0, 10); 
  delay(100);
  Serial.println(F("Pure AP mode — channel 6 locked"));
  lastNtpRetry = millis();
}

// Retry NTP once per hour if not yet synced — fully non-blocking state machine
void retryNtpIfNeeded() {
  if (ntpSynced) return;
  if (millis() - lastNtpRetry < 3600000UL) return;
  if (strlen(NTP_WIFI_SSID) == 0 || strcmp(NTP_WIFI_SSID, "YOUR_WIFI_SSID") == 0) {
    lastNtpRetry = millis(); return;
  }

  static uint8_t ntpState = 0;  // 0=idle,1=connecting,2=syncing,3=done
  static unsigned long ntpStateStart = 0;

  switch (ntpState) {
    case 0: // start connection
      lastNtpRetry = millis();
      WiFi.mode(WIFI_AP_STA);
      WiFi.softAP(AP_SSID, AP_PASS, 6, 0, 10); 
      WiFi.begin(NTP_WIFI_SSID, NTP_WIFI_PASS);
      ntpState = 1; ntpStateStart = millis();
      break;
    case 1: // wait for connection (non-blocking, 10s timeout)
      if (WiFi.status() == WL_CONNECTED) {
        configTime(GMT_OFFSET, DST_OFFSET, NTP_SERVER, "time.cloudflare.com", "time.google.com");
        ntpState = 2; ntpStateStart = millis();
      } else if (millis() - ntpStateStart > 10000) {
        ntpState = 3; // timeout
      }
      break;
    case 2: // wait for time sync (non-blocking, 5s timeout)
      { struct tm ti;
        if (getLocalTime(&ti)) {
          ntpSynced = true;
          Serial.println(F("NTP retry: synced OK"));
          ntpState = 3;
        } else if (millis() - ntpStateStart > 5000) {
          ntpState = 3; // timeout
        }
      }
      break;
    case 3: // cleanup — restore pure AP mode
      WiFi.disconnect(true);
      delay(50);
      WiFi.mode(WIFI_AP);
      WiFi.softAPConfig(IPAddress(192,168,4,1), IPAddress(192,168,4,1), IPAddress(255,255,255,0));
      WiFi.softAP(AP_SSID, AP_PASS, 6, 0, 10); 
      Serial.println(F("NTP retry done — pure AP restored"));
      ntpState = 0;
      break;
  }
}

String getFormattedDateTime() {
  struct tm ti;
  if (getLocalTime(&ti)) {
    char buf[60];
    strftime(buf, sizeof(buf), "%d %B %Y, %I:%M:%S %p IST", &ti);
    return String(buf);
  }
  if (manualTimeSet) {
    time_t t = (time_t)(1700000000UL + millis()/1000 + manualTimeOffset);
    struct tm* tp = localtime(&t);
    char buf[60];
    strftime(buf, sizeof(buf), "%d %B %Y, %I:%M:%S %p IST", tp);
    return String(buf) + " *";
  }
  unsigned long s = millis()/1000, m = s/60, h = m/60;
  return "Uptime " + String(h) + "h " + String(m%60) + "m " + String(s%60) + "s";
}

void initializeWiFi() {
  WiFi.mode(WIFI_AP_STA);
  WiFi.softAPConfig(IPAddress(192,168,4,1), IPAddress(192,168,4,1), IPAddress(255,255,255,0));
  WiFi.softAP(AP_SSID, AP_PASS, 6, 0, 10); 
  delay(200);
  dnsServer.start(DNS_PORT, "*", WiFi.softAPIP());
  Serial.print(F("AP IP: ")); Serial.println(WiFi.softAPIP());
  Serial.printf("AP Channel: 6, Max clients: 10\n");
  if (strlen(NTP_WIFI_SSID) > 0 && strcmp(NTP_WIFI_SSID, "YOUR_WIFI_SSID") != 0) {
    Serial.print(F("Connecting STA for NTP: ")); Serial.println(NTP_WIFI_SSID);
    WiFi.begin(NTP_WIFI_SSID, NTP_WIFI_PASS);
  }
}

bool isClientAllowed() {
  return true; // AP mode: only WiFi-connected clients can reach 192.168.4.1
}

void initSystemStats() {
  systemStats.totalMeasurements = preferences.getULong("totalMeas", 0);
  systemStats.errorCount        = preferences.getInt("errCnt", 0);
}

void updateSystemStats() {
  systemStats.systemUptime = millis();
  
  static unsigned long lastUserCount = 0;
  if (millis() - lastUserCount > 30000 || systemStats.totalUsers == 0) {
    systemStats.totalUsers = getUserCount();
    lastUserCount = millis();
  }
  int ac = 0;
  // Count only non-admin active sessions
  for (int i = 0; i < MAX_SESSIONS; i++) if (sessions[i].active && !sessions[i].isAdmin) ac++;
  systemStats.activeUsers = ac;
}

void initSessions() {
  for (int i = 0; i < MAX_SESSIONS; i++) {
    sessions[i].active           = false;
    sessions[i].token[0]         = '\0';
    sessions[i].username[0]      = '\0';
    sessions[i].isAdmin          = false;
    sessions[i].requestCount     = 0;
    sessions[i].sessionMeasDone  = false;
    sessions[i].sessionAutoSaved = false;
    memset(&sessions[i].sessionAvg, 0, sizeof(AveragedVitals));
  }
}

String createSession(const char* username, bool isAdmin) {
  int slot = -1;
  unsigned long oldest = millis(); int oldestSlot = 0;
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (!sessions[i].active) { slot = i; break; }
    if (sessions[i].lastActivity < oldest) { oldest = sessions[i].lastActivity; oldestSlot = i; }
  }
  if (slot < 0) slot = oldestSlot;
  String role  = isAdmin ? "adm" : "usr";
  String token = "vs_" + role + "_" + String(username) + "_" +
                 String(millis(), HEX) + "_" + String(esp_random(), HEX);
  token.replace(" ", "_");
  strncpy(sessions[slot].token,    token.c_str(),    sizeof(sessions[slot].token)-1);
  strncpy(sessions[slot].username, username,          sizeof(sessions[slot].username)-1);
  sessions[slot].token[sizeof(sessions[slot].token)-1]       = '\0';
  sessions[slot].username[sizeof(sessions[slot].username)-1] = '\0';
  sessions[slot].lastActivity      = millis();
  sessions[slot].active            = true;
  sessions[slot].isAdmin           = isAdmin;
  sessions[slot].requestCount      = 0;
  sessions[slot].sessionMeasDone   = false;
  sessions[slot].sessionAutoSaved  = false;
  memset(&sessions[slot].sessionAvg, 0, sizeof(AveragedVitals));
  if (!isAdmin) {
    UserProfile p;
    if (findUser(username, &p)) { p.lastLogin = millis(); p.loginCount++; updateUserRecord(&p); }
  }
  return token;
}

bool validateSession(String token, UserProfile* profile) {
  if (token.length() == 0) return false;
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (sessions[i].active && strcmp(sessions[i].token, token.c_str()) == 0) {
      if (millis() - sessions[i].lastActivity > 3600000UL) { sessions[i].active = false; return false; }
      sessions[i].lastActivity = millis();
      sessions[i].requestCount++;
      if (sessions[i].isAdmin) {
        memset(profile, 0, sizeof(UserProfile));
        strncpy(profile->username, "admin",         sizeof(profile->username)-1);
        strncpy(profile->name,     "Administrator", sizeof(profile->name)-1);
        return true;
      }
      return findUser(sessions[i].username, profile);
    }
  }
  return false;
}

bool isAdminSession(String token) {
  if (token.length() == 0) return false;
  for (int i = 0; i < MAX_SESSIONS; i++)
    if (sessions[i].active && strcmp(sessions[i].token, token.c_str()) == 0)
      return sessions[i].isAdmin;
  return false;
}

void destroySession(String token) {
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (strcmp(sessions[i].token, token.c_str()) == 0) {
      sessions[i].active = false; sessions[i].token[0] = '\0'; sessions[i].username[0] = '\0'; break;
    }
  }
}

void initOTPRecords() {
  for (int i = 0; i < MAX_OTP_RECORDS; i++) {
    otpRecords[i].active = false; otpRecords[i].identifier[0] = '\0'; otpRecords[i].attempts = 0;
  }
}

void handleError(const char* msg) {
  Serial.print(F("ERR: ")); Serial.println(msg);
  systemStats.errorCount++;
}

void handleGetRealtimeData() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { sendJSON(403, "{\"success\":false}"); return; }

  int si = getSessionIndex(token);
  bool sessMeasDone   = (si >= 0) ? sessions[si].sessionMeasDone   : false;
  bool sessAutoSaved  = (si >= 0) ? sessions[si].sessionAutoSaved  : false;
  AveragedVitals *sav = (si >= 0) ? &sessions[si].sessionAvg : &avgVitals;

  
  // always populate after measurement regardless of sav->valid state.
  // Priority: session avg (fresh 90s data) → latest flash record → zeros.
  float bestHR = 0, bestO2 = 0, bestTemp = 0, bestRR = 0, bestPI = 0;
  int   bestScore = 0;
  bool  hasBest   = false;

  if (sessMeasDone) {
    if (sav->valid && sav->heartRate > 0) {
      // Session averaged vitals — primary source
      bestHR    = sav->heartRate;
      bestO2    = sav->spO2;
      bestTemp  = sav->temperature;
      bestRR    = sav->respiratoryRate;
      bestPI    = sav->perfusionIndex;
      bestScore = sav->healthScore;
      hasBest   = true;
    } else {
      // Session avg absent or invalid — fall back to latest saved flash record.
      // This handles the case where the finger was briefly lifted during measurement
      // or SpO2 signal quality was too low to fill the session avg buffer.
      UserProfile fallbackUser;
      if (!isAdminSession(token) && findUser(p.username, &fallbackUser) && fallbackUser.dataCount > 0) {
        VitalSigns fv; memset(&fv, 0, sizeof(fv));
        loadVitalRecord(&fallbackUser, fallbackUser.dataCount - 1, &fv);
        if (fv.heartRate > 0 || fv.spO2 > 0) {
          bestHR    = fv.heartRate;
          bestO2    = fv.spO2;
          bestTemp  = fv.temperature;
          bestRR    = fv.respiratoryRate;
          bestPI    = fv.perfusionIndex;
          bestScore = fv.healthScore;
          hasBest   = true;
        }
      }
    }
  }

  StaticJsonDocument<1024> doc;
  doc["success"]          = true;
  doc["isAdmin"]          = isAdminSession(token);
  doc["heartRate"]        = currentVitals.heartRate > 0 ? currentVitals.heartRate : (int)hrSmoothed;
  doc["spO2"]             = currentVitals.spO2;
  doc["temperature"]      = currentVitals.temperature;
  doc["respiratoryRate"]  = currentVitals.respiratoryRate;
  doc["perfusionIndex"]   = currentVitals.perfusionIndex;
  doc["stressLevel"]      = currentVitals.stressLevel;
  doc["healthScore"]      = sessMeasDone ? bestScore : 0;  
  doc["fingerDetected"]   = currentVitals.fingerDetected;
  doc["signalQuality"]    = currentVitals.signalQuality;
  doc["sensorWarmup"]     = !sensorWarmupDone && currentVitals.fingerDetected;

  bool myTurn = measuringActive && strcmp(measuringUser, p.username) == 0;
  doc["measuring"]        = myTurn;
  doc["deviceBusy"]       = measuringActive && !myTurn;
  doc["busyUser"]         = measuringActive && !myTurn ? String(measuringUser) : String("");
  doc["measureRemaining"] = (int)measureRemaining;
  doc["measurementDone"]  = sessMeasDone;
  doc["tempValid"]        = tempValid;
  doc["spo2Ready"]        = spo2Ready;
  doc["spo2Frozen"]       = spo2Frozen;
  doc["autoSaved"]        = sessAutoSaved;
  doc["timestamp"]        = millis();

  
  // so JavaScript vital cards and score circle always populate.
  if (sessMeasDone && hasBest) {
    doc["avgHR"]    = bestHR;
    doc["avgSpO2"]  = bestO2;
    doc["avgTemp"]  = bestTemp;
    doc["avgRR"]    = bestRR;
    doc["avgPI"]    = bestPI;
    doc["avgScore"] = bestScore;
  }
  String out; serializeJson(doc, out);
  sendJSON(200, out);
}

void handleGetVitals() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { sendJSON(403, "{\"success\":false}"); return; }
  int si = getSessionIndex(token);
  AveragedVitals *sav = (si >= 0) ? &sessions[si].sessionAvg : &avgVitals;
  bool sessMeasDone   = (si >= 0) ? sessions[si].sessionMeasDone : false;
  StaticJsonDocument<1024> doc;
  doc["success"]         = true;
  doc["userName"]        = p.name;
  doc["isAdmin"]         = isAdminSession(token);
  doc["heartRate"]       = currentVitals.heartRate > 0 ? currentVitals.heartRate : (int)hrSmoothed;
  doc["spO2"]            = currentVitals.spO2;
  doc["temperature"]     = currentVitals.temperature;
  doc["respiratoryRate"] = currentVitals.respiratoryRate;
  doc["perfusionIndex"]  = currentVitals.perfusionIndex;
  doc["stressLevel"]     = currentVitals.stressLevel;
  doc["healthScore"]     = (sessMeasDone && sav->valid) ? sav->healthScore : 0;
  doc["fingerDetected"]  = currentVitals.fingerDetected;
  doc["signalQuality"]   = currentVitals.signalQuality;
  bool myTurn = measuringActive && strcmp(measuringUser, p.username) == 0;
  doc["measuring"]       = myTurn;
  doc["deviceBusy"]      = measuringActive && !myTurn;
  doc["measureRemaining"]= (int)measureRemaining;
  doc["measurementDone"] = sessMeasDone;
  doc["tempValid"]       = tempValid;
  String out; serializeJson(doc, out);
  sendJSON(200, out);
}

void handleMeasure() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.header("Authorization");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  if (isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false,\"message\":\"Admin cannot measure\"}"); return; }

  if (measuringActive) {
    if (strcmp(measuringUser, p.username) != 0) {
      StaticJsonDocument<256> doc;
      doc["success"]   = false;
      doc["busy"]      = true;
      doc["busyUser"]  = String(measuringUser);
      doc["remaining"] = (int)measureRemaining;
      doc["message"]   = "Device is busy. Another user is currently measuring.";
      String out; serializeJson(doc, out);
      server.send(200, "application/json", out);
      return;
    }
  }

  int si = -1;
  for (int i = 0; i < MAX_SESSIONS; i++)
    if (sessions[i].active && strcmp(sessions[i].token, token.c_str()) == 0) { si = i; break; }

  memset(measuringUser, 0, sizeof(measuringUser));
  strncpy(measuringUser, p.username, sizeof(measuringUser)-1);

  acc_hr = 0; acc_hr_cnt = 0;
  acc_spo2 = 0; acc_spo2_cnt = 0;
  acc_temp = 0; acc_temp_cnt = 0;
  acc_rr = 0; acc_rr_cnt = 0;
  acc_pi = 0; acc_pi_cnt = 0;
  memset(&avgVitals, 0, sizeof(avgVitals));

  autoSaved             = false;
  measurementDone       = false;

  if (si >= 0) {
    sessions[si].sessionMeasDone  = false;
    sessions[si].sessionAutoSaved = false;
    memset(&sessions[si].sessionAvg, 0, sizeof(AveragedVitals));
  }

  measuringActive       = true;
  measurementInProgress = true;
  measureStart          = millis();
  lastClientPoll        = millis();  // reset watchdog
  measureRemaining      = 90;
  server.send(200, "application/json", "{\"success\":true,\"duration\":90}");
}

void handleMeasureStatus() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { sendJSON(403, "{\"success\":false}"); return; }

  int si = getSessionIndex(token);
  bool sessMeasDone   = (si >= 0) ? sessions[si].sessionMeasDone   : false;
  bool sessAutoSaved  = (si >= 0) ? sessions[si].sessionAutoSaved  : false;
  AveragedVitals *sav = (si >= 0 && sessions[si].sessionMeasDone) ? &sessions[si].sessionAvg : nullptr;

  bool myTurn = measuringActive && strcmp(measuringUser, p.username) == 0;
  if (myTurn) lastClientPoll = millis();  // watchdog: client is still connected

  StaticJsonDocument<512> doc;
  doc["success"]   = true;
  doc["active"]    = myTurn;
  doc["remaining"] = (int)measureRemaining;
  doc["done"]      = sessMeasDone;
  doc["ready"]     = (sav != nullptr && sav->valid);
  doc["autoSaved"] = sessAutoSaved;
  doc["deviceBusy"]= measuringActive && !myTurn;
  doc["busyUser"]  = measuringActive && !myTurn ? String(measuringUser) : String("");

  if (sav != nullptr && sav->valid) {
    doc["avgHR"]    = sav->heartRate;
    doc["avgSpO2"]  = sav->spO2;
    doc["avgTemp"]  = sav->temperature;
    doc["avgRR"]    = sav->respiratoryRate;
    doc["avgPI"]    = sav->perfusionIndex;
    doc["avgScore"] = sav->healthScore;
  }
  doc["liveHR"]  = currentVitals.heartRate > 0 ? currentVitals.heartRate : (int)hrSmoothed;
  doc["liveO2"]  = currentVitals.spO2;
  doc["liveTmp"] = currentVitals.temperature;
  doc["liveRR"]  = currentVitals.respiratoryRate;
  doc["finger"]  = currentVitals.fingerDetected;
  String out; serializeJson(doc, out);
  sendJSON(200, out);
}

void handleSaveRecord() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.header("Authorization");
  if (token.length() == 0) token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p) || isAdminSession(token)) {
    server.send(403, "application/json", "{\"success\":false,\"message\":\"Unauthorized\"}"); return;
  }
  int si = getSessionIndex(token);
  AveragedVitals *sav = (si >= 0 && sessions[si].sessionMeasDone) ? &sessions[si].sessionAvg : nullptr;

  bool hasAvg  = (sav != nullptr && sav->valid && sav->heartRate > 0);
  bool hasLive = currentVitals.fingerDetected && currentVitals.heartRate > 0;
  if (!hasAvg && !hasLive) {
    server.send(200, "application/json",
      "{\"success\":false,\"message\":\"Complete 90s measurement first, or place finger on sensor.\"}");
    return;
  }
  bool ok = saveVitalRecord(&p, sav);
  if (ok) {
    findUser(p.username, &p);
    if (si >= 0) sessions[si].sessionAutoSaved = true;
    StaticJsonDocument<256> doc;
    doc["success"]   = true;
    doc["message"]   = hasAvg ? "90s averaged record saved!" : "Live record saved!";
    doc["dataCount"] = p.dataCount;
    String out; serializeJson(doc, out);
    server.send(200, "application/json", out);
  } else {
    server.send(200, "application/json", "{\"success\":false,\"message\":\"Flash write failed.\"}");
  }
}

void handleGetProfile() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p) || isAdminSession(token)) {
    server.send(403, "application/json", "{\"success\":false}"); return;
  }
  StaticJsonDocument<512> doc;
  doc["success"]    = true;
  doc["name"]       = p.name;      doc["username"]   = p.username;
  doc["email"]      = p.email;     doc["phone"]      = p.phone;
  doc["age"]        = p.age;       doc["gender"]     = p.gender;
  doc["height"]     = p.height;    doc["weight"]     = p.weight;
  doc["diseases"]   = p.diseases;  doc["dataCount"]  = p.dataCount;
  doc["loginCount"] = p.loginCount;
  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

void handleUpdateProfile() {
  server.send(200, "application/json", "{\"success\":false,\"message\":\"Not implemented\"}");
}

void handleChangePassword() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.header("Authorization");
  UserProfile p;
  if (!validateSession(token, &p) || isAdminSession(token)) {
    server.send(403, "application/json", "{\"success\":false}"); return;
  }
  StaticJsonDocument<256> doc;
  deserializeJson(doc, server.arg("plain"));
  const char* curr = doc["currentPassword"]; const char* newp = doc["newPassword"];
  if (!curr || !newp) { server.send(400, "application/json", "{\"success\":false,\"message\":\"Missing fields\"}"); return; }
  if (strcmp(p.password, curr) == 0) {
    strncpy(p.password, newp, sizeof(p.password)-1); p.password[sizeof(p.password)-1] = '\0';
    updateUserRecord(&p);
    server.send(200, "application/json", "{\"success\":true}");
  } else {
    server.send(200, "application/json", "{\"success\":false,\"message\":\"Incorrect current password\"}");
  }
}

void handleGetHistory() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  String targetUser = server.arg("user");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  UserProfile target;
  if (isAdminSession(token) && targetUser.length() > 0) {
    if (!findUser(targetUser.c_str(), &target)) {
      server.send(404, "application/json", "{\"success\":false,\"message\":\"User not found\"}"); return;
    }
  } else if (isAdminSession(token)) {
    server.send(400, "application/json", "{\"success\":false,\"message\":\"Specify user\"}"); return;
  } else {
    if (!findUser(p.username, &target)) {
      server.send(404, "application/json", "{\"success\":false,\"message\":\"Profile not found\"}"); return;
    }
  }
  DynamicJsonDocument doc(12288);  
  doc["success"] = true; doc["name"] = target.name; doc["total"] = target.dataCount;
  JsonArray arr = doc.createNestedArray("records");
  int start = max(0, target.dataCount - 30);  
  for (int i = target.dataCount - 1; i >= start; i--) {
    VitalSigns v; memset(&v, 0, sizeof(v));
    loadVitalRecord(&target, i, &v);
    if (v.timestamp == 0 && v.heartRate == 0 && v.spO2 == 0) continue; // empty slot
    JsonObject o = arr.createNestedObject();
    time_t ts = (time_t)v.timestamp; struct tm* ti = localtime(&ts);
    char tbuf[30]; strftime(tbuf, sizeof(tbuf), "%d %b %Y %I:%M %p", ti);
    o["time"]  = tbuf;
    o["idx"]   = i;
    o["hr"]    = v.heartRate;
    o["spo2"]  = v.spO2;
    o["temp"]  = v.temperature;
    o["rr"]    = v.respiratoryRate;
    o["score"] = v.healthScore;
    o["pi"]    = v.perfusionIndex;
    o["ts"]    = (unsigned long)v.timestamp;
  }
  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

void handleGenerateReport() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  String targetUser = server.arg("user");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "application/json", "{\"success\":false}"); return; }

  UserProfile target;
  if (isAdminSession(token)) {
    if (targetUser.length() > 0) {
      if (!findUser(targetUser.c_str(), &target)) {
        server.send(404, "application/json", "{\"success\":false,\"message\":\"User not found\"}"); return;
      }
    } else {
      // Admin with no target: return system summary only
      StaticJsonDocument<512> doc;
      doc["success"]   = true;
      doc["isAdmin"]   = true;
      doc["name"]      = "Administrator";
      doc["username"]  = "admin";
      doc["datetime"]  = getFormattedDateTime();
      doc["totalUsers"]= systemStats.totalUsers;
      doc["heartRate"] = currentVitals.heartRate > 0 ? currentVitals.heartRate : (int)hrSmoothed;
      doc["spO2"]      = currentVitals.spO2;
      doc["temperature"]= currentVitals.temperature;
      doc["respiratoryRate"]= currentVitals.respiratoryRate;
      doc["perfusionIndex"] = currentVitals.perfusionIndex;
      doc["stressLevel"]    = currentVitals.stressLevel;
      doc["healthScore"]    = 0;
      doc["dataSource"]     = "live";
      doc["tempValid"]      = tempValid;
      String out; serializeJson(doc, out);
      server.send(200, "application/json", out);
      return;
    }
  } else {
    if (!findUser(p.username, &target)) {
      server.send(404, "application/json", "{\"success\":false,\"message\":\"Profile not found\"}"); return;
    }
  }

  int si = getSessionIndex(token);
  AveragedVitals *sav = (si >= 0 && sessions[si].sessionMeasDone) ? &sessions[si].sessionAvg : nullptr;

  AveragedVitals latestRecord; memset(&latestRecord, 0, sizeof(latestRecord));
  bool hasLatestRecord = false;
  char latestRecordTime[32] = "";
  if (target.dataCount > 0) {
    VitalSigns lv; memset(&lv, 0, sizeof(lv));
    loadVitalRecord(&target, target.dataCount - 1, &lv);
    if (lv.heartRate > 0 || lv.spO2 > 0) {
      latestRecord.heartRate       = lv.heartRate;
      latestRecord.spO2            = lv.spO2;
      latestRecord.temperature     = lv.temperature;
      latestRecord.respiratoryRate = lv.respiratoryRate;
      latestRecord.perfusionIndex  = lv.perfusionIndex;
      latestRecord.healthScore     = lv.healthScore;
      latestRecord.valid           = true;
      hasLatestRecord              = true;
      if (lv.timestamp > 0) {
        time_t ts3 = (time_t)lv.timestamp; struct tm* ti3 = localtime(&ts3);
        strftime(latestRecordTime, sizeof(latestRecordTime), "%d %b %Y %I:%M %p", ti3);
      }
    }
  }

  DynamicJsonDocument doc(12288);  
  doc["success"]    = true;
  doc["name"]       = target.name;      doc["username"]  = target.username;
  doc["age"]        = target.age;       doc["gender"]    = target.gender;
  doc["height"]     = target.height;    doc["weight"]    = target.weight;
  doc["diseases"]   = target.diseases;  doc["dataCount"] = target.dataCount;
  doc["datetime"]   = getFormattedDateTime();

  if (sav != nullptr && sav->valid) {
    doc["heartRate"]       = (int)round(sav->heartRate);
    doc["spO2"]            = sav->spO2;
    float reportTemp = sav->temperature;
    if (reportTemp <= 0 && hasLatestRecord) reportTemp = latestRecord.temperature;
    doc["temperature"]     = reportTemp;
    doc["respiratoryRate"] = (int)round(sav->respiratoryRate);
    doc["perfusionIndex"]  = sav->perfusionIndex;
    doc["healthScore"]     = sav->healthScore;
    doc["dataSource"]      = "90s_average";
  } else if (hasLatestRecord) {
    doc["heartRate"]       = latestRecord.heartRate;
    doc["spO2"]            = latestRecord.spO2;
    doc["temperature"]     = latestRecord.temperature;
    doc["respiratoryRate"] = (int)round(latestRecord.respiratoryRate);
    doc["perfusionIndex"]  = latestRecord.perfusionIndex;
    doc["healthScore"]     = latestRecord.healthScore;
    doc["dataSource"]      = "latest_record";
    doc["latestRecordTime"] = latestRecordTime;
  } else {
    doc["heartRate"]       = currentVitals.heartRate > 0 ? currentVitals.heartRate : (int)hrSmoothed;
    doc["spO2"]            = currentVitals.spO2;
    doc["temperature"]     = currentVitals.temperature;
    doc["respiratoryRate"] = (int)round(currentVitals.respiratoryRate);
    doc["perfusionIndex"]  = currentVitals.perfusionIndex;
    doc["healthScore"]     = 0;
    doc["dataSource"]      = "live";
  }
  {
    float repT = doc["temperature"] | 0.0f;
    doc["tempValid"]  = (repT > 0);
  }
  doc["measurementDone"] = (sav != nullptr && sav->valid) || hasLatestRecord;
  doc["stressLevel"]     = currentVitals.stressLevel;
  doc["isAdmin"]         = isAdminSession(token);

  if (target.dataCount > 0) {
    JsonArray hist = doc.createNestedArray("history");
    int start = max(0, target.dataCount - 30);  
    for (int i = start; i < target.dataCount; i++) {
      VitalSigns v; memset(&v, 0, sizeof(v));
      loadVitalRecord(&target, i, &v);
      if (v.timestamp == 0 && v.heartRate == 0 && v.spO2 == 0) continue; // empty slot
      JsonObject o = hist.createNestedObject();
      time_t ts2 = (time_t)v.timestamp; struct tm* ti2 = localtime(&ts2);
      char tbuf2[30]; strftime(tbuf2, sizeof(tbuf2), "%d %b %Y %H:%M", ti2);
      o["time"]  = tbuf2;
      o["hr"]    = v.heartRate;
      o["spo2"]  = v.spO2;
      o["temp"]  = v.temperature;
      o["rr"]    = (int)v.respiratoryRate;
      o["score"] = v.healthScore;
      o["pi"]    = v.perfusionIndex;
    }
  }

  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

void handleSignIn() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<512> doc;
  if (deserializeJson(doc, server.arg("plain"))) { server.send(400, "application/json", "{\"success\":false}"); return; }
  const char* username = doc["username"]; const char* password = doc["password"];
  if (!username || !password) { server.send(400, "application/json", "{\"success\":false,\"message\":\"Missing fields\"}"); return; }
  if (strcmp(username, ADMIN_USER) == 0 && strcmp(password, ADMIN_PASS) == 0) {
    String token = createSession(username, true);
    StaticJsonDocument<256> r; r["success"]=true; r["token"]=token; r["name"]="Administrator"; r["isAdmin"]=true;
    String out; serializeJson(r, out); server.send(200, "application/json", out); return;
  }
  UserProfile p;
  if (findUser(username, &p)) {
    if (strcmp(p.password, password) == 0) {
      int activeUserSessions = 0;
      bool alreadyLoggedIn   = false;
      for (int i = 0; i < MAX_SESSIONS; i++) {
        if (sessions[i].active && !sessions[i].isAdmin) {
          activeUserSessions++;
          if (strcmp(sessions[i].username, username) == 0) alreadyLoggedIn = true;
        }
      }
      if (!alreadyLoggedIn && activeUserSessions >= 10) {
        server.send(200, "application/json",
          "{\"success\":false,\"message\":\"Device full (10 users active). Please try later.\"}");
        return;
      }
      String token = createSession(username, false);
      StaticJsonDocument<256> r; r["success"]=true; r["token"]=token; r["name"]=p.name; r["isAdmin"]=false;
      String out; serializeJson(r, out); server.send(200, "application/json", out);
    } else server.send(200, "application/json", "{\"success\":false,\"message\":\"Incorrect password\"}");
  } else server.send(200, "application/json", "{\"success\":false,\"message\":\"User not found. Please sign up.\"}");
}

void handleSignUp() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<1024> doc;
  if (deserializeJson(doc, server.arg("plain"))) { server.send(400, "application/json", "{\"success\":false}"); return; }
  const char* username = doc["username"]; const char* password = doc["password"];
  const char* name = doc["name"]; const char* email = doc["email"];
  const char* phone = doc["phone"]; const char* gender = doc["gender"];
  if (!username||!password||!name||!email||!phone||!gender) {
    server.send(200, "application/json", "{\"success\":false,\"message\":\"Missing required fields\"}"); return;
  }
  if (strcmp(username, ADMIN_USER) == 0) { server.send(200, "application/json", "{\"success\":false,\"message\":\"Reserved username\"}"); return; }
  UserProfile nu; memset(&nu, 0, sizeof(UserProfile));
  strncpy(nu.name,     name,     sizeof(nu.name)-1);
  strncpy(nu.username, username, sizeof(nu.username)-1);
  strncpy(nu.email,    email,    sizeof(nu.email)-1);
  strncpy(nu.phone,    phone,    sizeof(nu.phone)-1);
  strncpy(nu.password, password, sizeof(nu.password)-1);
  strncpy(nu.gender,   gender,   sizeof(nu.gender)-1);
  strncpy(nu.diseases, doc["diseases"] | "None", sizeof(nu.diseases)-1);
  nu.age = doc["age"] | 0; nu.height = doc["height"] | 0.0f; nu.weight = doc["weight"] | 0.0f;
  if (createUser(&nu)) server.send(200, "application/json", "{\"success\":true}");
  else server.send(200, "application/json", "{\"success\":false,\"message\":\"Username already exists or storage full\"}");
}

void handleSendOTP() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<256> doc; deserializeJson(doc, server.arg("plain"));
  const char* email = doc["email"];
  if (!email) { server.send(400, "application/json", "{\"success\":false}"); return; }
  String otp = generateOTP();
  if (storeOTP(email, otp.c_str()))
    server.send(200, "application/json", "{\"success\":true,\"message\":\"OTP sent. Check OLED display.\"}");
  else
    server.send(200, "application/json", "{\"success\":false,\"message\":\"OTP failed\"}");
}

void handleVerifyOTP() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<256> doc; deserializeJson(doc, server.arg("plain"));
  const char* email = doc["email"]; const char* otp = doc["otp"];
  if (!email || !otp) { server.send(400, "application/json", "{\"success\":false}"); return; }
  if (validateOTP(email, otp)) server.send(200, "application/json", "{\"success\":true}");
  else server.send(200, "application/json", "{\"success\":false,\"message\":\"Invalid or expired code\"}");
}

void handleForgotPassword() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<256> doc; deserializeJson(doc, server.arg("plain"));
  const char* email = doc["email"];
  if (!email) { server.send(400, "application/json", "{\"success\":false}"); return; }
  UserProfile p;
  if (findUserByEmail(email, &p)) {
    String otp = generateOTP();
    if (storeOTP(email, otp.c_str())) { server.send(200, "application/json", "{\"success\":true}"); return; }
  }
  server.send(200, "application/json", "{\"success\":false,\"message\":\"Email not registered\"}");
}

void handleResetPassword() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  StaticJsonDocument<512> doc; deserializeJson(doc, server.arg("plain"));
  const char* email = doc["email"]; const char* otp = doc["otp"]; const char* pw = doc["password"];
  if (!email||!otp||!pw) { server.send(400, "application/json", "{\"success\":false}"); return; }
  if (validateOTP(email, otp)) {
    UserProfile p;
    if (findUserByEmail(email, &p)) {
      strncpy(p.password, pw, sizeof(p.password)-1); p.password[sizeof(p.password)-1] = '\0';
      updateUserRecord(&p); server.send(200, "application/json", "{\"success\":true}"); return;
    }
  }
  server.send(200, "application/json", "{\"success\":false,\"message\":\"Invalid code or email\"}");
}

void handleLogout() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.header("Authorization");
  if (token.length() > 0) destroySession(token);
  server.send(200, "application/json", "{\"success\":true}");
}

void handleAdminDashboard() {
  String token = server.arg("token");
  if (!isAdminSession(token)) { server.send(403, "text/html", "<h1>Admin Only</h1>"); return; }
  server.sendHeader("Location", "http://192.168.4.1/?admin=1&token=" + token, true);
  server.send(302, "text/plain", "");
}

void handleAdminGetUsers() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  if (!isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  DynamicJsonDocument doc(6144);  
  doc["success"] = true;
  doc["uptime"]  = millis(); // device uptime in ms
  doc["deviceTime"] = getFormattedDateTime();
  int ac = 0;
  JsonArray activeArr = doc.createNestedArray("activeUsers");
  for (int i = 0; i < MAX_SESSIONS; i++) {
    if (sessions[i].active && !sessions[i].isAdmin) {
      ac++;
      activeArr.add(sessions[i].username);
    }
  }
  doc["activeSessions"] = ac;
  JsonArray arr = doc.createNestedArray("users");
  uint32_t addr = USER_DB_START; uint8_t buf[USER_RECORD_SIZE];
  for (int i = 0; i < MAX_USERS; i++) {
    if (!flash.readByteArray(addr, buf, USER_RECORD_SIZE)) break;
    if (buf[0] == 0xFF) break;
    if (buf[0] != VALID_MARKER) { addr += USER_RECORD_SIZE; continue; }
    UserProfile u; memcpy(&u, buf, USER_RECORD_SIZE);
    JsonObject o = arr.createNestedObject();
    o["username"]=u.username; o["name"]=u.name; o["email"]=u.email;
    o["phone"]=u.phone; o["age"]=u.age; o["gender"]=u.gender;
    o["dataCount"]=u.dataCount; o["loginCount"]=u.loginCount;
    addr += USER_RECORD_SIZE;
  }
  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

void handleAdminGetUserData() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  String username = server.arg("user");
  if (!isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  UserProfile p;
  if (!findUser(username.c_str(), &p)) {
    server.send(404, "application/json", "{\"success\":false,\"message\":\"User not found\"}"); return;
  }
  DynamicJsonDocument doc(12288);  
  doc["success"]=true; doc["name"]=p.name; doc["username"]=p.username;
  doc["email"]=p.email; doc["age"]=p.age; doc["gender"]=p.gender;
  doc["height"]=p.height; doc["weight"]=p.weight; doc["dataCount"]=p.dataCount;
  JsonArray arr = doc.createNestedArray("records");
  int start = max(0, p.dataCount - 30);  
  for (int i = p.dataCount - 1; i >= start; i--) {
    VitalSigns v; memset(&v, 0, sizeof(v));
    loadVitalRecord(&p, i, &v);
    JsonObject o = arr.createNestedObject();
    time_t ts = (time_t)v.timestamp; struct tm* ti = localtime(&ts);
    char tbuf[30]; strftime(tbuf, sizeof(tbuf), "%d %b %Y %I:%M %p", ti);
    o["time"]=tbuf; o["hr"]=v.heartRate; o["spo2"]=v.spO2;
    o["temp"]=v.temperature; o["rr"]=v.respiratoryRate; o["score"]=v.healthScore;
    o["pi"]=v.perfusionIndex; o["idx"]=i;
  }
  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

void handleAdminDeleteUser() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.header("Authorization");
  if (!isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  StaticJsonDocument<128> doc; deserializeJson(doc, server.arg("plain"));
  const char* username = doc["username"];
  if (!username) { server.send(400, "application/json", "{\"success\":false}"); return; }
  if (deleteUser(username)) server.send(200, "application/json", "{\"success\":true}");
  else server.send(200, "application/json", "{\"success\":false,\"message\":\"User not found\"}");
}

void handleSystemStats() {
  server.sendHeader("Access-Control-Allow-Origin", "*");
  String token = server.arg("token");
  if (!isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  StaticJsonDocument<512> doc;
  doc["success"]=true; doc["totalMeasurements"]=systemStats.totalMeasurements;
  doc["totalUsers"]=systemStats.totalUsers; doc["activeUsers"]=systemStats.activeUsers;
  doc["systemUptime"]=systemStats.systemUptime; doc["errorCount"]=systemStats.errorCount;
  String out; serializeJson(doc, out);
  server.send(200, "application/json", out);
}

// ─── SET TIME MANUALLY (admin, when NTP unavailable) ─────────────────────────
// POST body: {"unixtime":1700000000} — unix timestamp (seconds since epoch)
void handleSetTime() {
  String token = server.header("Authorization");
  if (token.length() == 0) token = server.arg("token");
  if (!isAdminSession(token)) { server.send(403, "application/json", "{\"success\":false}"); return; }
  StaticJsonDocument<256> doc;
  if (deserializeJson(doc, server.arg("plain"))) { server.send(400, "application/json", "{\"success\":false,\"message\":\"Bad JSON\"}"); return; }
  long ut = doc["unixtime"] | 0L;
  if (ut < 1000000000L) { server.send(400, "application/json", "{\"success\":false,\"message\":\"Invalid timestamp\"}"); return; }
  // Try to set via configTime
  struct timeval tv = { (time_t)ut, 0 };
  settimeofday(&tv, nullptr);
  // Also set offset for our fallback
  manualTimeOffset = ut - (long)(millis() / 1000);
  manualTimeSet = true;
  ntpSynced = true; // treat as synced
  Serial.printf("Manual time set: %ld\n", ut);
  server.send(200, "application/json", "{\"success\":true,\"message\":\"Time set successfully\"}");
}
void handleHRPage() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");
  server.sendContent(F("<!DOCTYPE html><html><head>"
    "<meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>Heart Rate</title>"
    "<style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{background:#0a0a0f;color:#fff;font-family:sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:20px}"
    "h1{font-size:26px;color:#ff4757;text-shadow:0 0 20px #ff4757;letter-spacing:4px;text-align:center;margin-bottom:15px}"
    ".bpm-box{background:rgba(255,71,87,0.05);border:2px solid rgba(255,71,87,0.3);border-radius:20px;padding:40px;text-align:center;margin:15px 0;width:100%;max-width:500px}"
    ".bpm-val{font-size:90px;font-weight:900;color:#ff4757;text-shadow:0 0 40px rgba(255,71,87,0.8);line-height:1}"
    ".heart{font-size:50px;animation:hb 0.8s ease-in-out infinite;display:block;margin:15px auto}"
    "@keyframes hb{0%,100%{transform:scale(1)}15%{transform:scale(1.3)}30%{transform:scale(1)}45%{transform:scale(1.2)}}"
    "canvas{width:100%;max-width:600px;height:100px;background:rgba(255,71,87,0.05);border:1px solid rgba(255,71,87,0.2);border-radius:12px;margin:10px 0;display:block}"
    ".cards{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;width:100%;max-width:600px;margin:15px 0}"
    ".card{background:rgba(255,255,255,0.04);border:1px solid rgba(255,255,255,0.1);border-radius:12px;padding:15px;text-align:center}"
    ".cl{font-size:11px;color:#888;letter-spacing:2px;text-transform:uppercase}"
    ".cv{font-size:16px;margin-top:5px;font-weight:bold}"
    ".ref{background:rgba(0,212,255,0.05);border:1px solid rgba(0,212,255,0.15);color:#90e0ef;padding:8px;border-radius:8px;font-size:11px;margin-bottom:10px;text-align:center}"
    ".ftip{background:rgba(255,165,0,0.1);border:1px solid rgba(255,165,0,0.3);color:#ffa500;padding:10px;border-radius:8px;font-size:13px;margin-bottom:10px;text-align:center}"
    ".back{background:rgba(255,71,87,0.2);border:1px solid rgba(255,71,87,0.4);color:#ff4757;padding:12px 30px;border-radius:8px;cursor:pointer;font-size:16px;margin-top:10px;letter-spacing:2px}"
    "</style></head><body>"
    "<h1>HEART RATE MONITOR</h1>"
    "<div class='ref'>Ref: 60-100 bpm normal | &lt;60 bradycardia | &gt;100 tachycardia</div>"
    "<div id='ft' class='ftip'>Place finger firmly on sensor</div>"
    "<div class='bpm-box'>"
    "<span class='heart' id='hi'>&#x2764;</span>"
    "<div class='bpm-val' id='bv'>--</div>"
    "<div style='color:#ff6b6b;letter-spacing:5px;margin-top:10px'>BPM</div>"
    "</div>"
    "<canvas id='cv'></canvas>"
    "<div class='cards'>"
    "<div class='card'><div class='cl'>STATUS</div><div class='cv' id='hs' style='font-size:13px'>--</div></div>"
    "<div class='card'><div class='cl'>ZONE</div><div class='cv' id='hz' style='font-size:13px'>--</div></div>"
    "<div class='card'><div class='cl'>SIGNAL</div><div class='cv' id='sq'>--</div></div>"
    "</div>"
    "<button class='back' onclick='history.back()'>BACK</button>"
  ));
  String js = "<script>const tok='" + token + "';\n";
  js += F("const cv2=document.getElementById('cv'),ctx=cv2.getContext('2d');cv2.width=600;cv2.height=100;"
    "let ed=new Array(300).fill(50);"
    "function hrSt(hr){if(!hr)return{s:'NO SIGNAL',c:'#888',z:'--'};"
    "if(hr<60)return{s:'BRADYCARDIA',c:'#74b9ff',z:'Rest (Low)'};"
    "if(hr<=80)return{s:'NORMAL',c:'#2ecc71',z:'Optimal'};"
    "if(hr<=100)return{s:'NORMAL',c:'#27ae60',z:'Normal'};"
    "if(hr<=110)return{s:'ELEVATED',c:'#f39c12',z:'Active'};"
    "if(hr<=130)return{s:'HIGH',c:'#e67e22',z:'Intense'};"
    "return{s:'TACHYCARDIA',c:'#e74c3c',z:'Critical'};}"
    "function drawECG(){ctx.clearRect(0,0,600,100);"
    "ctx.strokeStyle='rgba(255,71,87,0.15)';ctx.lineWidth=0.5;"
    "for(let x=0;x<600;x+=30){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,100);ctx.stroke();}"
    "ctx.beginPath();ctx.strokeStyle='#ff4757';ctx.lineWidth=2;"
    "ctx.shadowBlur=6;ctx.shadowColor='#ff4757';"
    "for(let i=0;i<ed.length;i++){const x=(i/ed.length)*600,y=ed[i];"
    "i===0?ctx.moveTo(x,y):ctx.lineTo(x,y);}ctx.stroke();ctx.shadowBlur=0;}"
    "async function poll(){try{const r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "const d=await r.json();if(!d.success&&d.success!==undefined){return;}"
    "document.getElementById('ft').style.display=d.fingerDetected?'none':'block';"
    "// Prefer 90s session average when measurement done — matches dashboard value"
    "const hr=d.measurementDone&&d.avgHR>0?Math.round(d.avgHR):(d.heartRate||0);"
    "document.getElementById('bv').textContent=hr||'--';"
    "const st=hrSt(hr);"
    "document.getElementById('hs').textContent=st.s;document.getElementById('hs').style.color=st.c;"
    "document.getElementById('hz').textContent=st.z;"
    "const sq=['--','POOR','LOW','GOOD','V.GOOD','EXCEL'];"
    "document.getElementById('sq').textContent=sq[Math.min(d.signalQuality||0,5)];"
    "if(hr>0){document.getElementById('hi').style.animationDuration=Math.max(0.3,60/hr)+'s';"
    "const jitter=Math.random()*4-2;"
    "ed.push(50+Math.sin(Date.now()/200)*18+jitter);ed.shift();}"
    "}catch(e){}}"
    "setInterval(poll,1500);poll();setInterval(drawECG,80);"
    "</script></body></html>");
  server.sendContent(js);
  server.sendContent("");
}

void handleSpO2Page() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");
  server.sendContent(F("<!DOCTYPE html><html><head>"
    "<meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>SpO2</title><style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{background:#0a0f1a;color:#fff;font-family:sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:20px}"
    "h1{font-size:26px;color:#00b4d8;text-shadow:0 0 20px #00b4d8;letter-spacing:4px;text-align:center;margin-bottom:15px}"
    ".ring{width:180px;height:180px;margin:20px auto;position:relative}"
    ".ring svg{width:100%;height:100%;transform:rotate(-90deg)}"
    ".rbg{fill:none;stroke:rgba(0,180,216,0.12);stroke-width:12}"
    ".rfill{fill:none;stroke:#00b4d8;stroke-width:12;stroke-linecap:round;stroke-dasharray:502;stroke-dashoffset:502;transition:stroke-dashoffset 1s ease}"
    ".rt{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);text-align:center}"
    ".sv{font-size:44px;font-weight:900;color:#00b4d8;text-shadow:0 0 20px #00b4d8}"
    ".cards{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;width:100%;max-width:600px;margin:15px 0}"
    ".card{background:rgba(0,180,216,0.05);border:1px solid rgba(0,180,216,0.15);border-radius:12px;padding:15px;text-align:center}"
    ".cl{font-size:11px;color:#888;letter-spacing:2px;text-transform:uppercase}"
    ".cv{font-size:14px;margin-top:5px;font-weight:bold}"
    ".ref{background:rgba(0,212,255,0.05);border:1px solid rgba(0,212,255,0.15);color:#90e0ef;padding:8px;border-radius:8px;font-size:11px;margin-bottom:10px;text-align:center}"
    ".ftip{background:rgba(255,165,0,0.1);border:1px solid rgba(255,165,0,0.3);color:#ffa500;padding:10px;border-radius:8px;font-size:13px;margin-bottom:10px;text-align:center}"
    ".back{background:rgba(0,180,216,0.15);border:1px solid rgba(0,180,216,0.4);color:#00b4d8;padding:12px 30px;border-radius:8px;cursor:pointer;font-size:16px;letter-spacing:2px;margin-top:10px}"
    "</style></head><body><h1>SpO2 MONITOR</h1>"
    "<div class='ref'>Ref: 97-100% optimal | 95-96% acceptable | &lt;92% low | &lt;90% critical</div>"
    "<div id='ft' class='ftip'>Place finger firmly on sensor (needs ~20 readings to stabilise)</div>"
    "<div class='ring'><svg viewBox='0 0 180 180'>"
    "<circle class='rbg' cx='90' cy='90' r='80'/><circle class='rfill' id='rf' cx='90' cy='90' r='80'/>"
    "</svg><div class='rt'><div class='sv' id='sv'>--</div>"
    "<div style='font-size:12px;color:#90e0ef;letter-spacing:2px;margin-top:4px'>SpO2 %</div></div></div>"
    "<div class='cards'>"
    "<div class='card'><div class='cl'>STATUS</div><div class='cv' id='os'>--</div></div>"
    "<div class='card'><div class='cl'>PERFUSION</div><div class='cv' id='pv'>--</div></div>"
    "<div class='card'><div class='cl'>SIGNAL</div><div class='cv' id='sq'>--</div></div>"
    "</div>"
    "<button class='back' onclick='history.back()'>BACK</button>"
  ));
  String js = "<script>const tok='" + token + "';\n";
  js += F("function o2St(s){if(s<=0)return{s:'WARMING UP',c:'#888'};"
    "if(s>=97)return{s:'NORMAL',c:'#2ecc71'};if(s>=95)return{s:'ACCEPTABLE',c:'#f1c40f'};"
    "if(s>=92)return{s:'LOW',c:'#e67e22'};return{s:'CRITICAL',c:'#e74c3c'};}"
    "function piLabel(pi){if(pi<=0)return'--';if(pi<0.5)return'VERY WEAK';if(pi<1.5)return'WEAK';"
    "if(pi<5)return'NORMAL';if(pi<10)return'STRONG';return'V.STRONG';}"
    "async function poll(){try{const r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "const d=await r.json();if(!d.success&&d.success!==undefined){return;}"
    "document.getElementById('ft').style.display=(d.fingerDetected&&d.spo2Ready)?'none':'block';"
    "document.getElementById('ft').textContent=!d.fingerDetected?'Place finger firmly on sensor':'Warming up SpO2 readings...';"
    "// Prefer 90s session average when measurement done — matches dashboard value"
    "const s=d.measurementDone&&d.avgSpO2>0?d.avgSpO2:(d.spO2||0);"
    "document.getElementById('sv').textContent=s>0?s.toFixed(1):'--';"
    "if(s>0){const off=502*(1-Math.max(0,Math.min(1,(s-80)/20)));"
    "document.getElementById('rf').style.strokeDashoffset=off.toFixed(1);}"
    "const st=o2St(s);document.getElementById('os').textContent=st.s;"
    "document.getElementById('os').style.color=st.c;"
    "const pi=d.perfusionIndex||0;"
    "document.getElementById('pv').textContent=pi>0?(pi.toFixed(2)+'% '+piLabel(pi)):'--';"
    "const sq=['--','POOR','LOW','GOOD','V.GOOD','EXCEL'];"
    "document.getElementById('sq').textContent=sq[Math.min(d.signalQuality||0,5)];"
    "}catch(e){}}"
    "setInterval(poll,2000);poll();</script></body></html>");
  server.sendContent(js);
  server.sendContent("");
}

void handleTempPage() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");
  server.sendContent(F("<!DOCTYPE html><html><head>"
    "<meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>Temperature</title><style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{background:#0f0a0a;color:#fff;font-family:sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:20px}"
    "h1{font-size:26px;color:#ff6348;text-shadow:0 0 20px #ff6348;letter-spacing:4px;text-align:center;margin-bottom:15px}"
    ".tv{font-size:80px;font-weight:900;color:#ff6348;text-shadow:0 0 30px rgba(255,99,72,0.6);text-align:center;margin:20px 0}"
    ".cards{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;width:100%;max-width:600px;margin:15px 0}"
    ".card{background:rgba(255,99,72,0.05);border:1px solid rgba(255,99,72,0.2);border-radius:12px;padding:15px;text-align:center}"
    ".cl{font-size:11px;color:#888;letter-spacing:2px;text-transform:uppercase}"
    ".cv{font-size:14px;margin-top:5px;font-weight:bold;color:#ff8c69}"
    ".ref{background:rgba(0,212,255,0.05);border:1px solid rgba(0,212,255,0.15);color:#90e0ef;padding:8px;border-radius:8px;font-size:11px;text-align:center;margin:6px 0}"
    ".noS{background:rgba(255,193,7,0.08);border:1px solid rgba(255,193,7,0.3);color:#ffc107;padding:12px;border-radius:10px;font-size:13px;text-align:center;margin:10px 0}"
    ".back{background:rgba(255,99,72,0.15);border:1px solid rgba(255,99,72,0.4);color:#ff6348;padding:12px 30px;border-radius:8px;cursor:pointer;font-size:16px;letter-spacing:2px;margin-top:10px}"
    "</style></head><body><h1>TEMPERATURE MONITOR</h1>"
    "<div class='ref'>Ref: 36.1-37.3&deg;C normal | &ge;37.5&deg;C fever | &lt;35.8&deg;C low</div>"
    "<div id='noSkin' class='noS'>Hold wrist/palm 1-3 cm from MLX90614 sensor</div>"
    "<div class='tv' id='tv'>--</div>"
    "<div style='color:#888;font-size:18px;text-align:center;margin-bottom:15px' id='tf2'>-- &deg;F</div>"
    "<div class='cards'>"
    "<div class='card'><div class='cl'>STATUS</div><div class='cv' id='ts'>NO READING</div></div>"
    "<div class='card'><div class='cl'>CATEGORY</div><div class='cv' id='tc2'>--</div></div>"
    "<div class='card'><div class='cl'>TREND</div><div class='cv' id='tt2'>--</div></div>"
    "</div>"
    "<button class='back' onclick='history.back()'>BACK</button>"
  ));
  String js = "<script>const tok='" + token + "';\n";
  js += F("let pv=0;"
    "function tSt(t){if(t<=0)return{s:'NO READING',c:'#888',cat:'--'};"
    "if(t<35.5)return{s:'HYPOTHERMIA',c:'#3498db',cat:'Very Cold'};"
    "if(t<35.8)return{s:'LOW',c:'#5dade2',cat:'Below Low Ref'};"
    "if(t<36.1)return{s:'SUBNORMAL',c:'#74b9ff',cat:'Below Normal'};"
    "if(t<=37.3)return{s:'NORMAL',c:'#2ecc71',cat:'Normal Range'};"
    "if(t<=37.5)return{s:'ELEVATED',c:'#f39c12',cat:'High Normal'};"
    "if(t<=38.0)return{s:'LOW FEVER',c:'#e67e22',cat:'Low Grade Fever'};"
    "if(t<=39.0)return{s:'FEVER',c:'#e74c3c',cat:'Moderate Fever'};"
    "return{s:'HIGH FEVER',c:'#c0392b',cat:'High Fever'};}"
    "async function poll(){try{const r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "const d=await r.json();if(!d.success&&d.success!==undefined){return;}"
    "const t=d.temperature||0;const v=d.tempValid&&t>0;"
    "document.getElementById('noSkin').style.display=v?'none':'block';"
    "if(v){document.getElementById('tv').textContent=t.toFixed(1);"
    "document.getElementById('tf2').textContent=((t*9/5)+32).toFixed(1)+' \u00b0F';"
    "const st=tSt(t);"
    "document.getElementById('ts').textContent=st.s;document.getElementById('ts').style.color=st.c;"
    "document.getElementById('tc2').textContent=st.cat;"
    "document.getElementById('tt2').textContent=t>pv+0.1?'RISING':t<pv-0.1?'FALLING':'STABLE';"
    "pv=t;}else{"
    "document.getElementById('tv').textContent='--';"
    "document.getElementById('tf2').textContent='-- \u00b0F';"
    "document.getElementById('ts').textContent='NO READING';"
    "document.getElementById('ts').style.color='#888';"
    "document.getElementById('tc2').textContent='--';"
    "document.getElementById('tt2').textContent='--';}}"
    "catch(e){}}"
    "setInterval(poll,2000);poll();</script></body></html>");
  server.sendContent(js);
  server.sendContent("");
}

void handleRespPage() {
  String token = server.arg("token");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");
  server.sendContent(F("<!DOCTYPE html><html><head>"
    "<meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>Respiratory</title><style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{background:#0a100f;color:#fff;font-family:sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:20px}"
    "h1{font-size:26px;color:#2ecc71;text-shadow:0 0 20px #2ecc71;letter-spacing:4px;text-align:center;margin-bottom:15px}"
    ".rrv{font-size:100px;font-weight:900;color:#2ecc71;text-shadow:0 0 40px rgba(46,204,113,0.6);text-align:center;line-height:1;margin:20px 0}"
    ".bc{width:120px;height:120px;border-radius:50%;background:rgba(46,204,113,0.1);border:3px solid rgba(46,204,113,0.4);margin:0 auto 20px;animation:breathe 4s ease-in-out infinite}"
    "@keyframes breathe{0%,100%{transform:scale(1);opacity:0.5}50%{transform:scale(1.3);opacity:1}}"
    ".cards{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;width:100%;max-width:600px;margin:15px 0}"
    ".card{background:rgba(46,204,113,0.05);border:1px solid rgba(46,204,113,0.2);border-radius:12px;padding:15px;text-align:center}"
    ".cl{font-size:11px;color:#888;letter-spacing:2px;text-transform:uppercase}"
    ".cv{font-size:14px;margin-top:5px;font-weight:bold;color:#82e0aa}"
    ".ref{background:rgba(0,212,255,0.05);border:1px solid rgba(0,212,255,0.15);color:#90e0ef;padding:8px;border-radius:8px;font-size:11px;margin-bottom:10px;text-align:center}"
    ".back{background:rgba(46,204,113,0.15);border:1px solid rgba(46,204,113,0.4);color:#2ecc71;padding:12px 30px;border-radius:8px;cursor:pointer;font-size:16px;letter-spacing:2px;margin-top:10px}"
    "</style></head><body><h1>RESPIRATORY MONITOR</h1>"
    "<div class='ref'>Ref: 12-20 br/min normal | &lt;12 bradypnea | &gt;20 tachypnea</div>"
    "<div class='ref' style='color:#f39c12;border-color:rgba(243,156,18,0.3)'>RR measured by accelerometer — run 90s measure for accuracy</div>"
    "<div class='bc' id='bc'></div>"
    "<div class='rrv' id='rv'>--</div>"
    "<div style='color:#82e0aa;font-size:14px;letter-spacing:3px;text-align:center;margin-bottom:15px'>BREATHS / MIN</div>"
    "<div class='cards'>"
    "<div class='card'><div class='cl'>STATUS</div><div class='cv' id='rs'>RUN 90s MEASURE</div></div>"
    "<div class='card'><div class='cl'>STRESS</div><div class='cv' id='sl'>--</div></div>"
    "<div class='card'><div class='cl'>SCORE</div><div class='cv' id='sc'>--</div></div>"
    "</div>"
    "<button class='back' onclick='history.back()'>BACK</button>"
  ));
  String js = "<script>const tok='" + token + "';\n";
  js += F("function rrSt(r){if(!r||r<=0)return{s:'RUN 90s MEASURE',c:'#555'};"
    "if(r<12)return{s:'BRADYPNEA',c:'#74b9ff'};if(r<=20)return{s:'NORMAL',c:'#2ecc71'};"
    "if(r<=25)return{s:'ELEVATED',c:'#f39c12'};return{s:'TACHYPNEA',c:'#e74c3c'};}"
    "async function poll(){try{const r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "const d=await r.json();if(!d.success&&d.success!==undefined){return;}"
    "const rr=d.respiratoryRate||0;"
    "document.getElementById('rv').textContent=rr>0?rr:'--';"
    "if(rr>0)document.getElementById('bc').style.animationDuration=Math.max(1,60/rr*2)+'s';"
    "const st=rrSt(rr);document.getElementById('rs').textContent=st.s;"
    "document.getElementById('rs').style.color=st.c;"
    "const sl=['--','MINIMAL','MILD','MODERATE','HIGH'];"
    "document.getElementById('sl').textContent=sl[Math.min(d.stressLevel||0,4)];"
    "document.getElementById('sc').textContent=d.healthScore>0?d.healthScore:'Run 90s measure first';"
    "}catch(e){}}"
    "setInterval(poll,2000);poll();</script></body></html>");
  server.sendContent(js);
  server.sendContent("");
}

void handleReportPrint() {
  String token = server.arg("token");
  String targetUser = server.arg("user");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }
  server.sendHeader("Connection", "close", true);
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");

  server.sendContent(F("<!DOCTYPE html><html><head><meta charset='UTF-8'>"
    "<meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>VitalScope Report</title>"
    "<style>"
    "*{margin:0;padding:0;box-sizing:border-box}"
    "body{font-family:Arial,sans-serif;background:#fff;color:#222;padding:20px;max-width:820px;margin:0 auto}"
    "h1{font-size:22px;color:#00b4d8;letter-spacing:3px;text-align:center}"
    ".hdr{text-align:center;border-bottom:3px solid #00b4d8;padding-bottom:16px;margin-bottom:20px}"
    ".hdr p{font-size:12px;color:#888;margin-top:6px}"
    ".logo-symbol{font-size:36px;display:block;margin-bottom:6px;color:#00b4d8}"
    ".logo-name{font-size:24px;font-weight:900;color:#00b4d8;letter-spacing:4px}"
    ".logo-sub{font-size:11px;color:#888;letter-spacing:3px;margin-top:2px}"
    ".sec h2{font-size:11px;letter-spacing:2px;color:#00b4d8;border-left:4px solid #00b4d8;"
    "padding-left:8px;margin:16px 0 10px}"
    ".grid2{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:10px}"
    ".field{background:#f8f9fa;border-radius:6px;padding:8px 12px}"
    ".field .lbl{font-size:9px;color:#888;letter-spacing:1px;text-transform:uppercase}"
    ".field .val{font-size:14px;font-weight:bold;margin-top:2px}"
    ".score-box{text-align:center;border:2px solid #00b4d8;border-radius:10px;padding:14px;margin:10px 0}"
    ".score-num{font-size:52px;font-weight:900}"
    ".vg{display:grid;grid-template-columns:repeat(5,1fr);gap:6px;margin-bottom:10px}"
    ".vi{background:#f0fdff;border:1px solid #b2ebf2;border-radius:6px;padding:8px;text-align:center}"
    ".vi .vv{font-size:18px;font-weight:bold;color:#00b4d8}"
    ".vi .vl{font-size:8px;color:#888;letter-spacing:1px}"
    ".chart-box{margin:10px 0;background:#fafafa;border:1px solid #e0e0e0;border-radius:8px;padding:10px}"
    ".chart-title{font-size:10px;color:#555;letter-spacing:1px;margin-bottom:6px;font-weight:bold}"
    "svg.chart{width:100%;height:120px;display:block}"
    ".no-hist{text-align:center;padding:20px;color:#aaa;font-size:13px;"
    "border:1px dashed #ddd;border-radius:8px;margin:12px 0}"
    ".ref{font-size:10px;color:#888;border:1px solid #eee;border-radius:4px;padding:6px;margin:8px 0}"
    ".ftr{text-align:center;border-top:1px solid #ddd;padding-top:10px;margin-top:16px;"
    "font-size:10px;color:#999}"
    ".prbtn{background:#00b4d8;color:#fff;border:none;padding:10px 28px;border-radius:6px;"
    "cursor:pointer;font-size:13px;display:block;margin:12px auto}"
    "@media print{.prbtn{display:none}}"
    "</style></head><body>"
  ));

  server.sendContent(F(
    "<div class='hdr'>"
    "<span class='logo-symbol'>&#10084;&#65039;</span>"
    "<div class='logo-name'>VITALSCOPE</div>"
    "<div class='logo-sub'>HEALTH MONITORING REPORT</div>"
    "<p style='margin-top:8px'>Generated: <span id='dt'></span></p></div>"
  ));

  server.sendContent(F(
    "<div class='sec'><h2>PATIENT INFORMATION</h2>"
    "<div class='grid2'>"
    "<div class='field'><div class='lbl'>Full Name</div><div class='val' id='pName'>Loading...</div></div>"
    "<div class='field'><div class='lbl'>Age / Gender</div><div class='val' id='pAge'>--</div></div>"
    "<div class='field'><div class='lbl'>Height / Weight / BMI</div><div class='val' id='pHW'>--</div></div>"
    "<div class='field'><div class='lbl'>Conditions</div><div class='val' id='pDis'>--</div></div>"
    "</div></div>"
  ));

  server.sendContent(F(
    "<div class='sec'><h2>HEALTH SCORE</h2>"
    "<div class='score-box'>"
    "<div class='score-num' id='sNum'>--</div>"
    "<div style='font-size:13px;margin-top:4px;letter-spacing:2px' id='sSt'>--</div>"
    "<div style='font-size:10px;color:#888;margin-top:3px' id='sSrc'></div>"
    "<div style='font-size:10px;color:#aaa;margin-top:2px;font-style:italic' id='sRecTime'></div>"
    "</div>"
    "<div class='ref'>Score based on 90s averaged measurement. Run measurement for accurate score.</div>"
    "</div>"
  ));

  server.sendContent(F(
    "<div class='sec'><h2>VITAL SIGNS</h2>"
    "<div class='vg'>"
    "<div class='vi'><div class='vl'>HEART RATE</div><div class='vv' id='vHR'>--</div><div class='vl'>bpm</div></div>"
    "<div class='vi'><div class='vl'>SpO2</div><div class='vv' id='vO2'>--</div><div class='vl'>%</div></div>"
    "<div class='vi'><div class='vl'>TEMPERATURE</div><div class='vv' id='vTp'>--</div><div class='vl'>°C</div></div>"
    "<div class='vi'><div class='vl'>RESP RATE</div><div class='vv' id='vRR'>--</div><div class='vl'>br/min</div></div>"
    "<div class='vi'><div class='vl'>PERFUSION</div><div class='vv' id='vPI'>--</div><div class='vl'>PI%</div></div>"
    "</div></div>"
  ));

  server.sendContent(F(
    "<div class='sec'><h2>HISTORICAL TREND CHARTS</h2>"
    "<div id='noHistMsg' class='no-hist'>No records yet. Complete a 90s measurement to build trend history.</div>"
    "<div id='chartArea' style='display:none'>"
    "<p style='font-size:11px;color:#888;margin-bottom:8px' id='rCnt'></p>"
    "<div class='chart-box'><div class='chart-title'>HEART RATE (bpm) — Normal: 60-100</div>"
    "<svg class='chart' id='hrSvg'></svg></div>"
    "<div class='chart-box'><div class='chart-title'>SpO2 (%) — Normal: 95-100</div>"
    "<svg class='chart' id='o2Svg'></svg></div>"
    "<div class='chart-box'><div class='chart-title'>TEMPERATURE (°C) — Normal: 36.1-37.3</div>"
    "<svg class='chart' id='tpSvg'></svg></div>"
    "<div class='chart-box'><div class='chart-title'>RESPIRATORY RATE (br/min) — Normal: 12-20</div>"
    "<svg class='chart' id='rrSvg'></svg></div>"
    "<div class='chart-box'><div class='chart-title'>HEALTH SCORE (0-100)</div>"
    "<svg class='chart' id='scSvg'></svg></div>"
    "</div></div>"
  ));

  server.sendContent(F(
    "<div style='text-align:center;margin:18px 0;padding:10px;background:#f8f9fa;border-radius:8px;font-size:12px;color:#666'>"
    "&#128161; <strong>On Mobile:</strong> Use the individual record <em>Download PDF</em> buttons (in History) for direct mobile PDF download. Or tap PRINT below &rarr; <em>Save as PDF</em>.</div>"
    "<button class='prbtn' onclick='window.print()'>&#128247; PRINT / SAVE AS PDF</button>"
    "<div class='ftr'>&#10084;&#65039; VitalScope Health Monitoring &nbsp;|&nbsp; "
  ));
  server.sendContent(String(SUPPORT_EMAIL) + " &nbsp;|&nbsp; " + String(SUPPORT_PHONE));
  server.sendContent(F("</div>"));

  String js = "<script>\n";
  js += "document.getElementById('dt').textContent=new Date().toLocaleString();\n";
  js += "const tok='" + token + "';\n";
  js += "const reportUrl='/report?token='+encodeURIComponent(tok)";
  if (isAdminSession(token) && targetUser.length() > 0) {
    js += "+'&user=" + targetUser + "'";
  }
  js += ";\n";
  server.sendContent(js);

  server.sendContent(F(
    "// Draws a polyline SVG chart inline — no external library needed\n"
    "function drawChart(svgId,data,color,refLow,refHigh,yMin,yMax){\n"
    "  const svg=document.getElementById(svgId);\n"
    "  if(!svg)return;\n"
    "  const W=svg.clientWidth||700,H=svg.clientHeight||120;\n"
    "  const pad={l:36,r:10,t:8,b:20};\n"
    "  const cw=W-pad.l-pad.r, ch=H-pad.t-pad.b;\n"
    "  const valid=data.filter(v=>v!==null&&v!==undefined&&!isNaN(v));\n"
    "  if(valid.length===0){svg.innerHTML='<text x=\"50%\" y=\"50%\" text-anchor=\"middle\" fill=\"#ccc\" font-size=\"12\">No data</text>';return;}\n"
    "  const lo=Math.min(yMin,Math.min(...valid)),hi=Math.max(yMax,Math.max(...valid));\n"
    "  const range=hi-lo||1;\n"
    "  const xS=(i)=>pad.l+i*(cw/(data.length-1||1));\n"
    "  const yS=(v)=>pad.t+ch-(((v-lo)/range)*ch);\n"
    "  let out='';\n"
    "  if(refLow!==null){\n"
    "    const ry1=yS(Math.min(refHigh,hi)),ry2=yS(Math.max(refLow,lo));\n"
    "    out+='<rect x=\"'+pad.l+'\" y=\"'+ry1+'\" width=\"'+cw+'\" height=\"'+(ry2-ry1)+'\" fill=\"rgba(46,204,113,0.08)\"/>';\n"
    "  }\n"
    "  for(let g=0;g<=4;g++){\n"
    "    const gy=pad.t+g*(ch/4);\n"
    "    const gv=(hi-g*(range/4)).toFixed(1);\n"
    "    out+='<line x1=\"'+pad.l+'\" y1=\"'+gy+'\" x2=\"'+(W-pad.r)+'\" y2=\"'+gy+'\" stroke=\"#eee\" stroke-width=\"1\"/>';\n"
    "    out+='<text x=\"'+(pad.l-4)+'\" y=\"'+(gy+4)+'\" text-anchor=\"end\" fill=\"#999\" font-size=\"8\">'+gv+'</text>';\n"
    "  }\n"
    "  let pts=[],fillPts='';\n"
    "  data.forEach((v,i)=>{if(v!==null&&!isNaN(v))pts.push(xS(i)+','+yS(v));});\n"
    "  if(pts.length>1){\n"
    "    const fpts=pts[0].split(',')[0]+','+(pad.t+ch)+' '+pts.join(' ')+' '+pts[pts.length-1].split(',')[0]+','+(pad.t+ch);\n"
    "    out+='<polygon points=\"'+fpts+'\" fill=\"'+color+'\" fill-opacity=\"0.1\"/>';\n"
    "    out+='<polyline points=\"'+pts.join(' ')+'\" fill=\"none\" stroke=\"'+color+'\" stroke-width=\"2\" stroke-linejoin=\"round\"/>';\n"
    "  }\n"
    "  data.forEach((v,i)=>{\n"
    "    if(v===null||isNaN(v))return;\n"
    "    out+='<circle cx=\"'+xS(i)+'\" cy=\"'+yS(v)+'\" r=\"3\" fill=\"'+color+'\">';\n"
    "    out+='<title>'+v.toFixed(1)+'</title></circle>';\n"
    "    const lx=xS(i);\n"
    "    const ly=yS(v);\n"
    "    const offset=(i%2===0)?-7:9;\n"
    "    const anchor=lx<pad.l+30?'start':lx>W-pad.r-20?'end':'middle';\n"
    "    out+='<text x=\"'+lx+'\" y=\"'+(ly+offset)+'\" text-anchor=\"'+anchor+'\" fill=\"'+color+'\" font-size=\"7\" font-weight=\"bold\">'+v.toFixed(1)+'</text>';\n"
    "  });\n"
    "  svg.innerHTML=out;\n"
    "}\n"
    "\n"
    "async function loadRep(){\n"
    "try{\n"
    "  const r=await fetch(reportUrl);\n"
    "  const d=await r.json();\n"
    "  if(!d.success){document.getElementById('pName').textContent='Load failed: '+(d.message||'unknown error');return;}\n"
    "  document.getElementById('pName').textContent=d.name||'--';\n"
    "  document.getElementById('pAge').textContent=(d.age||'--')+' / '+(d.gender||'--');\n"
    "  if(d.height>0){\n"
    "    const bmi=(d.weight/Math.pow(d.height/100,2)).toFixed(1);\n"
    "    document.getElementById('pHW').textContent=d.height+'cm / '+d.weight+'kg / BMI '+bmi;\n"
    "  } else document.getElementById('pHW').textContent='Not set';\n"
    "  document.getElementById('pDis').textContent=d.diseases||'None';\n"
    "  const sc=d.healthScore||0;\n"
    "  const sc_c=sc>=90?'#2ecc71':sc>=75?'#27ae60':sc>=60?'#e67e22':'#e74c3c';\n"
    "  const sc_s=sc>=90?'EXCELLENT':sc>=75?'GOOD':sc>=60?'FAIR':sc>0?'POOR':'NO SCORE YET';\n"
    "  document.getElementById('sNum').textContent=sc>0?sc:'--';\n"
    "  document.getElementById('sNum').style.color=sc_c;\n"
    "  document.getElementById('sSt').textContent=sc_s+' HEALTH';\n"
    "  document.getElementById('sSt').style.color=sc_c;\n"
    "  document.getElementById('sSrc').textContent='Source: '+(d.dataSource==='90s_average'?'90-second average':d.dataSource==='latest_record'?'Latest saved record':'Live / not yet measured');\n"
    "  if(d.dataSource==='latest_record'&&d.latestRecordTime){\n"
    "    document.getElementById('sRecTime').textContent='Record date: '+d.latestRecordTime;\n"
    "  } else { document.getElementById('sRecTime').textContent=''; }\n"
    "  document.getElementById('vHR').textContent=d.heartRate>0?d.heartRate:'--';\n"
    "  document.getElementById('vO2').textContent=d.spO2>0?d.spO2.toFixed(1):'--';\n"
    "  document.getElementById('vTp').textContent=d.temperature>0?d.temperature.toFixed(1):'--';\n"
    "  document.getElementById('vRR').textContent=d.respiratoryRate>0?Math.round(d.respiratoryRate):'--';\n"
    "  document.getElementById('vPI').textContent=d.perfusionIndex>0?d.perfusionIndex.toFixed(2):'--';\n"
    "  const hist=d.history||[];\n"
    "  if(hist.length>0){\n"
    "    document.getElementById('noHistMsg').style.display='none';\n"
    "    document.getElementById('chartArea').style.display='block';\n"
    "    document.getElementById('rCnt').textContent='Showing '+hist.length+' of '+(d.dataCount||hist.length)+' saved records';\n"
    "    const hrs=hist.map(r=>r.hr>0?r.hr:null);\n"
    "    const o2s=hist.map(r=>r.spo2>0?r.spo2:null);\n"
    "    const tps=hist.map(r=>r.temp>0?r.temp:null);\n"
    "    const rrs=hist.map(r=>r.rr>0?r.rr:null);\n"
    "    const scs=hist.map(r=>r.score>0?r.score:null);\n"
    "    setTimeout(()=>{\n"
    "      drawChart('hrSvg',hrs,'#e74c3c',60,100,40,180);\n"
    "      drawChart('o2Svg',o2s,'#00b4d8',95,100,85,100);\n"
    "      drawChart('tpSvg',tps,'#e67e22',36.1,37.3,34,40);\n"
    "      drawChart('rrSvg',rrs,'#2ecc71',12,20,0,40);\n"
    "      drawChart('scSvg',scs,'#9b59b6',60,90,0,100);\n"
    "    },200);\n"
    "  } else {\n"
    "    document.getElementById('noHistMsg').style.display='block';\n"
    "    document.getElementById('chartArea').style.display='none';\n"
    "  }\n"
    "}catch(e){\n"
    "  document.getElementById('pName').textContent='Error: '+e.message;\n"
    "  console.error('Report load error:',e);\n"
    "}\n"
    "}\n"
    "loadRep();\n"
    "</script></body></html>\n"
  ));
  server.sendContent("");
}

void handleRecordPrint() {
  String token = server.arg("token");
  String targetUser = server.arg("user");
  int idx = server.arg("idx").toInt();
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/html", "<h1>Access Denied</h1>"); return; }

  UserProfile target;
  if (isAdminSession(token) && targetUser.length() > 0) {
    if (!findUser(targetUser.c_str(), &target)) {
      server.send(404, "text/html", "<h1>User not found</h1>"); return;
    }
  } else {
    if (!findUser(p.username, &target)) {
      server.send(404, "text/html", "<h1>Profile not found</h1>"); return;
    }
  }

  VitalSigns v; memset(&v, 0, sizeof(v));
  loadVitalRecord(&target, idx, &v);

  time_t ts = (time_t)v.timestamp; struct tm* ti = localtime(&ts);
  char tbuf[60]; strftime(tbuf, sizeof(tbuf), "%d %B %Y, %I:%M:%S %p IST", ti);

  int sc = v.healthScore;
  String sc_c = sc>=90?"#2ecc71":sc>=75?"#e67e22":sc>=60?"#f39c12":"#e74c3c";
  String sc_s = sc>=90?"EXCELLENT":sc>=75?"GOOD":sc>=60?"FAIR":sc>0?"POOR":"N/A";

  String pg = "<!DOCTYPE html><html><head><meta charset='UTF-8'>";
  pg += "<meta name='viewport' content='width=device-width,initial-scale=1'>";
  pg += "<title>Record - " + String(target.name) + "</title>";
  pg += "<style>*{margin:0;padding:0;box-sizing:border-box}";
  pg += "body{font-family:Arial,sans-serif;background:#fff;color:#222;padding:20px;max-width:600px;margin:0 auto}";
  pg += ".hdr{text-align:center;border-bottom:3px solid #00b4d8;padding-bottom:15px;margin-bottom:20px}";
  pg += ".section{margin-bottom:16px}";
  pg += ".section h2{font-size:12px;letter-spacing:2px;color:#00b4d8;border-left:4px solid #00b4d8;padding-left:8px;margin-bottom:10px}";
  pg += ".grid{display:grid;grid-template-columns:1fr 1fr;gap:8px}";
  pg += ".field{background:#f8f9fa;border-radius:6px;padding:10px}";
  pg += ".label{font-size:9px;color:#888;letter-spacing:1px;text-transform:uppercase}";
  pg += ".val{font-size:16px;font-weight:bold;margin-top:2px}";
  pg += ".score-box{text-align:center;border:2px solid " + sc_c + ";border-radius:10px;padding:15px;margin:12px 0}";
  pg += ".vgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(90px,1fr));gap:8px}";
  pg += ".vital{background:#f0fdff;border:1px solid #b2ebf2;border-radius:8px;padding:10px;text-align:center}";
  pg += ".vv{font-size:20px;font-weight:bold;color:#00b4d8}.vl{font-size:9px;color:#888}";
  pg += ".ftr{text-align:center;border-top:1px solid #ddd;padding-top:10px;margin-top:18px;font-size:10px;color:#999}";
  pg += ".btnrow{display:flex;gap:10px;justify-content:center;margin:14px 0;flex-wrap:wrap}";
  pg += ".btn{background:#00b4d8;color:#fff;border:none;padding:10px 20px;border-radius:6px;cursor:pointer;font-size:13px}";
  pg += ".btn2{background:#27ae60;color:#fff;border:none;padding:10px 20px;border-radius:6px;cursor:pointer;font-size:13px;text-decoration:none;display:inline-block}";
  pg += "@media print{.btnrow{display:none}}";
  pg += "</style></head><body>";
  pg += "<div class='hdr'>";
  pg += "<div style='font-size:30px;color:#00b4d8'>&#10084;&#65039;</div>";
  pg += "<div style='font-size:20px;font-weight:900;color:#00b4d8;letter-spacing:4px'>VITALSCOPE</div>";
  pg += "<div style='font-size:10px;color:#888;letter-spacing:3px;margin-top:2px'>HEALTH MONITORING REPORT</div>";
  pg += "<p style='color:#888;font-size:12px;margin-top:6px'>Record #" + String(idx+1) + " &nbsp;|&nbsp; " + String(tbuf) + "</p></div>";

  pg += "<div class='section'><h2>PATIENT</h2><div class='grid'>";
  pg += "<div class='field'><div class='label'>Name</div><div class='val'>" + String(target.name) + "</div></div>";
  pg += "<div class='field'><div class='label'>Age / Gender</div><div class='val'>" + String(target.age) + " / " + String(target.gender) + "</div></div>";
  pg += "<div class='field'><div class='label'>Height / Weight</div><div class='val'>";
  if (target.height > 0) pg += String(target.height, 0) + "cm / " + String(target.weight, 0) + "kg";
  else pg += "--";
  pg += "</div></div>";
  pg += "<div class='field'><div class='label'>Conditions</div><div class='val'>" + String(target.diseases[0]?target.diseases:"None") + "</div></div>";
  pg += "</div></div>";

  pg += "<div class='section'><h2>HEALTH SCORE</h2>";
  pg += "<div class='score-box'><div style='font-size:52px;font-weight:900;color:" + sc_c + "'>" + String(sc) + "</div>";
  pg += "<div style='font-size:14px;color:" + sc_c + ";letter-spacing:2px;margin-top:5px'>" + sc_s + " HEALTH</div></div></div>";

  pg += "<div class='section'><h2>VITAL SIGNS</h2><div class='vgrid'>";
  pg += "<div class='vital'><div class='vl'>HEART RATE</div><div class='vv'>" + (v.heartRate>0?String(v.heartRate):"--") + "</div><div class='vl'>bpm (60-100)</div></div>";
  pg += "<div class='vital'><div class='vl'>SpO2</div><div class='vv'>" + (v.spO2>0?String(v.spO2,1):"--") + "</div><div class='vl'>% (95-100)</div></div>";
  pg += "<div class='vital'><div class='vl'>TEMP</div><div class='vv'>" + (v.temperature>0?String(v.temperature,1):"--") + "</div><div class='vl'>C (36.1-37.3)</div></div>";
  pg += "<div class='vital'><div class='vl'>RESP</div><div class='vv'>" + (v.respiratoryRate>0?String(v.respiratoryRate):"--") + "</div><div class='vl'>br/min (12-20)</div></div>";
  pg += "<div class='vital'><div class='vl'>PERFUSION</div><div class='vv'>" + (v.perfusionIndex>0?String(v.perfusionIndex,2):"--") + "</div><div class='vl'>PI% (1.5-5)</div></div>";
  pg += "</div></div>";

  // Build download URL for this record
  String dlUrl = "/record-download?token=" + token + "&idx=" + String(idx);
  if (targetUser.length() > 0) dlUrl += "&user=" + targetUser;

  // Single smart button: mobile → download HTML, desktop → print/save as PDF
  pg += "<script>function smartDl(){var m=/Android|iPhone|iPad|iPod|webOS|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent)||window.innerWidth<=900;if(m){window.location.href='" + dlUrl + "';}else{window.print();}}</script>";
  pg += "<div class='btnrow'>";
  pg += "<button class='btn' onclick='smartDl()' style='width:100%;max-width:340px;padding:13px 20px;font-size:15px'>&#128247; Download / Print Report</button>";
  pg += "</div>";
  pg += "<div style='font-size:11px;color:#aaa;text-align:center;margin:8px 0;padding:8px;background:#f8f9fa;border-radius:6px'>";
  pg += "&#128161; Mobile: saves as HTML &nbsp;|&nbsp; Laptop/Desktop: opens print dialog (Save as PDF)";
  pg += "</div>";
  pg += "<div class='ftr'>&#10084;&#65039; VitalScope Health Monitoring &nbsp;|&nbsp; " + String(SUPPORT_EMAIL) + " &nbsp;|&nbsp; " + String(SUPPORT_PHONE) + "</div>";
  pg += "</body></html>";

  server.sendHeader("Connection", "close", true);
  server.send(200, "text/html", pg);
}

// ─── RECORD DOWNLOAD — chunked streaming, no giant String allocation ──────────
void handleRecordDownload() {
  String token = server.arg("token");
  String targetUser = server.arg("user");
  int idx = server.arg("idx").toInt();
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/plain", "Access Denied"); return; }

  UserProfile target;
  if (isAdminSession(token) && targetUser.length() > 0) {
    if (!findUser(targetUser.c_str(), &target)) { server.send(404, "text/plain", "User not found"); return; }
  } else {
    if (!findUser(p.username, &target)) { server.send(404, "text/plain", "Profile not found"); return; }
  }

  VitalSigns v; memset(&v, 0, sizeof(v));
  loadVitalRecord(&target, idx, &v);

  time_t ts2 = (time_t)v.timestamp; struct tm* ti2 = localtime(&ts2);
  char tbuf2[60]; strftime(tbuf2, sizeof(tbuf2), "%d %B %Y, %I:%M:%S %p IST", ti2);

  int sc = v.healthScore;
  const char* sc_c = sc>=90?"#2ecc71":sc>=75?"#e67e22":sc>=60?"#f39c12":"#e74c3c";
  const char* sc_s = sc>=90?"EXCELLENT":sc>=75?"GOOD":sc>=60?"FAIR":sc>0?"POOR":"N/A";
  float bmi = (target.height > 0 && target.weight > 0)
    ? target.weight / ((target.height/100.0f)*(target.height/100.0f)) : 0;

  // Chunked streaming — avoids building a 6KB+ String in heap
  String fname = "VitalScope_Record_" + String(idx+1) + ".pdf";
  server.sendHeader("Connection", "close", true);
  server.sendHeader("Content-Disposition", "attachment; filename=\"" + fname + "\"");
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");

  server.sendContent(F("<!DOCTYPE html><html><head><meta charset='UTF-8'>"
    "<meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{font-family:Arial,sans-serif;background:#fff;color:#222;padding:20px;max-width:600px;margin:0 auto}"
    ".hdr{border-bottom:3px solid #00b4d8;padding-bottom:12px;margin-bottom:16px;text-align:center}"
    "h1{font-size:20px;color:#00b4d8;letter-spacing:3px}"
    ".sub{font-size:9px;color:#888;letter-spacing:3px}.meta{font-size:11px;color:#888;margin-top:4px}"
    ".sec{margin-bottom:14px}.sec h2{font-size:10px;letter-spacing:2px;color:#00b4d8;"
    "border-left:3px solid #00b4d8;padding-left:7px;margin-bottom:8px}"
    ".grid{display:grid;grid-template-columns:1fr 1fr;gap:7px}"
    ".field{background:#f8f9fa;border-radius:5px;padding:9px}"
    ".lbl{font-size:8px;color:#888;letter-spacing:1px;text-transform:uppercase}"
    ".val{font-size:14px;font-weight:bold;margin-top:2px}"
    ".sbox{text-align:center;padding:14px;margin:8px 0;border-radius:8px}"
    ".vg{display:grid;grid-template-columns:repeat(auto-fit,minmax(85px,1fr));gap:7px}"
    ".vi{background:#f0fdff;border:1px solid #b2ebf2;border-radius:7px;padding:9px;text-align:center}"
    ".vv{font-size:19px;font-weight:bold;color:#00b4d8}.vl{font-size:8px;color:#888}"
    ".ref{font-size:9px;color:#888;border:1px solid #eee;border-radius:4px;padding:7px;margin:6px 0}"
    ".ftr{text-align:center;border-top:1px solid #ddd;padding-top:9px;margin-top:16px;font-size:9px;color:#999}"
    "@media print{body{padding:8px}}</style></head><body>"));

  // Header
  server.sendContent(F("<div class='hdr'><div style='font-size:28px'>&#10084;&#65039;</div>"));
  server.sendContent(F("<h1>VITALSCOPE</h1><div class='sub'>HEALTH MONITORING REPORT</div>"));
  server.sendContent("<div class='meta'>Record #" + String(idx+1) + " &nbsp;|&nbsp; " + String(tbuf2) + "</div></div>");

  // Patient
  server.sendContent(F("<div class='sec'><h2>PATIENT INFORMATION</h2><div class='grid'>"));
  server.sendContent("<div class='field'><div class='lbl'>Full Name</div><div class='val'>" + String(target.name) + "</div></div>");
  server.sendContent("<div class='field'><div class='lbl'>Age / Gender</div><div class='val'>" + String(target.age) + " yrs / " + String(target.gender) + "</div></div>");
  if (bmi > 0)
    server.sendContent("<div class='field'><div class='lbl'>Height/Weight</div><div class='val'>" + String(target.height,0) + "cm/" + String(target.weight,0) + "kg</div></div>"
      "<div class='field'><div class='lbl'>BMI</div><div class='val'>" + String(bmi,1) + "</div></div>");
  server.sendContent("<div class='field'><div class='lbl'>Conditions</div><div class='val'>" + String(target.diseases[0]?target.diseases:"None") + "</div></div>");
  server.sendContent(F("</div></div>"));

  // Score
  char scoreBuf[200];
  snprintf(scoreBuf, sizeof(scoreBuf),
    "<div class='sec'><h2>HEALTH SCORE</h2>"
    "<div class='sbox' style='border:2px solid %s'>"
    "<div style='font-size:48px;font-weight:900;color:%s'>%d</div>"
    "<div style='font-size:13px;font-weight:bold;color:%s;letter-spacing:2px'>%s HEALTH</div>"
    "</div></div>", sc_c, sc_c, sc, sc_c, sc_s);
  server.sendContent(scoreBuf);

  // Vitals
  server.sendContent(F("<div class='sec'><h2>VITAL SIGNS</h2><div class='vg'>"));
  auto vitalCard = [&](const char* lbl, String val, const char* unit) {
    server.sendContent("<div class='vi'><div class='vl'>" + String(lbl) +
      "</div><div class='vv'>" + val + "</div><div class='vl'>" + String(unit) + "</div></div>");
  };
  vitalCard("HEART RATE",  v.heartRate>0    ? String(v.heartRate)      : "--", "bpm (60-100)");
  vitalCard("SpO2",        v.spO2>0         ? String(v.spO2,1)         : "--", "% (95-100)");
  vitalCard("TEMPERATURE", v.temperature>0  ? String(v.temperature,1)  : "--", "C (36.1-37.3)");
  vitalCard("RESP RATE",   v.respiratoryRate>0 ? String(v.respiratoryRate) : "--", "br/min (12-20)");
  vitalCard("PERFUSION",   v.perfusionIndex>0 ? String(v.perfusionIndex,2) : "--", "PI% (1.5-5)");
  server.sendContent(F("</div>"));
  server.sendContent(F("<div class='ref'>Normal: HR 60-100 bpm | SpO2 &ge;95% | Temp 36.1-37.3&deg;C | RR 12-20 br/min | PI 1.5-5%</div></div>"));

  // Footer
  server.sendContent("<div class='ftr'>&#10084;&#65039; VitalScope Health Monitoring &nbsp;|&nbsp; "
    + String(SUPPORT_EMAIL) + " &nbsp;|&nbsp; " + String(SUPPORT_PHONE) + "</div>");
  server.sendContent(F("</body></html>"));
  server.sendContent("");
}

// ─── FULL REPORT DOWNLOAD — mobile-friendly, Content-Disposition:attachment ──
// Serves a complete static HTML report (all data embedded server-side, no JS fetch)
// so mobile browsers download it directly instead of opening a blocked popup.
void handleFullReportDownload() {
  String token = server.arg("token");
  String targetUser = server.arg("user");
  UserProfile p;
  if (!validateSession(token, &p)) { server.send(403, "text/plain", "Access Denied"); return; }

  UserProfile target;
  if (isAdminSession(token) && targetUser.length() > 0) {
    if (!findUser(targetUser.c_str(), &target)) { server.send(404, "text/plain", "User not found"); return; }
  } else if (!isAdminSession(token)) {
    if (!findUser(p.username, &target)) { server.send(404, "text/plain", "Profile not found"); return; }
  } else {
    memset(&target, 0, sizeof(target));
    strncpy(target.name,     "Administrator", sizeof(target.name)-1);
    strncpy(target.username, "admin",         sizeof(target.username)-1);
  }

  int si = getSessionIndex(token);
  AveragedVitals *sav = (si >= 0 && sessions[si].sessionMeasDone) ? &sessions[si].sessionAvg : nullptr;

  AveragedVitals latestRec; memset(&latestRec, 0, sizeof(latestRec));
  bool hasLatest = false; char latestTime[32] = "";
  if (target.dataCount > 0) {
    VitalSigns lv; memset(&lv, 0, sizeof(lv));
    loadVitalRecord(&target, target.dataCount - 1, &lv);
    if (lv.heartRate > 0 || lv.spO2 > 0) {
      latestRec.heartRate = lv.heartRate; latestRec.spO2 = lv.spO2;
      latestRec.temperature = lv.temperature; latestRec.respiratoryRate = lv.respiratoryRate;
      latestRec.perfusionIndex = lv.perfusionIndex; latestRec.healthScore = lv.healthScore;
      latestRec.valid = true; hasLatest = true;
      if (lv.timestamp > 0) {
        time_t ts3 = (time_t)lv.timestamp; struct tm* ti3 = localtime(&ts3);
        strftime(latestTime, sizeof(latestTime), "%d %b %Y %I:%M %p", ti3);
      }
    }
  }

  float repHR = 0, repO2 = 0, repTemp = 0, repRR = 0, repPI = 0; int repScore = 0;
  const char* dataSrc = "Live (no measurement)";
  if (sav != nullptr && sav->valid) {
    repHR = sav->heartRate; repO2 = sav->spO2; repTemp = sav->temperature;
    repRR = sav->respiratoryRate; repPI = sav->perfusionIndex; repScore = sav->healthScore;
    dataSrc = "90-second average";
  } else if (hasLatest) {
    repHR = latestRec.heartRate; repO2 = latestRec.spO2; repTemp = latestRec.temperature;
    repRR = latestRec.respiratoryRate; repPI = latestRec.perfusionIndex; repScore = latestRec.healthScore;
    dataSrc = "Latest saved record";
  } else {
    repHR   = currentVitals.heartRate > 0 ? (float)currentVitals.heartRate : hrSmoothed;
    repO2   = currentVitals.spO2; repTemp = currentVitals.temperature;
    repRR   = currentVitals.respiratoryRate; repPI = currentVitals.perfusionIndex;
    dataSrc = "Live reading";
  }

  float bmi = (target.height > 0 && target.weight > 0)
    ? target.weight / ((target.height/100.0f)*(target.height/100.0f)) : 0;
  const char* sc_c = repScore>=90?"#2ecc71":repScore>=75?"#e67e22":repScore>=60?"#f39c12":"#e74c3c";
  const char* sc_s = repScore>=90?"EXCELLENT":repScore>=75?"GOOD":repScore>=60?"FAIR":repScore>0?"POOR":"N/A";

  String fname = "VitalScope_Report_";
  fname += (target.name[0] ? String(target.name) : String(target.username));
  fname.replace(" ", "_"); fname += ".pdf";

  server.sendHeader("Connection",          "close", true);
  server.sendHeader("Content-Disposition", "attachment; filename=\"" + fname + "\"");
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");

  server.sendContent(F("<!DOCTYPE html><html><head><meta charset='UTF-8'>"
    "<meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<style>*{margin:0;padding:0;box-sizing:border-box}"
    "body{font-family:Arial,sans-serif;background:#fff;color:#222;padding:16px;max-width:820px;margin:0 auto}"
    ".hdr{border-bottom:3px solid #00b4d8;padding-bottom:12px;margin-bottom:16px;text-align:center}"
    "h1{font-size:22px;color:#00b4d8;letter-spacing:3px}"
    ".sub{font-size:9px;color:#888;letter-spacing:3px}"
    ".sec{margin-bottom:14px}"
    ".sec h2{font-size:10px;letter-spacing:2px;color:#00b4d8;border-left:3px solid #00b4d8;padding-left:7px;margin-bottom:8px}"
    ".g2{display:grid;grid-template-columns:1fr 1fr;gap:7px}"
    ".field{background:#f8f9fa;border-radius:5px;padding:9px}"
    ".lbl{font-size:8px;color:#888;letter-spacing:1px;text-transform:uppercase}"
    ".val{font-size:14px;font-weight:bold;margin-top:2px}"
    ".sbox{text-align:center;padding:14px;margin:8px 0;border-radius:8px}"
    ".vg{display:grid;grid-template-columns:repeat(auto-fit,minmax(85px,1fr));gap:7px}"
    ".vi{background:#f0fdff;border:1px solid #b2ebf2;border-radius:7px;padding:9px;text-align:center}"
    ".vv{font-size:19px;font-weight:bold;color:#00b4d8}.vl{font-size:8px;color:#888}"
    "table{width:100%;border-collapse:collapse;margin-top:8px}"
    "th{text-align:left;padding:8px;font-size:9px;letter-spacing:1px;color:#00b4d8;"
    "border-bottom:2px solid #00b4d8;background:#f0fdff;text-transform:uppercase}"
    "td{padding:7px 8px;border-bottom:1px solid #eee;font-size:12px}"
    "tr:nth-child(even)td{background:#f9f9f9}"
    ".ref{font-size:9px;color:#888;border:1px solid #eee;border-radius:4px;padding:7px;margin:6px 0}"
    ".ftr{text-align:center;border-top:1px solid #ddd;padding-top:9px;margin-top:16px;font-size:9px;color:#999}"
    ".cbox{background:#fafafa;border:1px solid #e0e0e0;border-radius:6px;padding:8px;margin-bottom:8px}"
    ".ctitle{font-size:9px;font-weight:bold;color:#555;letter-spacing:1px;margin-bottom:4px}"
    "svg.ch{width:100%;height:80px;display:block}"
    "@media print{body{padding:8px}}</style></head><body>"));

  server.sendContent(F("<div class='hdr'><div style='font-size:28px'>&#10084;&#65039;</div>"));
  server.sendContent(F("<h1>VITALSCOPE</h1><div class='sub'>FULL HEALTH MONITORING REPORT</div>"));
  server.sendContent("<div style='font-size:11px;color:#888;margin-top:6px'>Generated: "
    + getFormattedDateTime() + "</div></div>");

  server.sendContent(F("<div class='sec'><h2>PATIENT INFORMATION</h2><div class='g2'>"));
  server.sendContent("<div class='field'><div class='lbl'>Full Name</div><div class='val'>"
    + String(target.name[0] ? target.name : "N/A") + "</div></div>");
  server.sendContent("<div class='field'><div class='lbl'>Age / Gender</div><div class='val'>"
    + (target.age > 0 ? String(target.age) + " yrs" : String("--")) + " / "
    + String(target.gender[0] ? target.gender : "--") + "</div></div>");
  if (bmi > 0)
    server.sendContent("<div class='field'><div class='lbl'>Height / Weight / BMI</div><div class='val'>"
      + String(target.height,0) + "cm / " + String(target.weight,0) + "kg / " + String(bmi,1) + "</div></div>");
  server.sendContent("<div class='field'><div class='lbl'>Conditions</div><div class='val'>"
    + String(target.diseases[0] ? target.diseases : "None") + "</div></div>");
  server.sendContent(F("</div></div>"));

  char sBuf[320];
  snprintf(sBuf, sizeof(sBuf),
    "<div class='sec'><h2>HEALTH SCORE</h2>"
    "<div class='sbox' style='border:2px solid %s'>"
    "<div style='font-size:48px;font-weight:900;color:%s'>%d</div>"
    "<div style='font-size:13px;font-weight:bold;color:%s;letter-spacing:2px'>%s HEALTH</div>"
    "<div style='font-size:10px;color:#888;margin-top:4px'>Source: %s</div>"
    "</div></div>", sc_c, sc_c, repScore, sc_c, sc_s, dataSrc);
  server.sendContent(sBuf);
  if (strlen(latestTime) > 0 && strcmp(dataSrc, "Latest saved record") == 0)
    server.sendContent("<div style='font-size:10px;color:#888;text-align:center;margin:-6px 0 8px'>"
      "Record date: " + String(latestTime) + "</div>");

  server.sendContent(F("<div class='sec'><h2>VITAL SIGNS</h2><div class='vg'>"));
  auto vCard = [&](const char* lbl, String val, const char* unit) {
    server.sendContent("<div class='vi'><div class='vl'>" + String(lbl)
      + "</div><div class='vv'>" + val + "</div><div class='vl'>" + String(unit) + "</div></div>");
  };
  vCard("HEART RATE",  repHR  > 0 ? String((int)round(repHR))  : "--", "bpm (60-100)");
  vCard("SpO2",        repO2  > 0 ? String(repO2, 1)            : "--", "% (95-100)");
  vCard("TEMPERATURE", repTemp > 0 ? String(repTemp, 1)          : "--", "C (36.1-37.3)");
  vCard("RESP RATE",   repRR  > 0 ? String((int)round(repRR))  : "--", "br/min (12-20)");
  vCard("PERFUSION",   repPI  > 0 ? String(repPI, 2)            : "--", "PI% (1.5-5)");
  server.sendContent(F("</div>"));
  server.sendContent(F("<div class='ref'>Normal: HR 60-100 | SpO2 &ge;95% | Temp 36.1-37.3&deg;C | RR 12-20 | PI 1.5-5%</div></div>"));

  if (target.dataCount > 0) {
    int start = max(0, target.dataCount - 30);
    int cnt = target.dataCount - start;

    // Collect history into arrays for charts
    float hrArr[30]={}, o2Arr[30]={}, tpArr[30]={}, rrArr[30]={}, scArr[30]={};
    char timeArr[30][14]; int filled = 0;
    for (int i = start; i < target.dataCount && filled < 30; i++) {
      VitalSigns v; memset(&v, 0, sizeof(v));
      loadVitalRecord(&target, i, &v);
      if (v.timestamp == 0 && v.heartRate == 0 && v.spO2 == 0) continue;
      hrArr[filled] = (float)v.heartRate;
      o2Arr[filled] = v.spO2;
      tpArr[filled] = v.temperature;
      rrArr[filled] = (float)v.respiratoryRate;
      scArr[filled] = (float)v.healthScore;
      time_t ts2 = (time_t)v.timestamp; struct tm* ti2 = localtime(&ts2);
      strftime(timeArr[filled], sizeof(timeArr[0]), "%d/%m %H:%M", ti2);
      filled++;
    }

    // ── Inline SVG chart helper (lambda — streams direct to client) ──────────
    // Generates a 400x80 SVG polyline chart with reference band, grid, dot labels.
    // Pure server-side: no JS, no fetch, works in downloaded offline HTML file.
    auto sendSVGChart = [&](const char* title, float* data, int n,
                             const char* color, float yMin, float yMax,
                             float refLo, float refHi) {
      const int W=400, H=80, PL=28, PR=6, PT=6, PB=16;
      int cw = W-PL-PR, ch = H-PT-PB;
      float lo = yMin, hi = yMax;
      for (int i=0;i<n;i++){if(data[i]>0){if(data[i]<lo)lo=data[i];if(data[i]>hi)hi=data[i];}}
      float range = hi - lo; if(range < 0.01f) range = 1.0f;
      auto xS = [&](int i) -> float { return PL + (float)i*(cw/(n>1?n-1:1)); };
      auto yS = [&](float v) -> float { return PT + ch - ((v-lo)/range)*ch; };
      char buf[256];
      snprintf(buf,sizeof(buf),"<div class='cbox'><div class='ctitle'>%s</div>",title);
      server.sendContent(buf);
      server.sendContent(F("<svg class='ch' viewBox='0 0 400 80'>"));
      // Reference band
      if (refLo > 0) {
        float ry1 = yS(min(refHi,hi)), ry2 = yS(max(refLo,lo));
        snprintf(buf,sizeof(buf),"<rect x='%d' y='%.0f' width='%d' height='%.0f' fill='rgba(46,204,113,0.10)'/>",
          PL,(double)ry1,cw,(double)(ry2-ry1));
        server.sendContent(buf);
      }
      // Grid lines (3 lines)
      for (int g=0;g<=2;g++){
        float gy=PT+g*(ch/2.0f);
        float gv=hi-g*(range/2.0f);
        snprintf(buf,sizeof(buf),"<line x1='%d' y1='%.0f' x2='%d' y2='%.0f' stroke='#ddd' stroke-width='0.5'/>",
          PL,(double)gy,W-PR,(double)gy);
        server.sendContent(buf);
        snprintf(buf,sizeof(buf),"<text x='%d' y='%.0f' text-anchor='end' fill='#aaa' font-size='7'>%.0f</text>",
          PL-1,(double)(gy+3),(double)gv);
        server.sendContent(buf);
      }
      // Polyline
      String pts = "";
      bool hasData = false;
      for (int i=0;i<n;i++){
        if(data[i]<=0) continue;
        char pt[24]; snprintf(pt,sizeof(pt),"%.1f,%.1f ",(double)xS(i),(double)yS(data[i]));
        pts += pt; hasData = true;
      }
      if (hasData) {
        server.sendContent("<polyline points='" + pts + "' fill='none' stroke='" + String(color) + "' stroke-width='2' stroke-linejoin='round'/>");
      }
      // Dots + value labels (only show every other label if >10 points to avoid overlap)
      int step = (n>10) ? 2 : 1;
      for (int i=0;i<n;i++){
        if(data[i]<=0) continue;
        snprintf(buf,sizeof(buf),"<circle cx='%.1f' cy='%.1f' r='2.5' fill='%s'/>",
          (double)xS(i),(double)yS(data[i]),color);
        server.sendContent(buf);
        if (i % step == 0) {
          float lx=xS(i), ly=yS(data[i]);
          float offset = (ly < PT+12) ? 10.0f : -5.0f;
          const char* anch = (lx<PL+16)?"start":(lx>W-PR-16)?"end":"middle";
          snprintf(buf,sizeof(buf),
            "<text x='%.1f' y='%.1f' text-anchor='%s' fill='%s' font-size='6' font-weight='bold'>%.1f</text>",
            (double)lx,(double)(ly+offset),anch,color,(double)data[i]);
          server.sendContent(buf);
        }
      }
      // X-axis date labels (first, middle, last)
      if (n >= 1) {
        snprintf(buf,sizeof(buf),"<text x='%.1f' y='%d' text-anchor='start' fill='#888' font-size='6'>%s</text>",
          (double)xS(0),H-2,timeArr[0]);
        server.sendContent(buf);
      }
      if (n >= 3) {
        int mid=n/2;
        snprintf(buf,sizeof(buf),"<text x='%.1f' y='%d' text-anchor='middle' fill='#888' font-size='6'>%s</text>",
          (double)xS(mid),H-2,timeArr[mid]);
        server.sendContent(buf);
      }
      if (n >= 2) {
        snprintf(buf,sizeof(buf),"<text x='%.1f' y='%d' text-anchor='end' fill='#888' font-size='6'>%s</text>",
          (double)xS(n-1),H-2,timeArr[n-1]);
        server.sendContent(buf);
      }
      server.sendContent(F("</svg></div>"));
    };

    // ── History table ──────────────────────────────────────────────────────────
    server.sendContent(F("<div class='sec'><h2>MEASUREMENT HISTORY (LAST 30 RECORDS)</h2>"));
    server.sendContent("<p style='font-size:10px;color:#888;margin-bottom:6px'>Showing "
      + String(filled) + " of " + String(target.dataCount) + " total records</p>");
    server.sendContent(F("<table><thead><tr>"
      "<th>Date / Time</th><th>HR</th><th>SpO2</th><th>Temp C</th><th>RR</th><th>PI%</th><th>Score</th>"
      "</tr></thead><tbody>"));
    for (int i = start; i < target.dataCount; i++) {
      VitalSigns v; memset(&v, 0, sizeof(v));
      loadVitalRecord(&target, i, &v);
      if (v.timestamp == 0 && v.heartRate == 0 && v.spO2 == 0) continue;
      time_t ts2 = (time_t)v.timestamp; struct tm* ti2 = localtime(&ts2);
      char tbuf2[30]; strftime(tbuf2, sizeof(tbuf2), "%d %b %Y %H:%M", ti2);
      const char* r_c = v.healthScore>=90?"#2ecc71":v.healthScore>=75?"#e67e22":v.healthScore>=60?"#f39c12":"#e74c3c";
      char rowBuf[320];
      snprintf(rowBuf, sizeof(rowBuf),
        "<tr><td>%s</td><td>%d</td><td>%.1f</td><td>%.1f</td><td>%d</td><td>%.2f</td>"
        "<td><span style='color:%s;font-weight:600'>%d</span></td></tr>",
        tbuf2, v.heartRate, v.spO2, v.temperature, v.respiratoryRate, v.perfusionIndex, r_c, v.healthScore);
      server.sendContent(rowBuf);
    }
    server.sendContent(F("</tbody></table>"));

    // ── Trend charts (server-side SVG, no JavaScript needed) ─────────────────
    if (filled >= 2) {
      server.sendContent(F("<div style='margin-top:12px'><p style='font-size:9px;font-weight:bold;"
        "color:#00b4d8;letter-spacing:2px;margin-bottom:6px'>TREND CHARTS</p>"));
      sendSVGChart("HEART RATE (bpm) — Normal 60-100",       hrArr, filled, "#e74c3c", 40,180, 60,100);
      sendSVGChart("SpO2 (%) — Normal 95-100",               o2Arr, filled, "#00b4d8", 80,100, 95,100);
      sendSVGChart("TEMPERATURE (°C) — Normal 36.1-37.3",    tpArr, filled, "#e67e22", 34, 41, 36.1f,37.3f);
      sendSVGChart("RESPIRATORY RATE (br/min) — Normal 12-20",rrArr,filled, "#2ecc71",  0, 40, 12, 20);
      sendSVGChart("HEALTH SCORE (0-100)",                   scArr, filled, "#9b59b6",  0,100, 60, 90);
      server.sendContent(F("</div>"));
    }
    server.sendContent(F("</div>"));
  } else {
    server.sendContent(F("<div class='sec'><h2>MEASUREMENT HISTORY</h2>"
      "<p style='color:#aaa;text-align:center;padding:20px;border:1px dashed #ddd;border-radius:8px'>"
      "No records yet. Complete a 90s measurement to build history.</p></div>"));
  }

  server.sendContent("<div class='ftr'>&#10084;&#65039; VitalScope Health Monitoring &nbsp;|&nbsp; "
    + String(SUPPORT_EMAIL) + " &nbsp;|&nbsp; " + String(SUPPORT_PHONE) + "</div>");
  server.sendContent(F("</body></html>"));
  server.sendContent("");
}

void handleRoot() {
  if (!isClientAllowed()) { server.send(403, "text/plain", "Access denied: connect to VitalScope-Health WiFi"); return; }
  server.sendHeader("Connection", "close", true);
  server.sendHeader("Cache-Control", "no-cache, no-store, must-revalidate");
  server.sendHeader("Pragma", "no-cache");
  server.sendHeader("Expires", "-1");
  server.setContentLength(CONTENT_LENGTH_UNKNOWN);
  server.send(200, "text/html", "");

  server.sendContent(F("<!DOCTYPE html><html lang='en'><head>"
    "<meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
    "<title>VitalScope v1.0</title><style>"
    "*{margin:0;padding:0;box-sizing:border-box}"
    "body{font-family:sans-serif;background:#06070d;color:#e0e0e0;min-height:100vh;overflow-x:hidden}"
    ":root{--p:#00d4ff;--a:#ff4757;--ok:#2ecc71;--w:#f39c12;--bg:#06070d;--card:rgba(255,255,255,0.04);--br:rgba(255,255,255,0.08)}"
    ".asc{display:none;position:fixed;inset:0;background:radial-gradient(ellipse at 30% 50%,#0d1117,#06070d);z-index:100;align-items:center;justify-content:center;padding:20px;overflow-y:auto}"
    ".asc.show{display:flex}"
    ".abox{background:rgba(255,255,255,0.03);border:1px solid rgba(0,212,255,0.2);border-radius:24px;padding:40px;width:100%;max-width:440px;backdrop-filter:blur(10px)}"
    ".alogo{text-align:center;margin-bottom:30px}"
    ".alogo h1{font-size:24px;color:var(--p);text-shadow:0 0 20px var(--p);letter-spacing:4px;font-weight:900}"
    ".alogo p{color:#888;font-size:13px;margin-top:4px;letter-spacing:2px}"
    ".abox h2{font-size:15px;color:#aaa;letter-spacing:3px;margin-bottom:18px;text-align:center;text-transform:uppercase}"
    ".fg{margin-bottom:13px;position:relative}"
    ".fg label{display:block;font-size:11px;letter-spacing:2px;color:#888;text-transform:uppercase;margin-bottom:5px}"
    ".fg input,.fg select{width:100%;padding:11px 14px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);border-radius:10px;color:#fff;font-size:14px;transition:border .3s}"
    ".fg input:focus,.fg select:focus{outline:none;border-color:var(--p)}"
    ".fg select option{background:#1a1a2e}"
    ".eye{position:absolute;right:12px;bottom:10px;background:none;border:none;cursor:pointer;color:#666;font-size:15px}"
    ".bp{width:100%;padding:13px;background:linear-gradient(135deg,#00b4d8,#0077b6);border:none;border-radius:10px;color:#fff;font-size:14px;letter-spacing:2px;cursor:pointer;margin:6px 0;transition:all .3s}"
    ".bp:hover{transform:translateY(-1px);filter:brightness(1.1)}"
    ".bp:disabled{opacity:0.5;cursor:not-allowed;transform:none}"
    ".bo{width:100%;padding:11px;background:transparent;border:1px solid rgba(255,255,255,0.12);border-radius:10px;color:#aaa;font-size:13px;cursor:pointer;margin:4px 0;transition:all .3s}"
    ".bo:hover{border-color:var(--p);color:var(--p)}"
    ".al{padding:12px 16px;border-radius:10px;font-size:13px;margin-bottom:12px;display:none}"
    ".al.show{display:block}"
    ".al-e{background:rgba(255,71,87,0.1);border:1px solid rgba(255,71,87,0.3);color:#ff6b6b}"
    ".al-s{background:rgba(46,204,113,0.1);border:1px solid rgba(46,204,113,0.3);color:#82e0aa}"
    ".al-i{background:rgba(0,212,255,0.1);border:1px solid rgba(0,212,255,0.3);color:#90e0ef}"
    ".lnk{text-align:center;margin-top:15px;font-size:13px;color:#888}"
    ".lnk a{color:var(--p);text-decoration:none;cursor:pointer;font-weight:600}"
    ".dash{display:none;min-height:100vh}"
    ".dash.show{display:block}"
    ".nav{background:rgba(6,7,13,0.97);border-bottom:1px solid var(--br);padding:13px 20px;display:flex;align-items:center;justify-content:space-between;position:sticky;top:0;z-index:50}"
    ".nlogo{font-size:17px;color:var(--p);text-shadow:0 0 10px var(--p);letter-spacing:3px;font-weight:900}"
    ".nuser{font-size:13px;color:#aaa;margin-right:8px}"
    ".hambtn{background:none;border:1px solid rgba(255,255,255,0.15);border-radius:8px;color:#ccc;cursor:pointer;font-size:20px;padding:6px 12px;line-height:1;transition:all .3s}"
    ".hambtn:hover{border-color:var(--p);color:var(--p)}"
    ".side-overlay{display:none;position:fixed;inset:0;background:rgba(0,0,0,0.6);z-index:200}"
    ".side-overlay.open{display:block}"
    ".side-panel{position:fixed;top:0;right:-300px;width:280px;height:100vh;background:#0d0f1a;border-left:1px solid rgba(0,212,255,0.15);z-index:201;transition:right .3s ease;padding:0;display:flex;flex-direction:column}"
    ".side-panel.open{right:0}"
    ".side-hdr{padding:20px;border-bottom:1px solid rgba(255,255,255,0.07);display:flex;align-items:center;justify-content:space-between}"
    ".side-hdr span{color:var(--p);font-size:15px;letter-spacing:2px;font-weight:700}"
    ".side-close{background:none;border:none;color:#888;cursor:pointer;font-size:20px}"
    ".side-close:hover{color:#ff4757}"
    ".side-body{flex:1;overflow-y:auto;padding:10px 0}"
    ".side-item{display:flex;align-items:center;gap:12px;padding:14px 20px;cursor:pointer;border-bottom:1px solid rgba(255,255,255,0.04);transition:all .2s;color:#ccc;font-size:14px}"
    ".side-item:hover{background:rgba(0,212,255,0.06);color:var(--p)}"
    ".side-item .ico{font-size:18px;width:24px;text-align:center}"
    ".side-item.danger{color:#ff6b6b}"
    ".side-item.danger:hover{background:rgba(255,71,87,0.08);color:#ff4757}"
    ".side-foot{padding:16px 20px;border-top:1px solid rgba(255,255,255,0.06);font-size:11px;color:#444}"
    ".mc{padding:20px;max-width:1100px;margin:0 auto}"
    ".vg{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:14px;margin:16px 0}"
    ".vc{background:var(--card);border:1px solid var(--br);border-radius:16px;padding:20px;cursor:pointer;transition:all .3s;position:relative;overflow:hidden}"
    ".vc:hover{transform:translateY(-3px);box-shadow:0 8px 30px rgba(0,0,0,0.3)}"
    ".vc.hr:hover{border-color:rgba(255,71,87,0.5)}"
    ".vc.sp:hover{border-color:rgba(0,180,216,0.5)}"
    ".vc.tp:hover{border-color:rgba(255,99,72,0.5)}"
    ".vc.rp:hover{border-color:rgba(46,204,113,0.5)}"
    ".vc.pi:hover{border-color:rgba(162,155,254,0.5)}"
    ".vi{font-size:26px;margin-bottom:8px}"
    ".vl2{font-size:10px;letter-spacing:3px;color:#666;text-transform:uppercase}"
    ".vv2{font-size:38px;font-weight:700;line-height:1;margin:6px 0}"
    ".vu{font-size:12px;color:#888;letter-spacing:1px}"
    ".vs{font-size:11px;margin-top:8px;padding:4px 10px;border-radius:20px;display:inline-block;letter-spacing:1px}"
    ".vtap{position:absolute;bottom:8px;right:12px;font-size:10px;color:#444;letter-spacing:1px}"
    ".sc{background:var(--card);border:1px solid var(--br);border-radius:20px;padding:28px;margin:16px 0;display:flex;align-items:center;gap:28px;flex-wrap:wrap}"
    ".scc{position:relative;width:140px;height:140px;flex-shrink:0}"
    ".ssvg{transform:rotate(-90deg);width:100%;height:100%}"
    ".sbg{fill:none;stroke:rgba(255,255,255,0.05);stroke-width:10}"
    ".sarc{fill:none;stroke:var(--p);stroke-width:10;stroke-linecap:round;stroke-dasharray:408;stroke-dashoffset:408;transition:stroke-dashoffset 1.2s ease}"
    ".snum{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);text-align:center}"
    ".sval{font-size:36px;font-weight:900;color:var(--p)}"
    ".si{flex:1;min-width:200px}"
    ".sbs{display:flex;flex-direction:column;gap:6px;margin-top:10px}"
    ".sb{display:flex;align-items:center;gap:10px;font-size:12px}"
    ".sbl{width:50px;color:#888;letter-spacing:1px}"
    ".sbt{flex:1;height:5px;background:rgba(255,255,255,0.07);border-radius:3px;overflow:hidden}"
    ".sbf{height:100%;border-radius:3px;transition:width 1.2s ease}"
    ".fb{background:rgba(255,193,7,0.06);border:1px solid rgba(255,193,7,0.2);border-radius:12px;padding:12px 18px;display:flex;align-items:center;gap:12px;margin-bottom:16px;transition:all .3s}"
    ".fd{width:10px;height:10px;border-radius:50%;background:#ffc107;animation:bl 1.5s ease-in-out infinite;flex-shrink:0}"
    ".fd.ok{background:#2ecc71;animation:none}"
    "@keyframes bl{0%,100%{opacity:1}50%{opacity:0.2}}"
    ".ft{font-size:13px;color:#ffc107}"
    ".ft.ok{color:#82e0aa}"
    ".busy-banner{background:rgba(255,71,87,0.08);border:1px solid rgba(255,71,87,0.3);border-radius:12px;padding:14px 18px;margin-bottom:14px;display:none;text-align:center}"
    ".busy-banner.show{display:block}"
    ".busy-txt{color:#ff6b6b;font-size:14px;font-weight:600}"
    ".busy-sub{color:#888;font-size:12px;margin-top:4px}"
    ".mp{background:var(--card);border:1px solid rgba(0,212,255,0.2);border-radius:14px;padding:20px;margin:14px 0;display:none}"
    ".mp.show{display:block}"
    ".mpb{height:8px;background:rgba(255,255,255,0.05);border-radius:4px;overflow:hidden;margin:12px 0}"
    ".mpf{height:100%;background:linear-gradient(90deg,#00b4d8,#0077b6);border-radius:4px;transition:width 1s linear}"
    ".mlive{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-top:12px}"
    ".ml{text-align:center;background:rgba(255,255,255,0.03);border-radius:8px;padding:10px}"
    ".mll{font-size:10px;color:#666;letter-spacing:1px;text-transform:uppercase}"
    ".mlv{font-size:20px;font-weight:bold;color:var(--p);margin-top:3px}"
    ".measarea{text-align:center;margin:20px 0 10px}"
    ".measbig{background:linear-gradient(135deg,rgba(0,180,216,0.15),rgba(0,100,180,0.15));border:2px solid rgba(0,212,255,0.4);color:#00d4ff;padding:16px 36px;border-radius:14px;font-size:16px;letter-spacing:3px;cursor:pointer;transition:all .3s;display:inline-flex;align-items:center;gap:10px}"
    ".measbig:hover{background:linear-gradient(135deg,rgba(0,180,216,0.3),rgba(0,100,180,0.3));transform:translateY(-2px);box-shadow:0 8px 25px rgba(0,212,255,0.2)}"
    ".measbig:disabled{opacity:0.5;cursor:not-allowed;transform:none}"
    ".savebtn{background:rgba(46,204,113,0.12);border:1px solid rgba(46,204,113,0.3);color:#2ecc71;padding:12px 24px;border-radius:10px;cursor:pointer;font-size:14px;letter-spacing:2px;margin:8px;transition:all .3s}"
    ".savebtn:hover{background:rgba(46,204,113,0.25);transform:translateY(-1px)}"
    ".pn{background:var(--card);border:1px solid var(--br);border-radius:16px;padding:22px;margin:14px 0}"
    ".pn h3{font-size:12px;letter-spacing:3px;color:#888;margin-bottom:18px;text-transform:uppercase}"
    ".dt{width:100%;border-collapse:collapse;font-size:13px}"
    ".dt th{text-align:left;padding:10px 14px;font-size:10px;letter-spacing:2px;color:#666;text-transform:uppercase;border-bottom:1px solid var(--br)}"
    ".dt td{padding:11px 14px;border-bottom:1px solid rgba(255,255,255,0.04)}"
    ".badge{padding:3px 10px;border-radius:20px;font-size:11px;background:rgba(0,212,255,0.08);color:#90e0ef;border:1px solid rgba(0,212,255,0.15)}"
    ".db{background:rgba(255,71,87,0.08);border:1px solid rgba(255,71,87,0.2);color:#ff6b6b;padding:5px 12px;border-radius:6px;cursor:pointer;font-size:12px;transition:all .3s}"
    ".db:hover{background:rgba(255,71,87,0.2)}"
    ".vb{background:rgba(0,212,255,0.08);border:1px solid rgba(0,212,255,0.2);color:#90e0ef;padding:5px 12px;border-radius:6px;cursor:pointer;font-size:12px;margin-right:4px;transition:all .3s}"
    ".vb:hover{background:rgba(0,212,255,0.2)}"
    ".pdfb{background:rgba(46,204,113,0.08);border:1px solid rgba(46,204,113,0.2);color:#82e0aa;padding:5px 10px;border-radius:6px;cursor:pointer;font-size:11px;margin-right:2px;transition:all .3s}"
    ".pdfb:hover{background:rgba(46,204,113,0.2)}"
    ".rpb{background:rgba(162,155,254,0.08);border:1px solid rgba(162,155,254,0.2);color:#a29bfe;padding:5px 10px;border-radius:6px;cursor:pointer;font-size:11px;margin-right:2px;transition:all .3s}"
    ".rpb:hover{background:rgba(162,155,254,0.2)}"
    ".modal{display:none;position:fixed;inset:0;background:rgba(0,0,0,0.85);z-index:300;align-items:center;justify-content:center;padding:20px}"
    ".modal.show{display:flex}"
    ".mbox{background:#0d0f1a;border:1px solid rgba(0,212,255,0.15);border-radius:20px;padding:28px;width:100%;max-width:700px;max-height:90vh;overflow-y:auto}"
    ".mbox h2{font-size:15px;color:var(--p);letter-spacing:3px;margin-bottom:18px;text-transform:uppercase}"
    ".mc2{float:right;background:rgba(255,71,87,0.12);border:1px solid rgba(255,71,87,0.3);color:#ff6b6b;padding:5px 12px;border-radius:6px;cursor:pointer;font-size:12px}"
    ".toast{position:fixed;bottom:20px;right:20px;background:#0d0f1a;border:1px solid rgba(0,212,255,0.3);border-radius:12px;padding:14px 20px;color:#fff;font-size:14px;z-index:999;opacity:0;transform:translateY(20px);transition:all .3s;max-width:320px;pointer-events:none}"
    ".toast.show{opacity:1;transform:translateY(0)}"
    ".toast.err{border-color:rgba(255,71,87,0.4)}"
    ".toast.ok{border-color:rgba(46,204,113,0.4)}"
    "@media(max-width:600px){.vg{grid-template-columns:repeat(2,1fr)}.sc{flex-direction:column;text-align:center}.nav{padding:10px 14px}.mlive{grid-template-columns:repeat(2,1fr)}}"
    "</style></head><body>"
  ));

  server.sendContent(F("<div class='toast' id='toast'></div>\n"));

  // AUTH SCREENS
  server.sendContent(F(
    "<div class='asc show' id='sSignIn'><div class='abox'>"
    "<div class='alogo'><h1>VITALSCOPE</h1><p>HEALTH MONITORING v1.0</p></div>"
    "<h2>SIGN IN</h2>"
    "<div class='al al-e' id='siErr'></div>"
    "<div class='fg'><label>Username</label><input id='siU' type='text' placeholder='Enter username' autocomplete='username'></div>"
    "<div class='fg'><label>Password</label><input id='siP' type='password' placeholder='Enter password'>"
    "<button type='button' class='eye' onclick='togglePwd(\"siP\",this)'>&#x1F441;</button></div>"
    "<button class='bp' id='siBt' onclick='doSignIn()'>SIGN IN</button>"
    "<button class='bo' onclick='showScr(\"sSignUp\")'>CREATE ACCOUNT</button>"
    "<div class='lnk'><a onclick='showScr(\"sForgot\")'>Forgot password?</a></div>"
    "</div></div>"
  ));

  server.sendContent(F(
    "<div class='asc' id='sSignUp'><div class='abox' style='max-height:95vh;overflow-y:auto;margin:auto'>"
    "<div class='alogo'><h1>VITALSCOPE</h1></div><h2>CREATE ACCOUNT</h2>"
    "<div class='al al-e' id='suErr'></div><div class='al al-s' id='suOk'></div>"
    "<div id='suForm'>"
    "<div class='fg'><label>Full Name *</label><input id='suName' type='text'></div>"
    "<div class='fg'><label>Username * (no spaces)</label><input id='suUser' type='text'></div>"
    "<div class='fg'><label>Email *</label><input id='suEmail' type='email'></div>"
    "<div class='fg'><label>Phone * (10 digits)</label><input id='suPhone' type='tel' maxlength='10'></div>"
    "<div class='fg'><label>Password * (min 6)</label><input id='suPass' type='password'>"
    "<button type='button' class='eye' onclick='togglePwd(\"suPass\",this)'>&#x1F441;</button></div>"
    "<div class='fg'><label>Age *</label><input id='suAge' type='number' min='1' max='120'></div>"
    "<div class='fg'><label>Gender *</label><select id='suGender'><option value=''>Select</option>"
    "<option>Male</option><option>Female</option><option>Other</option></select></div>"
    "<div class='fg'><label>Height (cm)</label><input id='suHt' type='number' step='0.1'></div>"
    "<div class='fg'><label>Weight (kg)</label><input id='suWt' type='number' step='0.1'></div>"
    "<div class='fg'><label>Medical Conditions</label><input id='suDis' type='text' placeholder='None'></div>"
    "<button class='bp' id='suBt' onclick='doSendOTP()'>SEND VERIFICATION CODE</button>"
    "<button class='bo' onclick='showScr(\"sSignIn\")'>BACK TO SIGN IN</button>"
    "</div>"
    "<div id='otpSec' style='display:none'>"
    "<div class='al al-i show'>&#128274; Check <strong>OLED display</strong> for your 6-digit code.</div>"
    "<div class='fg' style='margin-top:15px'><label>6-Digit Code</label>"
    "<input id='otpIn' type='text' inputmode='numeric' maxlength='6' placeholder='000000' style='letter-spacing:8px;font-size:24px;text-align:center'></div>"
    "<button class='bp' onclick='doVerOTP()'>VERIFY AND CREATE ACCOUNT</button>"
    "<button class='bo' id='resendBtn' onclick='resendOTP()'>RESEND CODE</button>"
    "<button class='bo' onclick='document.getElementById(\"otpSec\").style.display=\"none\";document.getElementById(\"suForm\").style.display=\"block\"'>BACK TO FORM</button>"
    "</div></div></div>"
  ));

  server.sendContent(F(
    "<div class='asc' id='sForgot'><div class='abox'>"
    "<div class='alogo'><h1>VITALSCOPE</h1></div><h2>RESET PASSWORD</h2>"
    "<div class='al al-e' id='fpErr'></div><div class='al al-s' id='fpOk'></div>"
    "<div id='fpStep1'>"
    "<div class='fg'><label>Registered Email</label><input id='fpEmail' type='email'></div>"
    "<button class='bp' onclick='doSendReset()'>SEND RESET CODE</button>"
    "<button class='bo' onclick='showScr(\"sSignIn\")'>BACK TO SIGN IN</button>"
    "</div>"
    "<div id='fpStep2' style='display:none'>"
    "<div class='al al-i show'>&#128274; Reset code sent! Check OLED display.</div>"
    "<div class='fg' style='margin-top:12px'><label>6-Digit Code</label>"
    "<input id='fpOTP' type='text' inputmode='numeric' maxlength='6' placeholder='000000' style='letter-spacing:8px;font-size:22px;text-align:center'></div>"
    "<div class='fg'><label>New Password</label><input id='fpPw' type='password'>"
    "<button type='button' class='eye' onclick='togglePwd(\"fpPw\",this)'>&#x1F441;</button></div>"
    "<button class='bp' onclick='doResetPw()'>RESET PASSWORD</button>"
    "<button class='bo' onclick='resendResetOTP()'>RESEND CODE</button>"
    "</div></div></div>"
  ));

  // SIDE PANEL + DASHBOARD STRUCTURE
  server.sendContent(F(
    "<div class='side-overlay' id='sideOverlay' onclick='closeSide()'></div>"
    "<div class='side-panel' id='sidePanel'>"
    "<div class='side-hdr'><span>MENU</span>"
    "<button class='side-close' onclick='closeSide()'>&#x2715;</button></div>"
    "<div class='side-body'>"
    "<div class='side-item userOnly' onclick='closeSide();showHist()'><span class='ico'>&#128202;</span>Health History</div>"
    "<div class='side-item userOnly' onclick='closeSide();showProfile()'><span class='ico'>&#128100;</span>My Profile</div>"
    "<div class='side-item userOnly' onclick='closeSide();doReport()'><span class='ico'>&#128203;</span>Generate Report</div>"
    "<div class='side-item danger' onclick='closeSide();doLogout()'><span class='ico'>&#128274;</span>Sign Out</div>"
    "</div>"
    "<div class='side-foot'>VitalScope v1.0</div>"
    "</div>"
    "<div class='dash' id='dashboard'>"
    "<nav class='nav'>"
    "<div class='nlogo'>&#10084; VITALSCOPE</div>"
    "<div style='display:flex;align-items:center;gap:10px'>"
    "<span class='nuser' id='navU'></span>"
    "<button class='hambtn' onclick='openSide()'>&#9776;</button>"
    "</div></nav>"
    "<div class='mc'>"
    "<div id='userP' style='display:none'>"
    "<div class='fb' id='fBanner'><div class='fd' id='fDot'></div><div class='ft' id='fTxt'>Place finger on MAX30102 sensor</div></div>"
    "<div class='busy-banner' id='busyBanner'>"
    "<div class='busy-txt'>&#9888; DEVICE BUSY</div>"
    "<div class='busy-sub' id='busySub'>Another user is measuring. Please wait...</div>"
    "</div>"
    "<div class='sc'><div class='scc'>"
    "<svg class='ssvg' viewBox='0 0 140 140'>"
    "<circle class='sbg' cx='70' cy='70' r='65'/>"
    "<circle class='sarc' id='scArc' cx='70' cy='70' r='65'/></svg>"
    "<div class='snum'><div class='sval' id='scVal'>--</div>"
    "<div style='font-size:11px;color:#666;letter-spacing:2px'>SCORE</div></div></div>"
    "<div class='si'>"
    "<div style='font-size:12px;color:#aaa;letter-spacing:3px;margin-bottom:6px'>HEALTH STATUS</div>"
    "<div style='font-size:17px;font-weight:600;margin-bottom:8px' id='scSt'>Press START MEASURE below</div>"
    "<div class='sbs' id='scBars'></div></div></div>"
    "<div class='vg'>"
    // HR card
    "<div class='vc hr' onclick='openVital(\"hr\")'>"
    "<div class='vi'>&#x2764;</div><div class='vl2'>HEART RATE</div>"
    "<div class='vv2' id='vcHR' style='color:#ff4757'>--</div><div class='vu'>BPM</div>"
    "<div class='vs' id='vcHRS' style='background:rgba(255,71,87,0.08);color:#666'>PRESS START MEASURE</div>"
    "<span class='vtap'>TAP &#8599;</span></div>"
    // SpO2 card
    "<div class='vc sp' onclick='openVital(\"spo2\")'>"
    "<div class='vi'>&#x1F4A7;</div><div class='vl2'>OXYGEN SAT.</div>"
    "<div class='vv2' id='vcO2' style='color:#00b4d8'>--</div><div class='vu'>SpO2 %</div>"
    "<div class='vs' id='vcO2S' style='background:rgba(0,180,216,0.08);color:#666'>PRESS START MEASURE</div>"
    "<span class='vtap'>TAP &#8599;</span></div>"
    // Temp card
    "<div class='vc tp' onclick='openVital(\"temp\")'>"
    "<div class='vi'>&#x1F321;</div><div class='vl2'>TEMPERATURE</div>"
    "<div class='vv2' id='vcTp' style='color:#ff6348'>--</div><div class='vu'>CELSIUS</div>"
    "<div class='vs' id='vcTpS' style='background:rgba(255,99,72,0.08);color:#666'>PRESS START MEASURE</div>"
    "<span class='vtap'>TAP &#8599;</span></div>"
    // Resp card
    "<div class='vc rp' onclick='openVital(\"resp\")'>"
    "<div class='vi'>&#x1FAC1;</div><div class='vl2'>RESPIRATORY</div>"
    "<div class='vv2' id='vcRR' style='color:#2ecc71'>--</div><div class='vu'>BR/MIN</div>"
    "<div class='vs' id='vcRRS' style='background:rgba(46,204,113,0.08);color:#666'>PRESS START MEASURE</div>"
    "<span class='vtap'>TAP &#8599;</span></div>"
    // Perfusion Index card (NEW)
    "<div class='vc pi' onclick='openVital(\"spo2\")'>"
    "<div class='vi'>&#128266;</div><div class='vl2'>PERFUSION INDEX</div>"
    "<div class='vv2' id='vcPI' style='color:#a29bfe'>--</div><div class='vu'>PI %</div>"
    "<div class='vs' id='vcPIS' style='background:rgba(162,155,254,0.08);color:#666'>PRESS START MEASURE</div>"
    "<span class='vtap'>TAP &#8599;</span></div>"
    "</div>"
    "<div class='mp' id='measProg'>"
    "<div style='display:flex;justify-content:space-between;align-items:center'>"
    "<div style='font-size:13px;color:#00d4ff;letter-spacing:2px'>MEASURING — KEEP FINGER STEADY</div>"
    "<div style='font-size:24px;font-weight:900;color:#00d4ff' id='mSec'>90</div>"
    "</div>"
    "<div class='mpb'><div class='mpf' id='mpfill' style='width:0%'></div></div>"
    "<div style='font-size:12px;color:#888;margin-bottom:10px'>Averaging over 90 seconds. Keep still.</div>"
    "<div class='mlive'>"
    "<div class='ml'><div class='mll'>HR (live)</div><div class='mlv' id='mlHR'>--</div></div>"
    "<div class='ml'><div class='mll'>SpO2</div><div class='mlv' id='mlO2'>warming...</div></div>"
    "<div class='ml'><div class='mll'>Temp</div><div class='mlv' id='mlTp'>--</div></div>"
    "<div class='ml'><div class='mll'>RR</div><div class='mlv' id='mlRR'>--</div></div>"
    "</div></div>"
    "<div class='measarea'>"
    "<button class='measbig' id='measBtn' onclick='doMeasure()'>&#9654; START 90-SECOND MEASURE</button>"
    "</div>"
    "<div style='font-size:12px;color:#555;text-align:center;margin-bottom:20px;padding:8px;background:rgba(255,255,255,0.02);border-radius:8px'>"
    "&#9432; Records auto-save after each 90s measurement. Cards update only after measurement completes. Each session is isolated.</div>"
    "</div>"
    "<div id='adminP' style='display:none'>"
    "<div class='pn'><h3>SYSTEM OVERVIEW</h3>"
    "<div style='display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin-bottom:20px'>"
    "<div style='background:rgba(0,212,255,0.05);border:1px solid rgba(0,212,255,0.12);border-radius:12px;padding:18px;text-align:center'>"
    "<div style='font-size:11px;color:#666;letter-spacing:2px'>TOTAL USERS</div>"
    "<div style='font-size:36px;color:#00d4ff;margin-top:5px;font-weight:900' id='aTU'>-</div></div>"
    "<div style='background:rgba(46,204,113,0.05);border:1px solid rgba(46,204,113,0.12);border-radius:12px;padding:18px;text-align:center'>"
    "<div style='font-size:11px;color:#666;letter-spacing:2px'>ACTIVE SESSIONS</div>"
    "<div style='font-size:36px;color:#2ecc71;margin-top:5px;font-weight:900' id='aAS'>-</div>"
    "<div style='font-size:10px;color:#888;margin-top:4px' id='aAU'>—</div></div>"
    "<div style='background:rgba(123,94,167,0.05);border:1px solid rgba(123,94,167,0.12);border-radius:12px;padding:18px;text-align:center'>"
    "<div style='font-size:11px;color:#666;letter-spacing:2px'>DEVICE UPTIME</div>"
    "<div style='font-size:22px;color:#a29bfe;margin-top:5px;font-weight:bold' id='aUT'>-</div></div>"
    "</div>"
    // Time sync panel
    "<div style='background:rgba(255,165,0,0.04);border:1px solid rgba(255,165,0,0.18);border-radius:12px;padding:16px;margin-bottom:20px'>"
    "<div style='font-size:11px;color:#ffad00;letter-spacing:2px;margin-bottom:10px'>&#128336; DEVICE TIME SYNC</div>"
    "<div style='font-size:13px;color:#aaa;margin-bottom:10px' id='curTimeDisp'>Device time: loading...</div>"
    "<div style='display:flex;gap:10px;flex-wrap:wrap;align-items:center'>"
    "<button onclick='setDeviceTime()' style='background:linear-gradient(135deg,rgba(255,165,0,0.25),rgba(255,165,0,0.15));border:1px solid rgba(255,165,0,0.4);color:#ffad00;padding:10px 20px;border-radius:8px;cursor:pointer;font-size:13px;letter-spacing:1px'>&#128336; SYNC FROM MY BROWSER CLOCK</button>"
    "<span style='font-size:11px;color:#666'>Syncs ESP32 clock to your phone/laptop time. Works without internet.</span>"
    "</div></div>"
    "<h3>REGISTERED USERS</h3>"
    "<div style='overflow-x:auto'><table class='dt'><thead><tr>"
    "<th>NAME</th><th>USERNAME</th><th>EMAIL</th><th>AGE/GENDER</th><th>RECORDS</th><th>ACTIONS</th>"
    "</tr></thead><tbody id='uBody'></tbody></table></div></div></div>"
    "</div></div>"
  ));

  // MODALS
  server.sendContent(F(
    "<div class='modal' id='mHist'><div class='mbox'>"
    "<button class='mc2' onclick='closeM(\"mHist\")'>&#x2715; CLOSE</button>"
    "<h2>&#128202; HEALTH HISTORY</h2><div id='histC'>Loading...</div></div></div>"
    "<div class='modal' id='mReport'><div class='mbox'>"
    "<button class='mc2' onclick='closeM(\"mReport\")'>&#x2715; CLOSE</button>"
    "<h2>&#128203; HEALTH REPORT</h2><div id='repC'>Loading...</div>"
    "<div style='margin-top:15px;text-align:center'>"
    "<button id='dlBtn' onclick='dlReport()' style='background:linear-gradient(135deg,#00b4d8,#0077b6);border:none;color:#fff;padding:14px 32px;border-radius:10px;cursor:pointer;font-size:15px;letter-spacing:2px;width:100%;max-width:380px'>&#128247; DOWNLOAD / PRINT REPORT</button>"
    "<div style='font-size:11px;color:#666;margin-top:8px;padding:6px 10px;background:rgba(0,212,255,0.04);border-radius:6px'>"
    "&#128161; Mobile: saves as HTML file &nbsp;|&nbsp; Laptop/Desktop: opens print view (Save as PDF)"
    "</div>"
    "</div>"
    "</div></div>"
    "<div class='modal' id='mProf'><div class='mbox'>"
    "<button class='mc2' onclick='closeM(\"mProf\")'>&#x2715; CLOSE</button>"
    "<h2>&#128100; MY PROFILE</h2><div id='profC'>Loading...</div></div></div>"
    "<div class='modal' id='mAdmU'><div class='mbox'>"
    "<button class='mc2' onclick='closeM(\"mAdmU\")'>&#x2715; CLOSE</button>"
    "<h2 id='admUT'>USER DATA</h2><div id='admUC'>Loading...</div></div></div>"
  ));

  // JAVASCRIPT
  server.sendContent(F("<script>\n"
    "const SS=sessionStorage;\n"
    "let tok=SS.getItem('vsTok')||'';\n"
    "let isAdm=SS.getItem('vsAdm')==='1';\n"
    "let rtTimer=null;\n"
    "let lastRep=null;\n"
    "let suData=null;\n"
    "let measTimer=null;\n"
    "let measElapsed=0;\n"
    "let lastAdmViewUser='';\n"
    "\n"
    "function openSide(){document.getElementById('sideOverlay').classList.add('open');document.getElementById('sidePanel').classList.add('open');}\n"
    "function closeSide(){document.getElementById('sideOverlay').classList.remove('open');document.getElementById('sidePanel').classList.remove('open');}\n"
    "\n"
    "function toast(msg,type){"
    "type=type||'ok';"
    "var t=document.getElementById('toast');"
    "t.textContent=msg;t.className='toast '+type+' show';"
    "setTimeout(function(){t.classList.remove('show');},5000);}\n"
    "\n"
    "function togglePwd(id,btn){"
    "var e=document.getElementById(id);e.type=e.type==='password'?'text':'password';"
    "btn.textContent=e.type==='password'?'\\uD83D\\uDC41':'\\u{1F648}';}\n"
    "function showScr(id){"
    "document.querySelectorAll('.asc').forEach(function(s){s.classList.remove('show');});"
    "var s=document.getElementById(id);if(s)s.classList.add('show');}\n"
    "function showAl(id,msg,type){"
    "type=type||'e';"
    "var e=document.getElementById(id);if(!e)return;"
    "e.textContent=msg;e.className='al al-'+type+' show';"
    "setTimeout(function(){e.classList.remove('show');},10000);}\n"
    "function closeM(id){document.getElementById(id).classList.remove('show');}\n"
    "\n"
    "function showDash(name,admin){"
    "document.querySelectorAll('.asc').forEach(function(s){s.classList.remove('show');});"
    "document.getElementById('dashboard').classList.add('show');"
    "document.getElementById('navU').textContent=admin?'ADMIN':name;"
    "document.querySelectorAll('.userOnly').forEach(function(el){el.style.display=admin?'none':'flex';});"
    "if(admin){"
    "document.getElementById('adminP').style.display='block';"
    "document.getElementById('userP').style.display='none';"
    "loadAdmin();"
    "}else{"
    "document.getElementById('userP').style.display='block';"
    "document.getElementById('adminP').style.display='none';"
    "startRT();}}\n"
    "\n"
    "async function doSignIn(){"
    "var u=document.getElementById('siU').value.trim();"
    "var p=document.getElementById('siP').value;"
    "if(!u||!p){showAl('siErr','Please fill all fields');return;}"
    "var btn=document.getElementById('siBt');btn.disabled=true;btn.textContent='SIGNING IN...';"
    "try{var r=await fetch('/signin',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({username:u,password:p})});"
    "var d=await r.json();"
    "if(d.success){"
    "tok=d.token;isAdm=d.isAdmin||false;"
    "SS.setItem('vsTok',tok);SS.setItem('vsAdm',isAdm?'1':'0');SS.setItem('vsNm',d.name);"
    "showDash(d.name,isAdm);"
    "}else showAl('siErr',d.message||'Invalid credentials');"
    "}catch(e){showAl('siErr','Connection error. Try again.');}"
    "btn.disabled=false;btn.textContent='SIGN IN';}\n"
    "\n"
    "async function doSendOTP(){"
    "var name=document.getElementById('suName').value.trim();"
    "var user=document.getElementById('suUser').value.trim().toLowerCase();"
    "var email=document.getElementById('suEmail').value.trim();"
    "var phone=document.getElementById('suPhone').value.trim();"
    "var pass=document.getElementById('suPass').value;"
    "var age=parseInt(document.getElementById('suAge').value)||0;"
    "var gender=document.getElementById('suGender').value;"
    "if(!name||!user||!email||!phone||!pass||!age||!gender){showAl('suErr','Fill all required fields');return;}"
    "if(pass.length<6){showAl('suErr','Password min 6 chars');return;}"
    "if(!/^[0-9]{10}$/.test(phone)){showAl('suErr','Phone must be 10 digits');return;}"
    "if(user==='admin'){showAl('suErr','Reserved username');return;}"
    "suData={name:name,username:user,email:email,phone:phone,password:pass,age:age,gender:gender,"
    "height:parseFloat(document.getElementById('suHt').value)||0,"
    "weight:parseFloat(document.getElementById('suWt').value)||0,"
    "diseases:document.getElementById('suDis').value||'None'};"
    "var btn=document.getElementById('suBt');btn.disabled=true;btn.textContent='SENDING...';"
    "try{"
    "var r=await fetch('/send-otp',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:email})});"
    "var d=await r.json();"
    "if(d.success){"
    "document.getElementById('suForm').style.display='none';"
    "document.getElementById('otpSec').style.display='block';"
    "document.getElementById('otpIn').focus();"
    "}else showAl('suErr',d.message||'Failed to send code');"
    "}catch(e){showAl('suErr','Connection error');}"
    "btn.disabled=false;btn.textContent='SEND VERIFICATION CODE';}\n"
    "\n"
    "async function resendOTP(){"
    "if(!suData){toast('Session expired. Fill form again.','err');return;}"
    "var btn=document.getElementById('resendBtn');btn.disabled=true;"
    "try{var r=await fetch('/send-otp',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:suData.email})});"
    "var d=await r.json();"
    "if(d.success)showAl('suOk','New code sent! Check OLED.','s');"
    "else showAl('suErr',d.message||'Failed');"
    "}catch(e){showAl('suErr','Error');}"
    "btn.disabled=false;btn.textContent='RESEND CODE';}\n"
    "\n"
    "async function doVerOTP(){"
    "var otp=document.getElementById('otpIn').value.trim();"
    "if(otp.length!==6){toast('Enter 6-digit code','err');return;}"
    "if(!suData){toast('Session expired','err');return;}"
    "try{"
    "var r=await fetch('/verify-otp',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:suData.email,otp:otp})});"
    "var d=await r.json();"
    "if(d.success){"
    "var r2=await fetch('/signup',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify(suData)});var d2=await r2.json();"
    "if(d2.success){showAl('suOk','Account created! Please sign in.','s');"
    "setTimeout(function(){showScr('sSignIn');},2000);"
    "}else showAl('suErr',d2.message||'Failed');"
    "}else toast('Invalid or expired code','err');"
    "}catch(e){toast('Error: '+e.message,'err');}}\n"
    "\n"
    "async function doSendReset(){"
    "var email=document.getElementById('fpEmail').value.trim();"
    "if(!email){showAl('fpErr','Enter your email');return;}"
    "try{var r=await fetch('/forgot-password',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:email})});var d=await r.json();"
    "if(d.success){document.getElementById('fpStep1').style.display='none';"
    "document.getElementById('fpStep2').style.display='block';"
    "}else showAl('fpErr',d.message||'Email not found');"
    "}catch(e){showAl('fpErr','Connection error');}}\n"
    "\n"
    "async function resendResetOTP(){"
    "var email=document.getElementById('fpEmail').value.trim();"
    "if(!email){toast('Enter email first','err');return;}"
    "try{var r=await fetch('/forgot-password',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:email})});var d=await r.json();"
    "if(d.success)showAl('fpOk','New code sent!','s');else toast(d.message||'Failed','err');"
    "}catch(e){toast('Error','err');}}\n"
    "\n"
    "async function doResetPw(){"
    "var email=document.getElementById('fpEmail').value.trim();"
    "var otp=document.getElementById('fpOTP').value.trim();"
    "var np=document.getElementById('fpPw').value;"
    "if(otp.length!==6||np.length<6){toast('Check inputs','err');return;}"
    "try{var r=await fetch('/reset-password',{method:'POST',headers:{'Content-Type':'application/json'},"
    "body:JSON.stringify({email:email,otp:otp,password:np})});var d=await r.json();"
    "if(d.success){toast('Password reset! Sign in.','ok');showScr('sSignIn');}"
    "else toast(d.message||'Reset failed','err');"
    "}catch(e){toast('Error','err');}}\n"
    "\n"
    "async function doLogout(){"
    "clearInterval(rtTimer);clearInterval(measTimer);"
    "if(tok)try{await fetch('/logout',{method:'POST',headers:{Authorization:tok}});}catch(e){}"
    "tok='';isAdm=false;"
    "SS.removeItem('vsTok');SS.removeItem('vsAdm');SS.removeItem('vsNm');"
    "document.getElementById('dashboard').classList.remove('show');"
    "document.getElementById('siU').value='';document.getElementById('siP').value='';"
    "showScr('sSignIn');}\n"
    "\n"
  ));

  server.sendContent(F(
    "async function doMeasure(){"
    "var btn=document.getElementById('measBtn');"
    "btn.disabled=true;btn.textContent='STARTING...';"
    "try{"
    "var r=await fetch('/measure',{method:'POST',headers:{Authorization:tok}});"
    "var d=await r.json();"
    "if(!d.success){"
    "btn.disabled=false;btn.textContent='\\u25b6 START 90-SECOND MEASURE';"
    "if(d.busy){"
    "var bb=document.getElementById('busyBanner');"
    "document.getElementById('busySub').textContent='Device busy (\u2248'+d.remaining+'s left). Wait for current measurement to finish.';"
    "bb.classList.add('show');"
    "setTimeout(function(){bb.classList.remove('show');},8000);"
    "toast('Device is busy. Please wait '+d.remaining+'s.','err');"
    "}else toast('Start failed','err');"
    "return;}"
    "}catch(e){btn.disabled=false;btn.textContent='\\u25b6 START 90-SECOND MEASURE';return;}"
    "document.getElementById('busyBanner').classList.remove('show');"
    "document.getElementById('measProg').classList.add('show');"
    "btn.textContent='MEASURING...';"
    "measElapsed=0;"
    "clearInterval(measTimer);"
    "measTimer=setInterval(async function(){"
    "measElapsed++;"
    "var pct=Math.round((measElapsed/90)*100);"
    "document.getElementById('mpfill').style.width=Math.min(pct,100)+'%';"
    "document.getElementById('mSec').textContent=Math.max(0,90-measElapsed);"
    "try{"
    "var rs=await fetch('/measure-status?token='+encodeURIComponent(tok));"
    "var ds=await rs.json();"
    "document.getElementById('mlHR').textContent=ds.liveHR>0?ds.liveHR:'--';"
    "document.getElementById('mlO2').textContent=ds.liveO2>0?ds.liveO2.toFixed(1)+'%':'reading...';"
    "document.getElementById('mlTp').textContent=ds.liveTmp>0?ds.liveTmp.toFixed(1)+'\u00b0C':'--';"
    "document.getElementById('mlRR').textContent=ds.liveRR>0?ds.liveRR:'--';"
    "if(measElapsed>=90||ds.done){"
    "clearInterval(measTimer);"
    "document.getElementById('measProg').classList.remove('show');"
    "btn.disabled=false;btn.textContent='\\u25b6 START 90-SECOND MEASURE';"
    "if(ds.ready){"
    "if(!ds.autoSaved){"
    "try{await fetch('/save-record',{method:'POST',headers:{Authorization:tok}});}catch(e){}"
    "}"
    "var summ='Done! HR:'+Math.round(ds.avgHR)+' SpO2:'+(ds.avgSpO2>0?ds.avgSpO2.toFixed(1):'--')+'% Temp:'+(ds.avgTemp>0?ds.avgTemp.toFixed(1):'--')+'C'+(ds.autoSaved?' [SAVED]':'');"
    "toast(summ,'ok');"
    "}else{"
    "toast('Measurement complete. Keep finger for SpO2.','ok');}"
    "}}"
    "catch(e){}"
    "},1000);}\n"
    "\n"
    "async function doSaveRecord(){"
    "try{"
    "var r=await fetch('/save-record',{method:'POST',headers:{Authorization:tok}});"
    "var d=await r.json();"
    "toast(d.message||(d.success?'Record saved!':'Save failed'),d.success?'ok':'err');"
    "}catch(e){toast('Save error','err');}}\n"
    "\n"
    "function openVital(type){window.location.href='/vital/'+type+'?token='+encodeURIComponent(tok);}\n"
    "function startRT(){loadRT();rtTimer=setInterval(loadRT,3000);}\n"
    "async function loadRT(){"
    "if(!tok)return;"
    "try{"
    "var r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "var d=await r.json();if(!d.success){doLogout();return;}updDash(d);"
    "}catch(e){}}\n"
  ));

  server.sendContent(F(
    "function updDash(d){"
    "var fd=document.getElementById('fDot'),ft=document.getElementById('fTxt'),fb=document.getElementById('fBanner');"
    "if(d.fingerDetected){"
    "fd.className='fd ok';ft.className='ft ok';"
    "if(d.sensorWarmup){"
    "ft.textContent='Warming up... keep finger still (15s for accurate HR)';"
    "fb.style.borderColor='rgba(255,193,7,0.4)';fb.style.background='rgba(255,193,7,0.06)';}"
    "else{"
    "ft.textContent='Finger detected \u2014 live reading active';"
    "fb.style.borderColor='rgba(46,204,113,0.3)';fb.style.background='rgba(46,204,113,0.04)';}}"
    "else{"
    "fd.className='fd';ft.className='ft';"
    "ft.textContent='Place finger firmly on MAX30102 sensor';"
    "fb.style.borderColor='rgba(255,193,7,0.2)';fb.style.background='rgba(255,193,7,0.04)';}"
    "\n"
    "// Busy banner from polling\n"
    "var bb=document.getElementById('busyBanner');\n"
    "if(d.deviceBusy&&!d.measuring){\n"
    "document.getElementById('busySub').textContent='User is measuring (\u2248'+d.measureRemaining+'s left). Wait...';\n"
    "bb.classList.add('show');\n"
    "}else if(!d.deviceBusy){bb.classList.remove('show');}\n"
    "\n"
    "var done=d.measurementDone||false;\n"
    "var measuring=d.measuring||false;\n"
    "\n"
    "var hr=done&&d.avgHR>0?Math.round(d.avgHR):0;"
    "document.getElementById('vcHR').textContent=hr>0?hr:'--';"
    "document.getElementById('vcHR').style.color=hr>0?getHRColor(hr):'#555';"
    "document.getElementById('vcHRS').textContent=done?(hr>0?getHRStatus(hr):'NO DATA'):(measuring?'MEASURING...':'PRESS START MEASURE');"
    "\n"
    "var o2=done&&d.avgSpO2>0?d.avgSpO2:0;"
    "document.getElementById('vcO2').textContent=o2>0?o2.toFixed(1):(done?'--':(d.spo2Frozen&&d.spO2>0?d.spO2.toFixed(1)+'*':'--'));"
    "document.getElementById('vcO2').style.color=o2>0?getO2Color(o2):(d.spo2Frozen&&d.spO2>0?getO2Color(d.spO2):'#555');"
    "document.getElementById('vcO2S').textContent=done?(o2>0?getO2Status(o2)+' (90s avg)':'NO DATA'):(measuring?(d.spO2>0?'Live '+d.spO2.toFixed(1)+'%':'Detecting...'):(d.spo2Frozen&&d.spO2>0?'Last reading':'PRESS START MEASURE'));"
    "\n"
    "var t=done&&d.avgTemp>0?d.avgTemp:0;"
    "document.getElementById('vcTp').textContent=t>0?t.toFixed(1):'--';"
    "document.getElementById('vcTp').style.color=t>0?getTempColor(t):'#555';"
    "document.getElementById('vcTpS').textContent=done?(t>0?getTempStatus(t)+' (90s avg)':'NO DATA'):(measuring?'Measuring...':'Run 90s measure');"
    "\n"
    "var rr=done?(d.avgRR>0?Math.round(d.avgRR):(d.respiratoryRate>0?Math.round(d.respiratoryRate):0)):0;"
    "document.getElementById('vcRR').textContent=(done&&rr>0)?rr:'--';"
    "document.getElementById('vcRR').style.color=(done&&rr>0)?getRRColor(rr):'#555';"
    "document.getElementById('vcRRS').textContent=done?(rr>0?getRRStatus(rr):'NO DATA'):(measuring?'MEASURING...':'PRESS START MEASURE');"
    "\n"
    "var pi=done&&d.avgPI>0?d.avgPI:0;"
    "document.getElementById('vcPI').textContent=(done&&pi>0)?pi.toFixed(2):'--';"
    "document.getElementById('vcPI').style.color=(done&&pi>0)?getPIColor(pi):'#555';"
    "document.getElementById('vcPIS').textContent=done?(pi>0?getPIStatus(pi):'NO DATA'):(measuring?'MEASURING...':'PRESS START MEASURE');"
    "\n"
    "var sc=done?(typeof d.avgScore!=='undefined'?d.avgScore:(d.healthScore||0)):0;"
    "var arc=document.getElementById('scArc');"
    "if(done){"
    "document.getElementById('scVal').textContent=sc;"
    "arc.style.strokeDashoffset=(408*(1-sc/100)).toFixed(1);"
    "var sco=sc>=90?'#2ecc71':sc>=75?'#f1c40f':sc>=60?'#e67e22':'#e74c3c';"
    "var sst=sc>=90?'EXCELLENT':sc>=75?'GOOD':sc>=60?'FAIR':'POOR \u2014 CONSULT DOCTOR';"
    "arc.style.stroke=sco;"
    "document.getElementById('scSt').textContent=sst;"
    "document.getElementById('scSt').style.color=sco;"
    "var bars='';"
    "if(hr>0)bars+='<div class=\"sb\"><span class=\"sbl\">HR</span><div class=\"sbt\"><div class=\"sbf\" style=\"width:'+Math.min(100,Math.max(5,Math.round(100-Math.abs(hr-80)*2)))+'%;background:#ff4757\"></div></div><span style=\"font-size:11px;color:#666;margin-left:5px\">'+hr+'</span></div>';"
    "if(o2>0)bars+='<div class=\"sb\"><span class=\"sbl\">SpO2</span><div class=\"sbt\"><div class=\"sbf\" style=\"width:'+Math.min(100,Math.max(5,Math.round((o2-80)*5)))+'%;background:#00b4d8\"></div></div><span style=\"font-size:11px;color:#666;margin-left:5px\">'+o2.toFixed(1)+'</span></div>';"
    "if(t>0)bars+='<div class=\"sb\"><span class=\"sbl\">TEMP</span><div class=\"sbt\"><div class=\"sbf\" style=\"width:'+Math.min(100,Math.max(5,Math.round(100-Math.abs(t-36.7)*25)))+'%;background:#ff6348\"></div></div><span style=\"font-size:11px;color:#666;margin-left:5px\">'+t.toFixed(1)+'</span></div>';"
    "if(rr>0)bars+='<div class=\"sb\"><span class=\"sbl\">RR</span><div class=\"sbt\"><div class=\"sbf\" style=\"width:'+Math.min(100,Math.max(5,Math.round(100-Math.abs(rr-16)*8)))+'%;background:#2ecc71\"></div></div><span style=\"font-size:11px;color:#666;margin-left:5px\">'+rr+'</span></div>';"
    "document.getElementById('scBars').innerHTML=bars;"
    "}else if(d.measuring){"
    "document.getElementById('scVal').textContent='...';"
    "arc.style.strokeDashoffset=408;arc.style.stroke='rgba(0,212,255,0.3)';"
    "document.getElementById('scSt').textContent='Measuring... '+(d.measureRemaining||'')+'s left';"
    "document.getElementById('scSt').style.color='#00d4ff';"
    "document.getElementById('scBars').innerHTML='';"
    "}else{"
    "document.getElementById('scVal').textContent='--';"
    "arc.style.strokeDashoffset=408;arc.style.stroke='rgba(255,255,255,0.08)';"
    "document.getElementById('scSt').textContent='Press START MEASURE below';"
    "document.getElementById('scSt').style.color='#555';"
    "document.getElementById('scBars').innerHTML='';}}\n"
    "\n"
    "function getHRColor(hr){if(hr>=60&&hr<=100)return'#2ecc71';if(hr<60||hr>100)return'#f39c12';return'#e74c3c';}\n"
    "function getHRStatus(hr){if(hr<50)return'BRADYCARDIA';if(hr<60)return'LOW NORMAL';if(hr<=100)return'NORMAL';if(hr<=110)return'ELEVATED';return'TACHYCARDIA';}\n"
    "function getO2Color(s){if(s>=97)return'#2ecc71';if(s>=95)return'#f1c40f';if(s>=92)return'#e67e22';return'#e74c3c';}\n"
    "function getO2Status(s){if(s>=97)return'NORMAL';if(s>=95)return'ACCEPTABLE';if(s>=92)return'LOW';return'CRITICAL';}\n"
    "function getTempColor(t){if(t>=36.1&&t<=37.3)return'#2ecc71';if(t<36.1)return'#74b9ff';if(t<=37.5)return'#f39c12';return'#e74c3c';}\n"
    "function getTempStatus(t){if(t<35.5)return'HYPOTHERMIA';if(t<35.8)return'LOW';if(t<36.1)return'SUBNORMAL';if(t<=37.3)return'NORMAL';if(t<=37.5)return'ELEVATED';if(t<=38.0)return'LOW FEVER';return'FEVER';}\n"
    "function getRRColor(rr){if(rr>=12&&rr<=20)return'#2ecc71';if(rr>=10&&rr<=24)return'#f39c12';return'#e74c3c';}\n"
    "function getRRStatus(rr){if(rr<10)return'BRADYPNEA';if(rr<12)return'LOW';if(rr<=20)return'NORMAL';if(rr<=25)return'ELEVATED';return'TACHYPNEA';}\n"
    "function getPIColor(pi){if(pi>=1.5&&pi<=5)return'#2ecc71';if(pi<0.5)return'#e74c3c';if(pi<1.5)return'#f39c12';return'#a29bfe';}\n"
    "function getPIStatus(pi){if(pi<0.5)return'VERY WEAK';if(pi<1.5)return'WEAK';if(pi<=5)return'NORMAL';if(pi<=10)return'STRONG';return'VERY STRONG';}\n"
  ));

  server.sendContent(F(
    "async function showHist(){"
    "document.getElementById('mHist').classList.add('show');"
    "document.getElementById('histC').innerHTML='<div style=\"text-align:center;padding:40px;color:#555\">Loading...</div>';"
    "try{"
    "var r=await fetch('/history?token='+encodeURIComponent(tok));"
    "var d=await r.json();"
    "if(!d.success){document.getElementById('histC').innerHTML='<p style=\"color:#ff4757\">Failed to load</p>';return;}"
    "if(!d.records||d.records.length===0){"
    "document.getElementById('histC').innerHTML='<div style=\"text-align:center;padding:30px\">'+"
    "'<div style=\"font-size:40px;margin-bottom:15px\">&#128202;</div>'+"
    "'<p style=\"color:#666\">No records yet.</p>'+"
    "'<p style=\"color:#555;font-size:13px;margin-top:8px\">Run 90s measurement to start. Records auto-save.</p></div>';"
    "return;}"
    "var h='<div style=\"text-align:center;margin-bottom:14px\">';"
    "h+='<button onclick=\"downloadFullReport()\" style=\"background:linear-gradient(135deg,#00b4d8,#0077b6);border:none;color:#fff;padding:12px 28px;border-radius:10px;cursor:pointer;font-size:14px;letter-spacing:2px;width:100%\">&#128202; FULL REPORT WITH TRENDS</button>';"
    "h+='</button>';"
    "h+='<div style=\"font-size:11px;color:#555;margin-top:6px\">Mobile: saves HTML with charts &nbsp;|&nbsp; Desktop: opens print view</div>';"
    "h+='</div>';"
    "h+='<div style=\"overflow-x:auto\">';"
    "h+='<table class=\"dt\"><thead><tr>';"
    "h+='<th>DATE/TIME</th><th>HR</th><th>SpO2%</th><th>TEMP C</th><th>RR</th><th>PI%</th><th>SCORE</th><th>PDF</th></tr></thead><tbody>';"
    "d.records.forEach(function(rec){"
    "var sc_c=rec.score>=90?'#2ecc71':rec.score>=75?'#f1c40f':rec.score>=60?'#e67e22':'#e74c3c';"
    "var spo2Str=rec.spo2>0?rec.spo2.toFixed(1):'--';"
    "var tempStr=rec.temp>0?rec.temp.toFixed(1):'--';"
    "var rrStr=rec.rr>0?rec.rr:'--';"
    "var piStr=rec.pi>0?rec.pi.toFixed(2):'--';"
    "h+='<tr><td>'+rec.time+'</td><td><strong>'+rec.hr+'</strong></td>';"
    "h+='<td>'+spo2Str+'</td><td>'+tempStr+'</td><td>'+rrStr+'</td><td>'+piStr+'</td>';"
    "h+='<td><span style=\"color:'+sc_c+';font-weight:600\">'+rec.score+'</span></td>';"
    "h+='<td><button class=\"pdfb\" onclick=\"openRecordPdf('+rec.idx+')\">&#128247; PDF</button></td></tr>';});"
    "h+='</tbody></table></div>';"
    "h+='<p style=\"color:#555;font-size:12px;margin-top:10px\">Last '+d.records.length+' of '+d.total+' total records</p>';"
    "document.getElementById('histC').innerHTML=h;"
    "}catch(e){document.getElementById('histC').innerHTML='<p style=\"color:#ff4757\">Error: '+e.message+'</p>';}}\n"
    "\n"
    "function openRecordPdf(idx){"
    "window.open('/record-print?token='+encodeURIComponent(tok)+'&idx='+idx,'_blank');}\n"
    "\n"
    "function downloadFullReport(){"
    "if(!tok){toast('Please sign in first','err');return;}"
    "if(isMobile()){"
    "window.location.href='/full-report-download?token='+encodeURIComponent(tok);"
    "}else{"
    "window.location.href='/report-print?token='+encodeURIComponent(tok);}}"
    "\n"
    "\n"
    "async function doReport(){"
    "document.getElementById('mReport').classList.add('show');"
    "document.getElementById('repC').innerHTML='<div style=\"text-align:center;padding:40px;color:#555\">Generating report...</div>';"
    "try{"
    "var r=await fetch('/report?token='+encodeURIComponent(tok));"
    "var d=await r.json();"
    "if(!d.success){document.getElementById('repC').innerHTML='<p style=\"color:#ff4757\">Failed</p>';return;}"
    "lastRep=d;"
    "var sc=d.healthScore||0;"
    "var sc_c=sc>=90?'#2ecc71':sc>=75?'#f1c40f':sc>=60?'#e67e22':'#e74c3c';"
    "var sc_s=sc>=90?'EXCELLENT':sc>=75?'GOOD':sc>=60?'FAIR':sc>0?'POOR':'RUN 90s MEASURE';"
    "var src=d.dataSource==='90s_average'?'90s averaged':'Live (run 90s for accuracy)';"
    "var h='<div style=\"font-size:11px;color:#555;text-align:center;margin-bottom:12px\">Source: '+src+'</div>';"
    "h+='<div style=\"background:rgba(255,255,255,0.03);border:1px solid rgba(255,255,255,0.07);border-radius:12px;padding:16px;margin-bottom:12px\">';"
    "h+='<div style=\"font-size:11px;letter-spacing:2px;color:#00d4ff;margin-bottom:10px\">PATIENT INFORMATION</div>';"
    "h+='<div style=\"display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:8px\">';"
    "h+='<div><span style=\"color:#666;font-size:11px\">NAME</span><div>'+d.name+'</div></div>';"
    "h+='<div><span style=\"color:#666;font-size:11px\">AGE / GENDER</span><div>'+(d.age||'--')+' / '+(d.gender||'--')+'</div></div>';"
    "if(d.height>0){var bmi=(d.weight/Math.pow(d.height/100,2)).toFixed(1);h+='<div><span style=\"color:#666;font-size:11px\">BMI</span><div>'+bmi+'</div></div>';}"
    "h+='</div></div>';"
    "h+='<div style=\"text-align:center;background:linear-gradient(135deg,rgba(0,212,255,0.06),rgba(123,94,167,0.06));border:1px solid rgba(0,212,255,0.15);border-radius:12px;padding:20px;margin-bottom:12px\">';"
    "h+='<div style=\"font-size:56px;font-weight:900;color:'+sc_c+'\">'+sc+'</div>';"
    "h+='<div style=\"font-size:14px;color:'+sc_c+';letter-spacing:3px;margin-top:4px\">'+sc_s+'</div></div>';"
    "h+='<div style=\"display:grid;grid-template-columns:repeat(auto-fit,minmax(100px,1fr));gap:8px;margin-bottom:12px\">';"
    "var spo2Disp=d.spO2>0?d.spO2.toFixed(1):'--';"
    "var tempDisp=d.tempValid&&d.temperature>0?d.temperature.toFixed(1)+' C':'--';"
    "var rrDisp=d.respiratoryRate>0?d.respiratoryRate:'--';"
    "var piDisp=d.perfusionIndex>0?d.perfusionIndex.toFixed(2):'--';"
    "var cards=["
    "{l:'HEART RATE',v:d.heartRate>0?String(d.heartRate):'--',u:'bpm (60-100)',c:'#ff4757'},"
    "{l:'OXYGEN SAT',v:spo2Disp,u:'SpO2% (95-100)',c:'#00b4d8'},"
    "{l:'TEMPERATURE',v:tempDisp,u:'C (36.1-37.3)',c:'#ff6348'},"
    "{l:'RESPIRATORY',v:rrDisp,u:'br/min (12-20)',c:'#2ecc71'},"
    "{l:'PERFUSION',v:piDisp,u:'PI% (1.5-5)',c:'#a29bfe'}"
    "];"
    "cards.forEach(function(cd){"
    "h+='<div style=\"background:rgba(255,255,255,0.03);border:1px solid rgba(255,255,255,0.07);border-radius:10px;padding:12px;text-align:center\">';"
    "h+='<div style=\"font-size:9px;color:#555;letter-spacing:2px\">'+cd.l+'</div>';"
    "h+='<div style=\"font-size:18px;color:'+cd.c+';margin:4px 0;font-weight:bold\">'+cd.v+'</div>';"
    "h+='<div style=\"font-size:10px;color:#777\">'+cd.u+'</div></div>';});"
    "h+='</div>';"
    "h+='<div style=\"font-size:12px;color:#555;text-align:center\">Total saved records: '+d.dataCount+'</div>';"
    "if(d.history&&d.history.length>0){"
    "h+='<div style=\"font-size:12px;color:#888;text-align:center;margin-top:8px\">&#128202; '+d.history.length+' historical records — click Print for full trend charts</div>';}"
    "else{"
    "h+='<div style=\"font-size:12px;color:#555;text-align:center;margin-top:8px\">No historical records yet. Trend charts appear after first measurement.</div>';}"
    "document.getElementById('repC').innerHTML=h;"
    "}catch(e){document.getElementById('repC').innerHTML='<p style=\"color:#ff4757\">Error</p>';}}\n"
    "\n"
    "function isMobile(){"
    "return(/Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent)||window.innerWidth<=900);}"
    "\n"
    "// Single report button: on mobile → download as HTML (PDF broken on mobile browsers);"
    "// on desktop → open print page so user can Save as PDF with full trend charts."
    "function dlReport(){"
    "if(!tok){toast('Please sign in first','err');return;}"
    "if(isMobile()){"
    "window.location.href='/full-report-download?token='+encodeURIComponent(tok);"
    "}else{"
    "window.location.href='/report-print?token='+encodeURIComponent(tok);}}"
    "\n"
  ));

  server.sendContent(F(
    "async function showProfile(){"
    "document.getElementById('mProf').classList.add('show');"
    "try{var r=await fetch('/profile?token='+encodeURIComponent(tok));var d=await r.json();"
    "if(!d.success){document.getElementById('profC').innerHTML='<p style=\"color:#ff4757\">Failed</p>';return;}"
    "function fld(l,v){return '<div style=\"background:rgba(255,255,255,0.03);border:1px solid rgba(255,255,255,0.06);border-radius:10px;padding:12px\">'+"
    "'<div style=\"font-size:10px;color:#555;letter-spacing:2px\">'+l+'</div>'+"
    "'<div style=\"font-size:15px;margin-top:3px\">'+v+'</div></div>';}"
    "var h='<div style=\"display:grid;gap:10px\">';"
    "h+=fld('FULL NAME',d.name)+fld('USERNAME','@'+d.username)+fld('EMAIL',d.email);"
    "h+=fld('PHONE',d.phone)+fld('AGE',d.age+' years')+fld('GENDER',d.gender);"
    "if(d.height>0){var h2=d.height/100;h+=fld('HEIGHT / WEIGHT / BMI',d.height+'cm / '+d.weight+'kg / BMI '+(d.weight/(h2*h2)).toFixed(1));}"
    "h+=fld('CONDITIONS',d.diseases)+fld('RECORDS SAVED',d.dataCount)+fld('TOTAL LOGINS',d.loginCount);"
    "h+='</div>';"
    "h+='<div style=\"margin-top:18px;background:rgba(255,71,87,0.04);border:1px solid rgba(255,71,87,0.12);border-radius:12px;padding:18px\">';"
    "h+='<div style=\"color:#ff4757;font-size:12px;letter-spacing:3px;margin-bottom:12px\">CHANGE PASSWORD</div>';"
    "h+='<input type=\"password\" id=\"cpC\" placeholder=\"Current Password\" style=\"width:100%;padding:10px;background:rgba(255,255,255,0.04);border:1px solid rgba(255,255,255,0.08);border-radius:8px;color:#fff;font-size:14px;margin-bottom:8px\">';"
    "h+='<input type=\"password\" id=\"cpN\" placeholder=\"New Password (min 6)\" style=\"width:100%;padding:10px;background:rgba(255,255,255,0.04);border:1px solid rgba(255,255,255,0.08);border-radius:8px;color:#fff;font-size:14px;margin-bottom:8px\">';"
    "h+='<input type=\"password\" id=\"cpCn\" placeholder=\"Confirm New Password\" style=\"width:100%;padding:10px;background:rgba(255,255,255,0.04);border:1px solid rgba(255,255,255,0.08);border-radius:8px;color:#fff;font-size:14px;margin-bottom:10px\">';"
    "h+='<button onclick=\"chgPw()\" style=\"background:linear-gradient(135deg,rgba(255,71,87,0.25),rgba(255,71,87,0.15));border:1px solid rgba(255,71,87,0.3);color:#ff6b6b;padding:11px 24px;border-radius:8px;cursor:pointer;font-size:14px;letter-spacing:2px\">CHANGE PASSWORD</button>';"
    "h+='</div>';"
    "document.getElementById('profC').innerHTML=h;"
    "}catch(e){document.getElementById('profC').innerHTML='<p style=\"color:#ff4757\">Error</p>';}}\n"
    "\n"
    "async function chgPw(){"
    "var cur=document.getElementById('cpC').value;"
    "var np=document.getElementById('cpN').value;"
    "var cn=document.getElementById('cpCn').value;"
    "if(!cur||!np||!cn){toast('Fill all fields','err');return;}"
    "if(np!==cn){toast('Passwords do not match','err');return;}"
    "if(np.length<6){toast('Min 6 characters','err');return;}"
    "try{var r=await fetch('/change-password',{method:'POST',headers:{Authorization:tok,'Content-Type':'application/json'},"
    "body:JSON.stringify({currentPassword:cur,newPassword:np})});var d=await r.json();"
    "if(d.success)toast('Password changed!','ok');else toast(d.message||'Failed','err');"
    "}catch(e){toast('Error','err');}}\n"
    "\n"
    "async function setDeviceTime(){"
    "const ut=Math.floor(Date.now()/1000);"
    "try{const r=await fetch('/set-time',{method:'POST',"
    "headers:{Authorization:tok,'Content-Type':'application/json'},"
    "body:JSON.stringify({unixtime:ut})});"
    "const d=await r.json();"
    "if(d.success){toast('Device time synced to '+new Date().toLocaleString(),'ok');loadAdmin();}"
    "else toast(d.message||'Failed','err');"
    "}catch(e){toast('Error: '+e.message,'err');}}\n"
    "\n"
    "async function loadAdmin(){"
    "if(!isAdm||!tok)return;"
    "try{var r=await fetch('/admin/users?token='+encodeURIComponent(tok));var d=await r.json();"
    "if(!d.success)return;"
    "document.getElementById('aTU').textContent=d.users.length;"
    "document.getElementById('aAS').textContent=d.activeSessions;"
    // Show active user names
    "var activeNames=d.activeUsers||[];"
    "document.getElementById('aAU').textContent=activeNames.length>0?activeNames.join(', '):'None online';"
    // Device uptime
    "var h2=Math.floor(d.uptime/3600000),m2=Math.floor((d.uptime%3600000)/60000),s2=Math.floor((d.uptime%60000)/1000);"
    "document.getElementById('aUT').textContent=h2+'h '+m2+'m '+s2+'s';"
    "if(d.deviceTime){var ct=document.getElementById('curTimeDisp');if(ct)ct.textContent='Device time: '+d.deviceTime;}"
    "var rows='';"
    "if(!d.users||d.users.length===0){"
    "rows='<tr><td colspan=\"6\" style=\"text-align:center;color:#555;padding:30px\">No users registered</td></tr>';"
    "}else{"
    "d.users.forEach(function(u){"
    "var isOnline=activeNames.indexOf(u.username)>=0;"
    "var onlineBadge=isOnline?'<span style=\"background:#2ecc71;color:#000;font-size:9px;padding:2px 6px;border-radius:10px;margin-left:6px\">ONLINE</span>':'';"
    "rows+='<tr><td>'+u.name+onlineBadge+'</td><td><span class=\"badge\">@'+u.username+'</span></td>';"
    "rows+='<td>'+u.email+'</td><td>'+u.age+' / '+u.gender+'</td><td>'+u.dataCount+'</td>';"
    "rows+='<td>';"
    "rows+='<button class=\"vb\" data-u=\"'+u.username+'\" onclick=\"admView(this.dataset.u)\">VIEW</button>';\n"
    "rows+='<button class=\"rpb\" data-u=\"'+u.username+'\" onclick=\"admReport(this.dataset.u)\">REPORT</button>';\n"
    "rows+='<button class=\"db\" data-u=\"'+u.username+'\" data-n=\"'+u.name+'\" onclick=\"admDel(this.dataset.u,this.dataset.n)\">DELETE</button>';\n"
    "rows+='</td></tr>';});}"
    "document.getElementById('uBody').innerHTML=rows;"
    "}catch(e){}}\n"
    "\n"
    "function admReport(username){"
    "var u=encodeURIComponent(username),t=encodeURIComponent(tok);"
    "if(isMobile()){window.location.href='/full-report-download?token='+t+'&user='+u;}"
    "else{window.location.href='/report-print?token='+t+'&user='+u;}}\n"
    "\n"
    "async function admView(username){"
    "lastAdmViewUser=username;"
    "document.getElementById('mAdmU').classList.add('show');"
    "document.getElementById('admUT').textContent='USER: '+username.toUpperCase();"
    "document.getElementById('admUC').innerHTML='<div style=\"text-align:center;padding:30px;color:#555\">Loading...</div>';"
    "try{var r=await fetch('/admin/userdata?token='+encodeURIComponent(tok)+'&user='+encodeURIComponent(username));"
    "var d=await r.json();"
    "if(!d.success){document.getElementById('admUC').innerHTML='<p style=\"color:#ff4757\">Failed</p>';return;}"
    "var h='<div style=\"background:rgba(255,255,255,0.03);border:1px solid rgba(255,255,255,0.07);border-radius:10px;padding:14px;margin-bottom:14px\">';"
    "h+='<div style=\"display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:8px\">';"
    "h+='<div><span style=\"color:#555;font-size:11px\">NAME</span><div>'+d.name+'</div></div>';"
    "h+='<div><span style=\"color:#555;font-size:11px\">EMAIL</span><div>'+d.email+'</div></div>';"
    "h+='<div><span style=\"color:#555;font-size:11px\">AGE/GENDER</span><div>'+d.age+'/'+d.gender+'</div></div>';"
    "h+='<div><span style=\"color:#555;font-size:11px\">RECORDS</span><div>'+d.dataCount+'</div></div>';"
    "h+='</div></div>';"
    "h+='<div style=\"text-align:right;margin-bottom:10px\">';"
    "h+='<button class=\"rpb\" data-u=\"'+d.username+'\" onclick=\"admReport(this.dataset.u)\" style=\"font-size:13px;padding:8px 16px\">&#128247; FULL REPORT WITH TRENDS</button>';\n"
    "h+='</div>';"
    "if(d.records&&d.records.length>0){"
    "h+='<div style=\"overflow-x:auto\"><table class=\"dt\"><thead><tr>';"
    "h+='<th>DATE/TIME</th><th>HR</th><th>SpO2%</th><th>TEMP C</th><th>RR</th><th>PI%</th><th>SCORE</th><th>PDF</th></tr></thead><tbody>';"
    "d.records.forEach(function(rec){"
    "var sc_c=rec.score>=90?'#2ecc71':rec.score>=75?'#f1c40f':rec.score>=60?'#e67e22':'#e74c3c';"
    "var spo2Str=rec.spo2>0?rec.spo2.toFixed(1):'--';"
    "var tmpStr=rec.temp>0?rec.temp.toFixed(1):'--';"
    "var rrStr=rec.rr>0?rec.rr:'--';"
    "var piStr=rec.pi>0?rec.pi.toFixed(2):'--';"
    "h+='<tr><td>'+rec.time+'</td><td>'+rec.hr+'</td><td>'+spo2Str+'</td>';"
    "h+='<td>'+tmpStr+'</td><td>'+rrStr+'</td><td>'+piStr+'</td>';"
    "h+='<td><span style=\"color:'+sc_c+';font-weight:600\">'+rec.score+'</span></td>';"
    "h+='<td><button class=\"pdfb\" onclick=\"window.open(\\''+'/record-print?token='+encodeURIComponent(tok)+'&user='+encodeURIComponent(d.username)+'&idx='+rec.idx+'\\',\\'_blank\\')\">&#128247; PDF</button></td></tr>';});"
    "h+='</tbody></table></div>';"
    "}else h+='<p style=\"color:#555;text-align:center;padding:20px\">No records yet</p>';"
    "document.getElementById('admUC').innerHTML=h;"
    "}catch(e){document.getElementById('admUC').innerHTML='<p style=\"color:#ff4757\">Error</p>';}}\n"
    "\n"
    "async function admDel(username,name){"
    "if(!confirm('DELETE \"'+name+'\" (@'+username+')? ALL data permanently erased.'))return;"
    "try{var r=await fetch('/admin/delete-user',{method:'POST',"
    "headers:{Authorization:tok,'Content-Type':'application/json'},"
    "body:JSON.stringify({username:username})});var d=await r.json();"
    "if(d.success){toast('User '+username+' deleted.','ok');loadAdmin();}"
    "else toast(d.message||'Failed to delete','err');}"
    "catch(e){toast('Error','err');}}\n"
    "\n"
    "window.onload=async function(){"
    "if(!tok){showScr('sSignIn');return;}"
    "try{var r=await fetch('/realtime?token='+encodeURIComponent(tok));"
    "var d=await r.json();"
    "if(d.success){"
    "var name=SS.getItem('vsNm')||'User';showDash(name,isAdm);"
    // If measurement was running when user navigated away, resume the UI countdown
    "if(d.measuring&&d.measureRemaining>0){"
    "var rem=d.measureRemaining;"
    "measElapsed=90-rem;"
    "var btn=document.getElementById('measBtn');"
    "if(btn){btn.disabled=true;btn.textContent='MEASURING...';}"
    "document.getElementById('measProg').classList.add('show');"
    "document.getElementById('mSec').textContent=rem;"
    "clearInterval(measTimer);"
    "measTimer=setInterval(async function(){"
    "measElapsed++;var pct=Math.round((measElapsed/90)*100);"
    "document.getElementById('mpfill').style.width=Math.min(pct,100)+'%';"
    "document.getElementById('mSec').textContent=Math.max(0,90-measElapsed);"
    "try{var rs=await fetch('/measure-status?token='+encodeURIComponent(tok));"
    "var ds=await rs.json();"
    "document.getElementById('mlHR').textContent=ds.liveHR>0?ds.liveHR:'--';"
    "document.getElementById('mlO2').textContent=ds.liveO2>0?ds.liveO2.toFixed(1)+'%':'reading...';"
    "document.getElementById('mlTp').textContent=ds.liveTmp>0?ds.liveTmp.toFixed(1)+'\u00b0C':'--';"
    "document.getElementById('mlRR').textContent=ds.liveRR>0?ds.liveRR:'--';"
    "if(measElapsed>=90||ds.done){"
    "clearInterval(measTimer);"
    "document.getElementById('measProg').classList.remove('show');"
    "if(btn){btn.disabled=false;btn.textContent='\u25b6 START 90-SECOND MEASURE';}"
    "if(ds.ready){toast('Done! HR:'+Math.round(ds.avgHR)+' SpO2:'+(ds.avgSpO2>0?ds.avgSpO2.toFixed(1):'--')+'%','ok');}"
    "}}catch(e){}},1000);}}"
    "else{SS.removeItem('vsTok');SS.removeItem('vsAdm');SS.removeItem('vsNm');"
    "tok='';isAdm=false;showScr('sSignIn');}"
    "}catch(e){showScr('sSignIn');}}\n"
    "\n"
    "setInterval(function(){if(isAdm&&tok)loadAdmin();},30000);\n"
    "</script></body></html>\n"
  ));

  server.sendContent("");
}

void handleNotFound() {
  if (!isClientAllowed()) { server.send(403, "text/plain", "Access denied: connect to VitalScope-Health WiFi"); return; }
  server.sendHeader("Location", "http://192.168.4.1/", true);
  server.send(302, "text/plain", "");
}

void initializeWebServer() {
  server.enableCORS(false);
  server.enableDelay(false);
  server.begin(80);  // backlog handled by lwIP config
  server.on("/",                  HTTP_GET,  handleRoot);
  server.on("/signin",            HTTP_POST, handleSignIn);
  server.on("/signup",            HTTP_POST, handleSignUp);
  server.on("/send-otp",          HTTP_POST, handleSendOTP);
  server.on("/verify-otp",        HTTP_POST, handleVerifyOTP);
  server.on("/forgot-password",   HTTP_POST, handleForgotPassword);
  server.on("/reset-password",    HTTP_POST, handleResetPassword);
  server.on("/logout",            HTTP_POST, handleLogout);
  server.on("/vitals",            HTTP_GET,  handleGetVitals);
  server.on("/realtime",          HTTP_GET,  handleGetRealtimeData);
  server.on("/measure",           HTTP_POST, handleMeasure);
  server.on("/measure-status",    HTTP_GET,  handleMeasureStatus);
  server.on("/save-record",       HTTP_POST, handleSaveRecord);
  server.on("/profile",           HTTP_GET,  handleGetProfile);
  server.on("/update-profile",    HTTP_POST, handleUpdateProfile);
  server.on("/change-password",   HTTP_POST, handleChangePassword);
  server.on("/history",           HTTP_GET,  handleGetHistory);
  server.on("/report",            HTTP_GET,  handleGenerateReport);
  server.on("/report-print",      HTTP_GET,  handleReportPrint);
  server.on("/record-print",      HTTP_GET,  handleRecordPrint);
  server.on("/record-download",        HTTP_GET,  handleRecordDownload);
  server.on("/full-report-download",   HTTP_GET,  handleFullReportDownload);
  server.on("/vital/hr",          HTTP_GET,  handleHRPage);
  server.on("/vital/spo2",        HTTP_GET,  handleSpO2Page);
  server.on("/vital/temp",        HTTP_GET,  handleTempPage);
  server.on("/vital/resp",        HTTP_GET,  handleRespPage);
  server.on("/admin",             HTTP_GET,  handleAdminDashboard);
  server.on("/admin/users",       HTTP_GET,  handleAdminGetUsers);
  server.on("/admin/userdata",    HTTP_GET,  handleAdminGetUserData);
  server.on("/admin/delete-user", HTTP_POST, handleAdminDeleteUser);
  server.on("/set-time",           HTTP_POST, handleSetTime);
  server.on("/admin/stats",       HTTP_GET,  handleSystemStats);
  server.onNotFound(handleNotFound);
  Serial.println(F("Web server started on port 80"));
}

// ─── END — VitalScope v1.0 ────────────────────────────────────────────────────
