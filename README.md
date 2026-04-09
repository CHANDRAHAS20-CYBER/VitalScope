Real-time wearable multi-parameter health monitoring system using ESP32-C3

📌 Project Overview

VitalScope is a compact, ESP32-C3-based wearable system designed to measure, process, and display key physiological vitals in real time. It integrates multiple biomedical sensors with embedded signal processing and a self-hosted web interface, enabling reliable, offline health monitoring without cloud dependency.

⚙️ Features
Real-time monitoring of:
Heart Rate (HR)
Blood Oxygen Saturation (SpO₂)
Body Temperature
Respiratory Rate (RR)
Perfusion Index (PI)
AI-weighted Overall Health Score (AHA/WHO aligned)
90-second averaged measurement mode for accuracy
Multi-user system (up to 50 users, 500 records each)
On-device data storage using SPI flash
Built-in Wi-Fi Access Point (192.168.4.1)
Secure login with OTP verification (OLED display)
Downloadable health reports with SVG trend charts
Fully offline operation (no cloud required)

🧩 Hardware Components
ESP32-C3-DevKitM-1-N4X (Main Controller)
MAX30102 – Heart Rate & SpO₂ Sensor (PPG)
MLX90614 – Infrared Temperature Sensor
LSM6DSOX – IMU (Respiratory Rate detection)
SSD1306 OLED Display – Status & UI feedback

🔌 Pin Configuration
Component	Interface	ESP32-C3 Pins
MAX30102	I2C	GPIO4 (SDA), GPIO5 (SCL)
MLX90614	I2C	Shared Bus
LSM6DSOX	I2C	Shared Bus
SSD1306 OLED	I2C	Shared Bus

All sensors operate on a shared I2C bus with watchdog recovery handling.

🧠 Firmware Architecture
Developed using Arduino framework for ESP32-C3
Modular architecture:
Sensor acquisition layer
Signal processing layer
Health analytics engine
Web server & UI handler
Key techniques:
I2C bus management with recovery
Sensor warm-up sequencing
Memory-optimized multi-user session handling
SPI flash-based structured storage

🌐 Web Interface
Hosted directly on ESP32 (Access via 192.168.4.1)
Features:
User registration & login
OTP verification (displayed on OLED)
Health history tracking
Graphical reports (SVG-based charts)
Session-based multi-user isolation

📊 Health Score Algorithm
Based on clinically referenced ranges (AHA/WHO)
Inputs:
HR, SpO₂, Temperature, RR, PI, HRV
Processing:
90-second averaged data window
Weighted scoring model
Output:
Overall Health Score
Stress Level classification

🚀 Getting Started
Connect hardware as per pin configuration
Install required libraries (listed below)
Flash firmware to ESP32-C3
Power the device
Connect to Wi-Fi AP: VitalScope
Open browser → 192.168.4.1

📚 Libraries Required
Wire (I2C communication)
Adafruit SSD1306
Adafruit GFX
MAX30102 library
SparkFun MLX90614
LSM6DSOX driver
WiFi (ESP32)
WebServer / AsyncWebServer (depending on implementation)
SPIFFS / LittleFS

📄 License
This project is intended for academic and research purposes.

⚠️ Disclaimer

This system is not a certified medical device. Measurements are for educational and monitoring purposes only and should not be used for clinical diagnosis.
