@echo off
cd /d "%~dp0"
where python >nul 2>&1
if errorlevel 1 (
  echo Python 3 is required. Install it from https://www.python.org/downloads/ and run this file again.
  pause
  exit /b 1
)
python server.py
if errorlevel 1 pause
