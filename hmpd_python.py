#!/usr/bin/env python3
"""
HMPD Python Replacement
Reads E2 medical cart board and sends data directly to Azure
Replaces the problematic hmpd C++ binary
"""

# Version of this script
SCRIPT_VERSION = "1.0.46"  # 2026-07-15 TWO Hartford-readiness changes. (1) PROD-TENANT PLUMBING: authority/scope/callhome/cartusers endpoints are now .env-overridable (AZURE_AUTHORITY, AZURE_SCOPE, CALLHOME_ENDPOINT, CARTUSERS_ENDPOINT); when absent or blank the daemon behaves exactly as before (dev tenant). Needed because Hartford's tenant lives on Diego's NEW production server — the golden image now only waits on the endpoint VALUES, not a code change. Values travel ToolBox template → config.env → manual_setup → .env. (2) UPS-LESS DEGRADED CALLHOME: get_power_data() failure (dead/absent TDI UPS, NUT down) no longer aborts the run — mirrors the v1.0.27 E2-board decoupling. The cart now calls home with empty power fields (visible on the dashboard instead of vanishing); the power LOG is skipped while degraded. v1.0.45 lineage retained: board-RTC clock-sync fallback restored (sync_clocks() prefers the battery-backed board RTC over a wrong Pi clock when HTTPS time-sync fails AND |board − Pi| < 2y), belt-and-suspenders to manual_setup.set_clock_from_usb. v1.0.44 lineage = Hartford Pro candidate (AP notification + E3 C1/C0 alert, beacon/findMeBeacon, help-request queue, partial-G0 hardening).

import os
import json
import socket
import logging
import logging.handlers
import serial
import time
import re
import hashlib
from datetime import datetime, timezone
import requests
import msal
from dotenv import load_dotenv
import subprocess
import hid
import usb.core
import usb.util
import struct
import fcntl
import py_compile

# Configure logging with rotation (5MB max, 3 backups — prevents disk from filling)
# Prefer /var/log/ (tmpfs after fstab change) to avoid SD card writes.
# Fall back to /home/pi/ if /var/log is not writable (pre-fstab boards).
LOG_PATH = '/var/log/hmpd_python.log'
if not os.access(os.path.dirname(LOG_PATH), os.W_OK):
    LOG_PATH = '/home/pi/hmpd_python.log'

# FIELD VISIBILITY FIX (v1.0.26): If logging to tmpfs (/var/log/), create a symlink at the
# well-known path /home/pi/hmpd_python.log so support staff tailing that path always see
# the live log. Without this, /home/pi/hmpd_python.log shows stale pre-tmpfs entries,
# causing false alarms that the cart has stopped calling home.
if LOG_PATH.startswith('/var/log/'):
    _symlink_path = '/home/pi/hmpd_python.log'
    try:
        # Remove old file/symlink if it exists and points elsewhere
        if os.path.islink(_symlink_path) or os.path.isfile(_symlink_path):
            _current = os.readlink(_symlink_path) if os.path.islink(_symlink_path) else None
            if _current != LOG_PATH:
                os.remove(_symlink_path)
                os.symlink(LOG_PATH, _symlink_path)
        elif not os.path.exists(_symlink_path):
            os.symlink(LOG_PATH, _symlink_path)
    except Exception:
        pass  # Non-fatal — fallback is that support staff check /var/log/ directly

log_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
log_file_handler = logging.handlers.RotatingFileHandler(
    LOG_PATH,
    maxBytes=5 * 1024 * 1024,  # 5MB
    backupCount=3
)
log_file_handler.setFormatter(log_formatter)
log_console_handler = logging.StreamHandler()
log_console_handler.setFormatter(log_formatter)
logging.basicConfig(
    level=logging.INFO,
    handlers=[log_file_handler, log_console_handler]
)
logger = logging.getLogger(__name__)

# ── .env encrypted backup helpers (v1.0.32) ─────────────────────────────────
# FAT32 boot partition ignores Unix permissions — chmod 600 is a no-op.
# Encrypt the backup using a key derived from the machine's unique ID so that
# pulling the SD card doesn't expose Azure credentials in plaintext.
# Magic header byte b'\x01' distinguishes encrypted from legacy plaintext backups.
_ENV_BACKUP_MAGIC = b'\x01'

def _derive_env_key(length):
    """Derive an encryption key from machine identity for .env backup."""
    machine_id = ''
    for _mid_path in ['/etc/machine-id', '/var/lib/dbus/machine-id']:
        try:
            with open(_mid_path) as _mf:
                machine_id = _mf.read().strip()
                break
        except FileNotFoundError:
            continue
    if not machine_id:
        return None
    return hashlib.pbkdf2_hmac('sha256', machine_id.encode(),
                               b'hmpd-env-backup-v1', 100000, dklen=length)

def _encrypt_env(plaintext_bytes):
    """Encrypt .env content with machine-derived key. Returns bytes or None."""
    key = _derive_env_key(len(plaintext_bytes))
    if key is None:
        return None
    return _ENV_BACKUP_MAGIC + bytes(a ^ b for a, b in zip(plaintext_bytes, key))

def _decrypt_env(raw_bytes):
    """Decrypt .env backup. Handles both encrypted (v1.0.32+) and legacy plaintext."""
    if raw_bytes and raw_bytes[0:1] == _ENV_BACKUP_MAGIC:
        cipher = raw_bytes[1:]
        key = _derive_env_key(len(cipher))
        if key is None:
            return None
        return bytes(a ^ b for a, b in zip(cipher, key))
    # Legacy plaintext backup (pre-v1.0.32) — return as-is for backward compat
    return raw_bytes

# ── .env self-restore ────────────────────────────────────────────────────────
# If .env was lost (SD corruption, prepare_golden_pi.sh, etc.) but a backup
# copy lives on the FAT32 boot partition, restore it automatically before
# load_dotenv() so credentials are available without a full re-provisioning.
_ENV_PATH    = '/home/pi/.env'
_ENV_BACKUPS = ['/boot/firmware/hmpd_env_backup', '/boot/hmpd_env_backup']
if not os.path.exists(_ENV_PATH):
    for _bk in _ENV_BACKUPS:
        if os.path.exists(_bk):
            try:
                _raw = open(_bk, 'rb').read()
                _decrypted = _decrypt_env(_raw)
                if _decrypted:
                    with open(_ENV_PATH, 'wb') as _ef:
                        _ef.write(_decrypted)
                    os.chmod(_ENV_PATH, 0o600)
                    import sys as _sys
                    print(f'SELF-HEAL: restored .env from {_bk}', file=_sys.stderr)
                else:
                    import sys as _sys
                    print(f'SELF-HEAL: could not decrypt .env from {_bk} (machine-id mismatch?)', file=_sys.stderr)
            except Exception as _re:
                import sys as _sys
                print(f'SELF-HEAL: could not restore .env from {_bk}: {_re}', file=_sys.stderr)
            break

# Load environment variables
load_dotenv()

# Configuration
# AUDIT LOG: Written to tmpfs (/var/log/) to reduce SD card writes.
# On each run, also flushed to persistent mirror (/var/lib/hmpd/sent_audit_logs.json)
# so it survives reboots. Boot-time restore loads from persistent copy into tmpfs.
SENT_LOGS_TMPFS   = '/var/log/hmpd_sent_audit_logs.json'
SENT_LOGS_PERSIST = '/var/lib/hmpd/sent_audit_logs_persist.json'

CONFIG = {
    'client_id': os.getenv('CLIENT_ID'),
    'client_secret': os.getenv('CLIENT_SECRET'),
    'facility_id': os.getenv('FACILITY_ID'),
    # v1.0.46: Tenant endpoints are .env-overridable for production deployments
    # (Hartford lives on the NEW production server; E2/Pi customers stay on the
    # test server). Absent OR blank env vars fall back to the historical dev
    # values below, so an un-plumbed cart behaves exactly as before. `or` (not
    # a getenv default) is deliberate: a blank line in .env must also fall back.
    'authority': os.getenv('AZURE_AUTHORITY') or 'https://login.microsoftonline.com/309302c3-41fe-4755-8b1c-e568322b66aa',
    'scope': [os.getenv('AZURE_SCOPE') or 'api://d23cbe9f-9533-40a2-b0c7-d3cef90cb4d4/.default'],
    'endpoint': os.getenv('CALLHOME_ENDPOINT') or 'https://fleetmanager-func-callhome-dev.azurewebsites.net/api/callhome',
    # v1.0.32: Use stable udev symlink if available (see nut-configs/99-hmpd-e2.rules).
    # Falls back to ttyACM0 for devices where the rule hasn't been deployed yet.
    'e2_serial_port': '/dev/hmpd-e2' if os.path.exists('/dev/hmpd-e2') else '/dev/ttyACM0',
    'e2_baudrate': 115200,
    'cart_id': 'UNKNOWN',  # Will be read from E2 board dynamically
    'cart_serial': 'UNKNOWN',  # Will be read from TDI Power Supply dynamically
    'cart_type': 'E2',  # Auto-detected from G0 response: 'E2' or 'E3' (Care Pro)
    'sent_logs_file': '/home/pi/sent_audit_logs.json',
    'power_log_state_file': '/var/lib/hmpd/power_log_state.json',
    'failed_payloads_file': '/var/lib/hmpd/failed_payloads.json',
    'ap_whitelist_file': '/var/lib/hmpd/ap_whitelist.json',
    'cart_type_state_file': '/var/lib/hmpd/cart_type_state.json',
    'roaming_alert_state_file': '/var/lib/hmpd/roaming_alert_state.json',
    'help_request_queue_file': '/var/lib/hmpd/help_request_queue.json',
    # Hartford Pro AP policy: by default, a whitelist mismatch is a Fleet
    # Manager location/assignment signal. Keep the cart connected unless an
    # explicit field policy opts back into local disconnect/roam enforcement.
    'ap_whitelist_enforce_disconnect': os.getenv('AP_WHITELIST_ENFORCE_DISCONNECT', '0').lower() in ('1', 'true', 'yes', 'on'),
    # Extra AP fields are opt-in because the current Fleet Manager call-home
    # contract visible in Postman only shows currentAP/aP1/aP2/aP3.
    'ap_whitelist_report_fields': os.getenv('AP_WHITELIST_REPORT_FIELDS', '0').lower() in ('1', 'true', 'yes', 'on'),
    # Height sync: local state file tracks last-uploaded heights per userId
    # so we only POST to CallHomeCartUsers when something actually changed.
    'height_state_file': '/var/lib/hmpd/height_state.json',
    # CallHomeCartUsers endpoint — base URL; facilityId is appended at call time
    # Full URL: .../api/callhome/cartusersrequest/{facilityId}/
    # v1.0.46: .env-overridable (CARTUSERS_ENDPOINT) — see the authority note above.
    'cartusers_endpoint': os.getenv('CARTUSERS_ENDPOINT') or 'https://fleetmanager-func-callhome-dev.azurewebsites.net/api/callhome/cartusersrequest',
    # v1.0.33: Mains power defaults (overridable via .env for international deployments)
    'mains_voltage': int(os.getenv('MAINS_VOLTAGE', '120')),
    'mains_frequency': int(os.getenv('MAINS_FREQUENCY', '60')),
}

# ============================================================
# RELIABILITY: Health Checks (v1.0.23)
# ============================================================

def setup_hardware_watchdog():
    """Enable the hardware watchdog timer.
    
    If the system hangs (kernel panic, I/O wait, driver crash), the
    hardware watchdog reboots the Pi automatically after 15 seconds.
    Uses /dev/watchdog which is provided by bcm2835_wdt on Pi and
    meson_wdt on Le Potato/Armbian.
    """
    try:
        if os.path.exists('/dev/watchdog'):
            # The systemd watchdog handles the petting — we just ensure the
            # kernel module is loaded. On Pi OS, add dtparam=watchdog=on to
            # /boot/config.txt. On Armbian, meson_wdt is loaded automatically.
            logger.info("✓ Hardware watchdog available (/dev/watchdog)")
        else:
            # Try loading the watchdog kernel module
            subprocess.run(['modprobe', 'bcm2835_wdt'], check=False,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if os.path.exists('/dev/watchdog'):
                logger.info("✓ Hardware watchdog loaded (bcm2835_wdt)")
            else:
                logger.debug("Hardware watchdog not available on this platform")
    except Exception as e:
        logger.debug(f"Watchdog setup skipped: {e}")

def check_and_restart_nut():
    """Check if NUT (Network UPS Tools) is responding. Auto-restart if dead.
    
    NUT driver can die after USB reconnects or power glitches without
    any visible error. This silently kills power/battery tracking.
    Restarts nut-driver and nut-server if upsc query fails.
    """
    try:
        result = subprocess.run(
            ['upsc', 'tdi@localhost', 'battery.charge'],
            capture_output=True, text=True, timeout=5
        )
        if result.returncode == 0 and result.stdout.strip():
            logger.debug(f"NUT healthy: battery.charge={result.stdout.strip()}")
            return True
        else:
            logger.warning("NUT not responding — restarting NUT services...")
            # Try instance name first (Pi: nut-driver@tdi), then generic
            for svc in ['nut-driver@tdi', 'nut-driver']:
                subprocess.run(['systemctl', 'restart', svc], check=False,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            time.sleep(3)
            subprocess.run(['systemctl', 'restart', 'nut-server'], check=False,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            time.sleep(5)  # NUT driver needs time to poll HID
            # Verify recovery
            result2 = subprocess.run(
                ['upsc', 'tdi@localhost', 'battery.charge'],
                capture_output=True, text=True, timeout=5
            )
            if result2.returncode == 0 and result2.stdout.strip():
                logger.info(f"✓ NUT recovered: battery.charge={result2.stdout.strip()}")
                return True
            else:
                logger.warning("NUT restart did not fully recover — script will use HID fallback for power data")
                return False
    except subprocess.TimeoutExpired:
        logger.warning("NUT query timed out — restarting NUT services...")
        for svc in ['nut-driver@tdi', 'nut-driver']:
            subprocess.run(['systemctl', 'restart', svc], check=False,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(3)
        subprocess.run(['systemctl', 'restart', 'nut-server'], check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return False
    except Exception as e:
        logger.debug(f"NUT check skipped: {e}")
        return False

def check_and_recover_wifi():
    """Verify WiFi connectivity and recover if the link is down.
    
    If the wireless interface has no IP or can't reach the default gateway,
    attempt reassociation. Without this, callhomes fail silently until reboot.
    Supports both wlan0 (Pi OS) and wlx... (USB dongles on Le Potato).
    """
    try:
        # Auto-detect wireless interface name (wlan0 or wlx...)
        wifi_iface = 'wlan0'  # Default
        try:
            iw_result = subprocess.run(
                ['ip', 'link', 'show'],
                capture_output=True, text=True, timeout=5
            )
            for line in iw_result.stdout.split('\n'):
                # Look for wlan0 or wlx* interfaces
                if 'wlan' in line or 'wlx' in line:
                    # Extract interface name: "3: wlx3c3300600d24: <BROADCAST..."
                    parts = line.strip().split(':')
                    if len(parts) >= 2:
                        wifi_iface = parts[1].strip()
                        break
        except Exception:
            pass
        
        # Check if the wireless interface has an IP address
        result = subprocess.run(
            ['ip', '-4', 'addr', 'show', wifi_iface],
            capture_output=True, text=True, timeout=5
        )
        has_ip = 'inet ' in result.stdout
        
        if not has_ip:
            logger.warning(f"WiFi ({wifi_iface}) has no IP address — attempting recovery...")
            # Try wpa_cli reassociate (Pi OS)
            subprocess.run(['wpa_cli', '-i', wifi_iface, 'reassociate'], check=False,
                           capture_output=True, timeout=5)
            # Try nmcli reconnect (Armbian)
            subprocess.run(['nmcli', 'dev', 'connect', wifi_iface], check=False,
                           capture_output=True, timeout=10)
            time.sleep(5)
            # Re-check
            result2 = subprocess.run(
                ['ip', '-4', 'addr', 'show', wifi_iface],
                capture_output=True, text=True, timeout=5
            )
            if 'inet ' in result2.stdout:
                logger.info("✓ WiFi recovered — IP address restored")
                return True
            else:
                logger.error("✗ WiFi recovery failed — no IP, callhome will likely fail")
                return False
        
        # Has IP — try to reach the gateway
        gw_result = subprocess.run(
            ['ip', 'route', 'show', 'default'],
            capture_output=True, text=True, timeout=5
        )
        gateway = None
        for line in gw_result.stdout.split('\n'):
            if 'default via' in line:
                gateway = line.split('via')[1].strip().split()[0]
                break
        
        if gateway:
            ping = subprocess.run(
                ['ping', '-c', '1', '-W', '3', gateway],
                capture_output=True, timeout=5
            )
            if ping.returncode == 0:
                logger.debug(f"WiFi healthy: gateway {gateway} reachable")
                return True
            else:
                logger.warning(f"Gateway {gateway} unreachable — attempting WiFi recovery...")
                subprocess.run(['wpa_cli', '-i', wifi_iface, 'reassociate'], check=False,
                               capture_output=True, timeout=5)
                subprocess.run(['nmcli', 'dev', 'connect', wifi_iface], check=False,
                               capture_output=True, timeout=10)
                return False
        
        return True  # Has IP, no gateway info — assume OK
    except Exception as e:
        logger.debug(f"WiFi check skipped: {e}")
        return True  # Don't block callhome on check failure

def check_memory():
    """Check available memory and warn/act if critically low.
    
    Pi Zero 2 W has only 512MB RAM. MSAL + JSON + serial I/O can
    consume a lot. If free memory drops below 50MB, log a warning.
    If below 20MB, try to free caches.
    """
    try:
        with open('/proc/meminfo') as f:
            meminfo = f.read()
        
        available_mb = None
        for line in meminfo.split('\n'):
            if 'MemAvailable' in line:
                # MemAvailable: 123456 kB
                available_kb = int(line.split()[1])
                available_mb = available_kb // 1024
                break
        
        if available_mb is None:
            return True
        
        if available_mb < 20:
            logger.error(f"⚠ CRITICAL: Only {available_mb}MB RAM available — dropping caches")
            # Drop page caches to free memory
            try:
                with open('/proc/sys/vm/drop_caches', 'w') as f:
                    f.write('1')
            except PermissionError:
                subprocess.run(['sh', '-c', 'echo 1 > /proc/sys/vm/drop_caches'],
                               check=False, timeout=5)
            return False
        elif available_mb < 50:
            logger.warning(f"⚠ Low memory: {available_mb}MB available (threshold: 50MB)")
            return True
        else:
            logger.debug(f"Memory OK: {available_mb}MB available")
            return True
    except Exception as e:
        logger.debug(f"Memory check skipped: {e}")
        return True

def run_health_checks():
    """Run all pre-callhome health checks.
    
    Called at the start of main() before any serial/network operations.
    All checks are non-blocking — they log warnings but never prevent
    the callhome from proceeding.
    """
    logger.info("Running pre-callhome health checks...")
    
    # 1. Hardware watchdog
    setup_hardware_watchdog()
    
    # 2. NUT
    check_and_restart_nut()
    
    # 3. WiFi
    check_and_recover_wifi()
    
    # 4. Memory
    check_memory()
    
    # 5. Low battery — shutdown to protect SD card
    check_battery_shutdown()

    # 6. Clock sync (v1.0.29)
    # Full bidirectional sync: read board RTC (D0), compare to Pi time,
    # fetch HTTPS authoritative time if drift > 60s, set Pi clock + write board.
    sync_clocks()

    logger.info("Health checks complete")

def check_battery_shutdown():
    """Check TDI battery level and trigger clean shutdown if critically low.
    
    The #1 cause of SD card corruption on SBCs is unclean shutdown from
    complete power loss. When the TDI reports battery below 10% and on
    battery power (not charging), we do one final callhome, then cleanly
    shut down to prevent filesystem damage.
    
    Threshold: 10% battery AND on battery power (not wall/utility).
    """
    SHUTDOWN_THRESHOLD = 10  # percent
    try:
        result = subprocess.run(
            ['upsc', 'tdi@localhost', 'battery.charge'],
            capture_output=True, text=True, timeout=5
        )
        if result.returncode != 0:
            return  # NUT not available, skip

        # Check battery/mains status first (independent of charge parsing)
        status_result = subprocess.run(
            ['upsc', 'tdi@localhost', 'ups.status'],
            capture_output=True, text=True, timeout=5
        )
        ups_status = status_result.stdout.strip() if status_result.returncode == 0 else ''
        on_battery = 'OB' in ups_status

        # v1.0.33: Parse charge defensively — fail-safe if on battery and can't parse
        charge = None
        try:
            charge = int(result.stdout.strip())
        except (ValueError, TypeError):
            if on_battery:
                logger.critical(
                    'CRITICAL: On battery power but cannot parse charge level '
                    '(raw: %r) — assuming critical, triggering shutdown',
                    result.stdout.strip()
                )
                CONFIG['shutdown_after_callhome'] = True
                return
            else:
                logger.warning('Could not parse battery charge (raw: %r) but on mains — ignoring',
                               result.stdout.strip())
                return

        if charge <= SHUTDOWN_THRESHOLD and on_battery:
            logger.critical(f"⚠ CRITICAL: Battery at {charge}% on battery power — initiating clean shutdown to protect SD card")
            logger.critical("This callhome will complete, then system will shut down.")
            CONFIG['shutdown_after_callhome'] = True
        elif charge <= 20 and on_battery:
            logger.warning(f"⚠ Battery low: {charge}% on battery power — monitoring")
        else:
            logger.debug(f"Battery OK: {charge}% (status: {ups_status})")
    except subprocess.TimeoutExpired:
        logger.warning("Battery shutdown check timed out — NUT unresponsive")
    except Exception as e:
        logger.debug(f"Battery shutdown check skipped: {e}")

# Module-level MSAL token cache (v1.0.31).
# Tokens are valid for ~60 minutes. Reusing a cached token saves 2-3s per cycle
# and reduces auth calls from 6×/hour to 1×/hour per cart.
_MSAL_TOKEN_CACHE = {'token': None, 'expires_at': 0.0}


def get_auth_token():
    """Get authentication token using MSAL with retry logic and module-level cache.

    Cache TTL: 55 minutes (5-minute buffer before the Azure 60-min expiry).
    Retries up to 3 times with exponential backoff to survive transient network
    errors (e.g., ConnectionResetError from TP-Link routers during low-traffic
    overnight hours).
    """
    # Return cached token if still valid
    _now = time.time()
    if _MSAL_TOKEN_CACHE['token'] and _now < _MSAL_TOKEN_CACHE['expires_at']:
        _remaining = int(_MSAL_TOKEN_CACHE['expires_at'] - _now)
        logger.info(f'Using cached MSAL token ({_remaining}s remaining)')
        return _MSAL_TOKEN_CACHE['token']

    max_attempts = 3

    for attempt in range(1, max_attempts + 1):
        try:
            app = msal.ConfidentialClientApplication(
                CONFIG['client_id'],
                authority=CONFIG['authority'],
                client_credential=CONFIG['client_secret']
            )

            logger.info(f'Acquiring fresh MSAL token (attempt {attempt}/{max_attempts})...')
            result = app.acquire_token_for_client(scopes=CONFIG['scope'])

            if 'access_token' in result:
                logger.info('Successfully acquired token')
                # Cache the token. Use expires_in from result if available,
                # otherwise assume 55-minute safe TTL.
                ttl = int(result.get('expires_in', 3600)) - 300  # 5-min safety buffer
                _MSAL_TOKEN_CACHE['token'] = result['access_token']
                _MSAL_TOKEN_CACHE['expires_at'] = time.time() + max(ttl, 300)
                return result['access_token']
            else:
                logger.error(f"Error getting token: {result.get('error')}")
                return None
        except Exception as e:
            logger.warning(f'Auth attempt {attempt}/{max_attempts} failed: {str(e)}')
            if attempt < max_attempts:
                wait_time = 5 * attempt  # 5s, 10s
                logger.info(f'Retrying in {wait_time} seconds...')
                time.sleep(wait_time)
            else:
                logger.error(f'Authentication failed after {max_attempts} attempts: {str(e)}')
                return None

def get_local_ip():
    """Get the actual local IP address (not loopback)
    
    socket.gethostbyname(hostname) returns 127.0.1.1 on Pi because of /etc/hosts.
    This uses hostname -I which returns the real interface IP.
    """
    try:
        result = subprocess.run(['hostname', '-I'], capture_output=True, text=True, timeout=5)
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip().split()[0]
    except Exception:
        pass
    try:
        # Fallback: UDP connect trick (doesn't actually send data)
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return socket.gethostbyname(socket.gethostname())

def get_wifi_info():
    """Get current WiFi connection information"""
    # Try iwconfig first (Raspberry Pi OS), then nmcli (Armbian/Le Potato)
    try:
        iwconfig_output = subprocess.check_output(["iwconfig"], text=True, stderr=subprocess.DEVNULL)
        
        ssid = None
        if 'ESSID:' in iwconfig_output:
            ssid = iwconfig_output.split('ESSID:"')[1].split('"')[0]
        
        mac = None
        if 'Access Point:' in iwconfig_output:
            mac = iwconfig_output.split('Access Point:')[1].split()[0].strip()
        
        signal = None
        if 'Signal level=' in iwconfig_output:
            signal = iwconfig_output.split('Signal level=')[1].split()[0].strip()
            signal = signal.replace('dBm', '').replace('-', '')
        
        if ssid and mac and signal:
            logger.info(f"WiFi: SSID={ssid}, MAC={mac}, Signal={signal}")
            return ssid, mac, signal
        
        return None, None, None
    except FileNotFoundError:
        # iwconfig not available (Armbian/Le Potato) — fall back to nmcli
        try:
            # Get SSID and signal from nmcli device info
            nmcli_output = subprocess.check_output(
                ["nmcli", "-t", "-f", "active,ssid,signal,bssid", "dev", "wifi", "list"],
                text=True, stderr=subprocess.DEVNULL
            )
            
            ssid, mac, signal = None, None, None
            for line in nmcli_output.strip().split('\n'):
                if line.startswith('yes:'):
                    parts = line.split(':')
                    # Format: yes:SSID:SIGNAL:BSSID (BSSID has colons, so rejoin)
                    if len(parts) >= 4:
                        ssid = parts[1]
                        signal = parts[2]
                        # BSSID is the remaining parts joined back with colons.
                        # v1.0.39: nmcli -t escapes literal colons in BSSIDs as `\:`,
                        # so naïve split+join leaves backslashes in (e.g.
                        # `A8\:6E\:84\:34\:D8\:22`). The whitelist normalization
                        # in check_ap_whitelist() only strips `:` and `-`, not `\`,
                        # so case A (current AP whitelisted) was reporting
                        # spurious AP WHITELIST VIOLATION → wasted disconnect→
                        # emergency-reconnect cycle. Fix: strip the `\:` escape
                        # so the BSSID is plain colon-separated hex.
                        mac = ':'.join(parts[3:]).strip().replace('\\:', ':').upper()
                    break
            
            if ssid and mac and signal:
                logger.info(f"WiFi (nmcli): SSID={ssid}, MAC={mac}, Signal={signal}")
                return ssid, mac, signal
            
            return None, None, None
        except Exception as e2:
            logger.error(f"Error getting WiFi info via nmcli: {str(e2)}")
            return None, None, None
    except Exception as e:
        logger.error(f"Error getting WiFi info: {str(e)}")
        return None, None, None

def load_ap_history():
    """Load AP history from persistent file
    
    Returns:
        list: List of AP strings [aP1, aP2, aP3] (most recent to oldest)
    """
    history_file = '/var/lib/hmpd/ap_history.json'
    try:
        if os.path.exists(history_file):
            with open(history_file, 'r') as f:
                import json
                data = json.load(f)
                return data.get('history', [None, None, None])
    except Exception as e:
        logger.debug(f"Could not load AP history: {e}")
    
    return [None, None, None]

def save_ap_history(history):
    """Save AP history to persistent file
    
    Args:
        history: List of AP strings [aP1, aP2, aP3]
    """
    history_file = '/var/lib/hmpd/ap_history.json'
    try:
        os.makedirs('/var/lib/hmpd', exist_ok=True)
        with open(history_file, 'w') as f:
            import json
            json.dump({'history': history}, f)
    except Exception as e:
        logger.warning(f"Could not save AP history: {e}")

def update_ap_history(current_ap):
    """Update AP history when cart moves to a new AP
    
    Args:
        current_ap: Current AP string (format: "SSID,MAC,Signal")
    
    Returns:
        tuple: (aP1, aP2, aP3) - Previous APs for semi-RTLS tracking
    """
    # Load existing history
    history = load_ap_history()  # [aP1, aP2, aP3]
    
    # Extract MAC from current AP to compare
    try:
        current_mac = current_ap.split(',')[1] if ',' in current_ap else None
    except:
        current_mac = None
    
    # Extract MAC from aP1 (most recent previous AP)
    try:
        previous_mac = history[0].split(',')[1] if history[0] and ',' in history[0] else None
    except:
        previous_mac = None
    
    # If cart moved to a different AP, update history
    if current_mac and current_mac != previous_mac:
        logger.info(f"Cart moved! Previous AP: {previous_mac} -> Current AP: {current_mac}")
        # Shift history: current AP becomes new aP1, old aP1 becomes aP2, old aP2 becomes aP3
        new_history = [
            current_ap,  # Current AP becomes new aP1 (will be "previous" on next check)
            history[0],  # Old aP1 becomes aP2
            history[1]   # Old aP2 becomes aP3 (oldest is dropped)
        ]
        # Save updated history for next time
        save_ap_history(new_history)
        # Return the history BEFORE the move (for this CallHome)
        # This shows where the cart WAS before moving to current location
        return tuple(history)
    else:
        # No movement detected, return existing history
        return tuple(history)

def load_ap_whitelist():
    """Load AP whitelist (approved BSSIDs) from persistent file.

    Returns:
        list: Approved BSSIDs in lowercase no-separator format,
              or empty list if no whitelist is configured.
    """
    try:
        if os.path.exists(CONFIG['ap_whitelist_file']):
            with open(CONFIG['ap_whitelist_file'], 'r') as f:
                data = json.load(f)
                return data.get('bssids', [])
    except Exception as e:
        logger.debug(f"Could not load AP whitelist: {e}")
    return []

def save_ap_whitelist(bssid_list):
    """Save AP whitelist to persistent file.

    Args:
        bssid_list: List of BSSID strings (normalized to lowercase, separators stripped)
    """
    try:
        os.makedirs('/var/lib/hmpd', exist_ok=True)
        normalized = [b.lower().replace(':', '').replace('-', '') for b in bssid_list if b]
        with open(CONFIG['ap_whitelist_file'], 'w') as f:
            json.dump({'bssids': normalized}, f)
        logger.info(f"AP whitelist saved: {len(normalized)} approved BSSIDs")
    except Exception as e:
        logger.warning(f"Could not save AP whitelist: {e}")

def check_ap_whitelist(current_mac):
    """Check if current AP BSSID is in the configured whitelist.

    Args:
        current_mac: Current AP MAC address (any format)

    Returns:
        tuple: (is_compliant, whitelist_active)
            is_compliant: True if AP is approved or no whitelist configured
            whitelist_active: True if a non-empty whitelist exists
    """
    whitelist = load_ap_whitelist()

    if not whitelist:
        return (True, False)  # No whitelist configured — always compliant

    if not current_mac:
        logger.warning("AP whitelist is active but no BSSID could be read")
        return (False, True)

    mac_normalized = current_mac.lower().replace(':', '').replace('-', '')
    is_compliant = mac_normalized in whitelist

    if is_compliant:
        logger.info(f"AP whitelist: BSSID {current_mac} is approved")
    else:
        logger.warning(f"AP WHITELIST VIOLATION: BSSID {current_mac} not in approved list ({len(whitelist)} entries)")

    return (is_compliant, True)

def create_ap_whitelist_report(current_mac, is_compliant=None, whitelist_active=None):
    """Build optional Fleet Manager diagnostic fields for AP assignment state."""
    if is_compliant is None or whitelist_active is None:
        is_compliant, whitelist_active = check_ap_whitelist(current_mac)

    whitelist = load_ap_whitelist()
    normalized_current = None
    if current_mac:
        normalized_current = current_mac.lower().replace(':', '').replace('-', '')

    violation = bool(whitelist_active and not is_compliant)
    return {
        "apWhitelistActive": bool(whitelist_active),
        "apWhitelistCompliant": bool(is_compliant),
        "apWhitelistViolation": violation,
        "apWhitelistViolationType": "not_assigned_to_cart_location" if violation else None,
        "apWhitelistCurrentBSSID": normalized_current,
        "apWhitelistApprovedCount": len(whitelist),
    }

def load_cart_type_state():
    """Load the last reliable G0 identity.

    E3 CDC-ACM framing can intermittently return only "Car" for G0. When that
    happens, a previous complete G0 is safer than silently downgrading a Pro
    cart to E2 for the rest of the callhome run.
    """
    try:
        path = CONFIG['cart_type_state_file']
        if os.path.exists(path):
            with open(path, 'r') as f:
                data = json.load(f) or {}
            if data.get('cart_type') in ('E2', 'E3'):
                return data
    except Exception as e:
        logger.debug(f"Could not load cart type state: {e}")
    return {}

def save_cart_type_state(cart_type, cart_id=None, firmware_version=None, raw_g0=None):
    """Persist the last complete G0 identity for partial-response recovery."""
    if cart_type not in ('E2', 'E3'):
        return
    try:
        os.makedirs(os.path.dirname(CONFIG['cart_type_state_file']), exist_ok=True)
        with open(CONFIG['cart_type_state_file'], 'w') as f:
            json.dump({
                'cart_type': cart_type,
                'cart_id': cart_id,
                'firmware_version': firmware_version,
                'raw_g0': raw_g0,
                'updated_at': datetime.now(timezone.utc).isoformat(),
            }, f, indent=2)
    except Exception as e:
        logger.debug(f"Could not save cart type state: {e}")

def restore_cart_type_from_state(reason):
    """Restore CONFIG cart identity from the last known complete G0, if any."""
    state = load_cart_type_state()
    state_type = state.get('cart_type')
    if state_type in ('E2', 'E3'):
        CONFIG['cart_type'] = state_type
        if CONFIG.get('cart_id') == 'UNKNOWN' and state.get('cart_id'):
            CONFIG['cart_id'] = state.get('cart_id')
        logger.warning(
            f"{reason}; using last known cart_type={state_type} "
            f"cart_id={state.get('cart_id') or CONFIG.get('cart_id')}"
        )
        return True
    return False

HELP_REQUEST_MESSAGES = {
    '1': 'Break Fix - Cart',
    '2': 'Break Fix - PC',
    '3': 'IT Request',
    '4': 'Pharmacy Restock',
    '5': 'Housekeeping',
    '6': 'Other',
}
_HELP_REQUEST_RE = re.compile(r'^\s*E3\s+(\S+)\s+(\S+)\s+([1-6])\s*$')

def parse_e3_help_request_line(line):
    """Parse Build126 help-request serial events.

    Firmware format from Mike: "E3 <CartModel> <Serial> <MessageID>".
    ServiceNow/backend posting is intentionally separate until Fleet Manager's
    ingest contract is confirmed.
    """
    if not line:
        return None
    clean = ''.join(ch for ch in line.strip() if ch.isprintable() or ch in '\t ')
    match = _HELP_REQUEST_RE.match(clean)
    if not match:
        return None
    cart_model, serial_number, message_id = match.groups()
    return {
        'eventType': 'E3HelpRequest',
        'cartModel': cart_model,
        'cartSerial': serial_number,
        'messageId': message_id,
        'message': HELP_REQUEST_MESSAGES.get(message_id, 'Other'),
        'raw': clean,
    }

def queue_e3_help_request(event):
    """Append a parsed E3 help request to a local queue for backend upload."""
    try:
        os.makedirs(os.path.dirname(CONFIG['help_request_queue_file']), exist_ok=True)
        now_utc = datetime.now(timezone.utc)
        dedupe_bucket = now_utc.strftime('%Y%m%dT%H%M')
        event = dict(event)
        event.update({
            'timestampUtc': now_utc.isoformat(),
            'hostname': socket.gethostname(),
            'facilityId': CONFIG.get('facility_id'),
            'cartId': CONFIG.get('cart_id'),
            'source': 'e3_serial',
            'status': 'pending_backend_contract',
        })
        event['dedupeKey'] = hashlib.sha1(
            f"{event.get('raw')}|{event.get('cartSerial')}|{event.get('messageId')}|{dedupe_bucket}".encode()
        ).hexdigest()

        events = []
        path = CONFIG['help_request_queue_file']
        if os.path.exists(path):
            try:
                with open(path, 'r') as f:
                    loaded = json.load(f)
                events = loaded.get('events', loaded if isinstance(loaded, list) else [])
            except Exception:
                events = []

        if any(e.get('dedupeKey') == event['dedupeKey'] for e in events[-25:]):
            logger.debug(f"E3 help request already queued for this minute: {event.get('raw')}")
            return True

        events.append(event)
        events = events[-200:]
        with open(path, 'w') as f:
            json.dump({'events': events}, f, indent=2)

        logger.info(
            f"✓ E3 help request queued: {event['messageId']} "
            f"({event['message']}) serial={event['cartSerial']}"
        )
        return True
    except Exception as e:
        logger.warning(f"Could not queue E3 help request: {e}")
        return False

def capture_e3_help_requests(raw_text):
    """Find and queue E3 help-request lines in any serial text block."""
    if not raw_text:
        return []
    captured = []
    for line in re.split(r'[\r\n]+', raw_text):
        event = parse_e3_help_request_line(line)
        if event:
            queue_e3_help_request(event)
            captured.append(event)
    return captured

# ============================================================
# SERIAL CONNECTION MANAGER (v1.0.32)
# ============================================================

class E2Serial:
    """Context manager for E2/E3 board serial connection.

    Opens the serial port once; all commands within the block share
    the connection.  Reduces USB open/close churn from 10-13 per cycle
    to 2-3 (one read phase, one write phase, one for clock sync).

    Usage:
        with E2Serial() as ser:
            data = read_e2_board_command(ser, 'G0')
            send_e2_write_command('D1...', ser=ser)
    """
    def __init__(self, port=None, baudrate=None, timeout=2):
        self.port = port or CONFIG['e2_serial_port']
        self.baudrate = baudrate or CONFIG['e2_baudrate']
        self.timeout = timeout
        self.ser = None

    def __enter__(self):
        self.ser = serial.Serial(
            port=self.port,
            baudrate=self.baudrate,
            timeout=self.timeout
        )
        time.sleep(0.5)
        try:
            if self.ser.in_waiting:
                pending = self.ser.read(self.ser.in_waiting).decode('utf-8', errors='ignore')
                capture_e3_help_requests(pending)
        except Exception as e:
            logger.debug(f"Could not inspect pending serial data: {e}")
        self.ser.reset_input_buffer()
        self.ser.reset_output_buffer()
        return self.ser

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.ser and self.ser.is_open:
            try:
                self.ser.close()
            except Exception:
                pass
        return False  # Don't suppress exceptions

def read_e2_board_command(ser, command, timeout=1):
    """Send command to E2 board and read response"""
    try:
        # Clear buffer before sending command
        try:
            if ser.in_waiting:
                pending = ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                capture_e3_help_requests(pending)
        except Exception as e:
            logger.debug(f"Could not inspect pending serial data before {command}: {e}")
        ser.reset_input_buffer()
        time.sleep(0.1)
        
        # Send command
        ser.write(f"{command}\r\n".encode())
        ser.flush()  # Ensure command is sent
        time.sleep(0.5)
        
        # Read response - keep reading until we have a complete response
        # E3 boards send data in multiple USB frames with unpredictable gaps
        response = ""
        start_time = time.time()
        no_data_count = 0
        while time.time() - start_time < timeout:
            if ser.in_waiting:
                response += ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                no_data_count = 0  # Reset counter when data received
                time.sleep(0.05)
            else:
                no_data_count += 1
                time.sleep(0.1)
                # Only exit on silence if we have a complete response (contains tab = multi-field)
                # or if we've waited long enough with no data at all
                if no_data_count > 5 and ('\t' in response or no_data_count > 15):
                    break

        capture_e3_help_requests(response)
        
        # Clean response more aggressively
        # Remove command echo, control characters, and empty lines
        lines = response.strip().split('\n')
        cleaned = []
        for line in lines:
            line = line.strip()
            # Skip empty lines, command echo, and lines that are just the command
            if line and line.rstrip('\r') != command:
                # Remove any remaining control characters
                line = ''.join(char for char in line if char.isprintable() or char in '\r\n\t')
                if line:
                    cleaned.append(line)
        
        return '\n'.join(cleaned) if cleaned else ""
        
    except Exception as e:
        logger.error(f"Error reading E2 command {command}: {str(e)}")
        return ""

def send_e2_write_command(command, expected_response=None, timeout=3, ser=None):
    """Send write command to E2 board and verify response

    Args:
        command: E2 command to send (without \r\n)
        expected_response: Optional expected response (e.g., 'OK')
        timeout: Timeout in seconds
        ser: Optional shared serial connection (from E2Serial context manager).
             If None, opens and closes its own connection.

    Returns:
        (success, response_data) tuple
    """
    owns_connection = ser is None
    try:
        logger.info(f"Sending E2 write command: {command}")

        if owns_connection:
            ser = serial.Serial(
                port=CONFIG['e2_serial_port'],
                baudrate=CONFIG['e2_baudrate'],
                timeout=timeout
            )
            time.sleep(0.2)

        # Clear buffers
        try:
            if ser.in_waiting:
                pending = ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                capture_e3_help_requests(pending)
        except Exception as e:
            logger.debug(f"Could not inspect pending serial data before write {command}: {e}")
        ser.reset_input_buffer()
        ser.reset_output_buffer()

        # Send command
        ser.write(f"{command}\r\n".encode())
        ser.flush()
        time.sleep(0.3)

        # Read echo (E2 board echoes the command back)
        echo = ""
        start_time = time.time()
        while time.time() - start_time < 1:
            if ser.in_waiting:
                echo += ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                time.sleep(0.1)
            else:
                time.sleep(0.1)
                if echo:
                    break

        echo = echo.strip()
        capture_e3_help_requests(echo)
        logger.debug(f"E2 echo: {repr(echo)}")

        # Check if echo matches command (some commands echo, some don't)
        if echo and command not in echo:
            logger.warning(f"Echo mismatch: expected '{command}' in echo, got '{echo}'")

        # Read response if expected
        response_data = None
        if expected_response:
            response = ""
            start_time = time.time()
            while time.time() - start_time < timeout:
                if ser.in_waiting:
                    response += ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                    time.sleep(0.1)
                else:
                    time.sleep(0.1)
                    if response:
                        break

            response_data = response.strip()
            capture_e3_help_requests(response_data)
            logger.debug(f"E2 response: {repr(response_data)}")

            if expected_response not in response_data:
                logger.warning(f"Expected response '{expected_response}' not found in '{response_data}'")
                if owns_connection:
                    ser.close()
                return (False, response_data)

        if owns_connection:
            ser.close()
        logger.info(f"✓ E2 write command successful: {command}")
        return (True, response_data)

    except Exception as e:
        logger.error(f"✗ E2 write command failed: {command} - {str(e)}")
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass
        return (False, None)

def read_e2_board_time(ser=None):
    """Read current time from E2/E3 board RTC via D0 command.

    Confirmed by live probe (2026-04-13):
      D0 → b'D0\\r\\t11111111\\t2604131200\\r\\r'
      Format: \\t CartID \\t YYMMDDHHMM

    Board stores LOCAL time (not UTC). Resolution: 1 minute.
    Sanity-checked: if year < 2020, board RTC is uninitialized (new cart).

    Args:
        ser: Optional shared serial connection (from E2Serial context manager).
             If None, opens and closes its own connection.

    Returns:
        datetime (local, naive, seconds=0) or None if unavailable / uninitialized
    """
    owns_connection = ser is None
    try:
        if owns_connection:
            ser = serial.Serial(
                port=CONFIG['e2_serial_port'],
                baudrate=CONFIG['e2_baudrate'],
                timeout=2
            )
            time.sleep(0.5)  # E3 needs longer settle than E2
            ser.reset_input_buffer()
            ser.reset_output_buffer()

        # Try D0 first (confirmed working on both E2 and E3 in sequence probe)
        ser.write(b'D0\r\n')
        ser.flush()

        # Gap-tolerant read loop: keeps reading until 0.5s of silence after data
        raw = b''
        start = time.time()
        no_data_count = 0
        while time.time() - start < 3.0:
            n = ser.in_waiting
            if n:
                raw += ser.read(n)
                no_data_count = 0
                time.sleep(0.05)
            else:
                no_data_count += 1
                time.sleep(0.1)
                if raw and no_data_count > 5:
                    break  # 0.5s silence after receiving data — done

        # If D0 returned nothing, try E0 (same data on some firmware versions)
        if not raw.strip():
            ser.reset_input_buffer()
            ser.write(b'E0\r\n')
            ser.flush()
            raw = b''
            start = time.time()
            no_data_count = 0
            while time.time() - start < 3.0:
                n = ser.in_waiting
                if n:
                    raw += ser.read(n)
                    no_data_count = 0
                    time.sleep(0.05)
                else:
                    no_data_count += 1
                    time.sleep(0.1)
                    if raw and no_data_count > 5:
                        break
            logger.debug('read_e2_board_time: D0 empty, used E0 fallback')

        if owns_connection:
            ser.close()

        # Find the 10-digit YYMMDDHHMM pattern (last one wins — CartID is 8 digits)
        text = raw.decode('utf-8', errors='ignore')
        matches = re.findall(r'\d{10}', text)
        if not matches:
            logger.debug('read_e2_board_time: no 10-digit field found: ' + repr(text[:80]))
            return None

        dt_str = matches[-1]  # take LAST 10-digit match (datetime, not CartID)
        yy = int(dt_str[0:2])
        mm = int(dt_str[2:4])
        dd = int(dt_str[4:6])
        hh = int(dt_str[6:8])
        mi = int(dt_str[8:10])
        year = 2000 + yy

        if year < 2020:
            logger.warning('read_e2_board_time: board RTC not initialized (year=' + str(year) + ')')
            return None

        board_dt = datetime(year, mm, dd, hh, mi, 0)
        logger.info('Board RTC (D0): ' + board_dt.strftime('%Y-%m-%d %H:%M'))
        return board_dt

    except Exception as e:
        logger.debug('read_e2_board_time failed (non-fatal): ' + str(e))
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass
        return None



def fetch_authoritative_time():
    """Fetch current local time via HTTPS — 3-tier fallback chain.

    Uses TCP 443 (HTTPS) instead of UDP 123 (NTP) because hospital firewalls
    routinely block NTP. If the SBC can call home to Azure, these work too.

    Tier 1: worldtimeapi.org/api/ip
        Returns timezone-aware local time based on the cart's IP geolocation.
        Best source: gives correct timezone automatically per hospital location.

    Tier 2: time.cloudflare.com Date header
        Pure UTC converted to local time. Highly available.

    Tier 3: login.microsoftonline.com Date header
        The Azure endpoint we already talk to. If this fails, callhome fails
        anyway — so time sync failure and callhome failure are the same event.

    Returns:
        datetime (local, naive) or None if all three tiers fail
    """
    from email.utils import parsedate_to_datetime as _parse_rfc2822

    # Tier 1: WorldTimeAPI — location-aware local time
    try:
        resp = requests.get('https://worldtimeapi.org/api/ip', timeout=8)
        if resp.status_code == 200:
            data = resp.json()
            dt_str = data.get('datetime', '')
            if dt_str:
                # '2026-04-13T12:03:02.123456-05:00' → take first 19 chars
                dt = datetime.fromisoformat(dt_str[:19])
                logger.info('HTTPS time (worldtimeapi.org): ' + str(dt))
                return dt
    except Exception as _e:
        logger.debug('HTTPS time: worldtimeapi.org failed: ' + str(_e))

    # Tier 2: Cloudflare Date header (UTC → local)
    try:
        resp = requests.head('https://time.cloudflare.com', timeout=5)
        date_hdr = resp.headers.get('Date', '')
        if date_hdr:
            dt_utc = _parse_rfc2822(date_hdr)
            dt_local = dt_utc.astimezone().replace(tzinfo=None)
            logger.info('HTTPS time (Cloudflare): ' + str(dt_local))
            return dt_local
    except Exception as _e:
        logger.debug('HTTPS time: Cloudflare failed: ' + str(_e))

    # Tier 3: Azure login endpoint Date header
    try:
        resp = requests.head('https://login.microsoftonline.com', timeout=5)
        date_hdr = resp.headers.get('Date', '')
        if date_hdr:
            dt_utc = _parse_rfc2822(date_hdr)
            dt_local = dt_utc.astimezone().replace(tzinfo=None)
            logger.info('HTTPS time (Azure): ' + str(dt_local))
            return dt_local
    except Exception as _e:
        logger.debug('HTTPS time: Azure endpoint failed: ' + str(_e))

    logger.warning('HTTPS time: all three tiers failed — cannot fetch authoritative time')
    return None


def sync_clocks():
    """Bidirectional clock sync: board RTC ↔ Pi system clock ↔ HTTPS time.

    Flow every callhome cycle:
      1. Read board RTC via D0
      2. Compare to Pi system time
      3. If delta > 60s OR board uninitialized (new cart):
           a. Fetch authoritative time via HTTPS (3-tier)
           b. Set Pi system clock  (date --set)
           c. Write corrected time to board via D1
           d. Update last_known_time on disk
      4. Log drift for diagnostics; always non-fatal

    Replaces the old e2_time_synced one-shot flag logic:
      - New cart (board year < 2020) triggers sync automatically
      - Long-idle cart (large delta) re-syncs on next callhome
      - Healthy cart: just logs 'clocks in sync (drift=Xs)'
    """
    DRIFT_THRESHOLD = 60  # seconds
    logger.info('CLOCK SYNC: checking Pi ↔ board drift...')

    try:
        # v1.0.32: Single serial connection for both D0 read and D1 write
        with E2Serial() as ser:
            board_dt = read_e2_board_time(ser=ser)
            pi_dt    = datetime.now()

            needs_sync   = False
            drift_seconds = None

            if board_dt is None:
                logger.warning('CLOCK SYNC: board RTC uninitialized or unreadable — sync needed')
                needs_sync = True
            else:
                drift_seconds = int(abs((pi_dt - board_dt).total_seconds()))
                if drift_seconds > DRIFT_THRESHOLD:
                    logger.warning(
                        'CLOCK SYNC: drift=' + str(drift_seconds) + 's '
                        '(Pi=' + pi_dt.strftime('%Y-%m-%d %H:%M') + ' '
                        'Board=' + board_dt.strftime('%Y-%m-%d %H:%M') + ') '
                        '— threshold=' + str(DRIFT_THRESHOLD) + 's, syncing'
                    )
                    needs_sync = True
                else:
                    logger.info('CLOCK SYNC: in sync (drift=' + str(drift_seconds) + 's) — no action needed')

            if not needs_sync:
                # Still update last_known_time so boot restore has a fresh reference
                try:
                    with open('/var/lib/hmpd/last_known_time', 'w') as _f:
                        _f.write(pi_dt.strftime('%Y-%m-%dT%H:%M:%S') + '\n')
                except Exception:
                    pass
                return

            # Fetch authoritative time via HTTPS
            auth_time = fetch_authoritative_time()

            if auth_time is None:
                # v1.0.42 (restored v1.0.45 after a v1.0.43/44 regression): Board
                # RTC fallback. On fresh Le Potato boots the Pi comes up with a
                # stale clock (no battery-backed Pi RTC; kernel time is whatever
                # the filesystem mtime / image-build-date says — typically months
                # in the past). HTTPS time-sync then fails on TLS cert validation
                # ("certificate is not yet valid"), and falling back to the wrong
                # Pi clock makes Azure JWT acquisition fail the same way.
                #
                # The E2/E3 board has a battery-backed RTC. If we have a board
                # reading AND it's not wildly far from the Pi clock (which would
                # indicate a corrupt board RTC or a battery that died and got
                # re-set to a far-future value), prefer it. The 2-year sanity
                # bound is conservative; read_e2_board_time already rejects
                # year < 2020. NOTE: a fresh E3 whose RTC is itself uninitialized
                # returns board_dt=None and this cannot fire — that case is
                # covered at provision time by manual_setup.py set_clock_from_usb.
                BOARD_RTC_SANITY_BOUND_SECONDS = 2 * 365 * 24 * 3600
                if (board_dt is not None and
                        abs((board_dt - pi_dt).total_seconds()) < BOARD_RTC_SANITY_BOUND_SECONDS):
                    logger.info(
                        'CLOCK SYNC: HTTPS unavailable; using battery-backed board RTC '
                        'as authoritative (board=' + board_dt.strftime('%Y-%m-%d %H:%M') + ')'
                    )
                    auth_time = board_dt
                    # Fall through into the "Got authoritative time" block — sets
                    # Pi clock from board_dt, rewrites board RTC (idempotent at
                    # 1-min resolution), and persists last_known_time so the next
                    # callhome can compute skew correctly.
                else:
                    logger.warning('CLOCK SYNC: HTTPS time unavailable; using Pi clock as best-effort')

                    # v1.0.38: Distinguish "network down" from "clock so wrong that JWT
                    # acquisition will fail". Cross-check Pi clock against last_known_time
                    # (written at the end of every successful sync). If the delta is
                    # large, MSAL will reject the next token as expired/skewed and the
                    # callhome will fail — that failure should be logged as a clock issue,
                    # not as a generic network error.
                    try:
                        with open('/var/lib/hmpd/last_known_time', 'r') as _lkf:
                            _last_known = datetime.fromisoformat(_lkf.read().strip())
                        _skew_seconds = abs((datetime.now() - _last_known).total_seconds())
                        if _skew_seconds > 300:  # 5 min — well inside Azure JWT clock-skew tolerance is ±5 min
                            logger.warning(
                                f'CLOCK SYNC: clock skew detected (Pi vs last_known_time = '
                                f'{int(_skew_seconds)}s) — JWT acquisition will likely fail this run'
                            )
                    except (FileNotFoundError, ValueError):
                        pass  # No last_known_time yet (fresh cart) — can't compare

                    if board_dt is None:
                        try:
                            ts = datetime.now().strftime('%y%m%d%H%M%S')
                            send_e2_write_command('D1' + ts, ser=ser)
                            logger.info('CLOCK SYNC: wrote Pi clock to board (best-effort, no HTTPS)')
                        except Exception:
                            pass
                    return

            # --- Got authoritative time ---
            time_fmt = auth_time.strftime('%Y-%m-%d %H:%M:%S')

            # 1. Set Pi system clock
            try:
                result = subprocess.run(
                    ['date', '--set', time_fmt],
                    capture_output=True, text=True, timeout=5
                )
                if result.returncode == 0:
                    logger.info('CLOCK SYNC: Pi clock set to ' + time_fmt)
                else:
                    logger.warning('CLOCK SYNC: date --set failed: ' + result.stderr.strip())
            except Exception as _e:
                logger.warning('CLOCK SYNC: could not set Pi clock: ' + str(_e))

            # 2. Write corrected time to NXP board via D1 (local time format YYMMDDHHMMSS)
            try:
                board_ts = auth_time.strftime('%y%m%d%H%M%S')
                success, _ = send_e2_write_command('D1' + board_ts, ser=ser)
                if success:
                    logger.info('CLOCK SYNC: board RTC set to ' + time_fmt)
                else:
                    logger.warning('CLOCK SYNC: D1 write to board failed')
            except Exception as _e:
                logger.warning('CLOCK SYNC: could not write board RTC: ' + str(_e))

            # 3. Persist authoritative time as last_known_time (boot restore reference)
            try:
                os.makedirs('/var/lib/hmpd', exist_ok=True)
                with open('/var/lib/hmpd/last_known_time', 'w') as _f:
                    _f.write(auth_time.strftime('%Y-%m-%dT%H:%M:%S') + '\n')
            except Exception:
                pass

            # 4. Also kick chrony to fine-tune after we set the clock
            try:
                subprocess.run(['chronyc', 'makestep'], capture_output=True, timeout=5)
            except Exception:
                pass

    except serial.SerialException as _se:
        logger.warning('CLOCK SYNC: serial port unavailable (non-fatal): ' + str(_se))
    except Exception as _e:
        logger.error('CLOCK SYNC: unexpected error (non-fatal): ' + str(_e))

def apply_cart_profile(profile, cart_id=None, asset_tag=None, ser=None):
    """Apply cart profile settings to E2 board

    Args:
        profile: CartProfile object from Azure response
        cart_id: Cart ID to set
        asset_tag: Asset tag (not written to E2, just logged)
        ser: Optional shared serial connection (from E2Serial context manager)

    Returns:
        True if successful, False otherwise
    """
    try:
        logger.info("=" * 60)
        logger.info("APPLYING CART PROFILE FROM AZURE")
        logger.info("=" * 60)
        
        if cart_id:
            logger.info(f"Cart ID: {cart_id}")
        if asset_tag:
            logger.info(f"Asset Tag: {asset_tag}")
        
        logger.info(f"Profile Name: {profile.get('name', 'N/A')}")
        logger.info(f"Relock Timer: {profile.get('relockTimer', 'N/A')} seconds")
        logger.info(f"Pharmacy Code: {profile.get('pharmacyCode', 'N/A')}")
        logger.info(f"Manager Code: {profile.get('managerCode', 'N/A')}")
        logger.info(f"Narcotic Code: {profile.get('narcCode', 'N/A')}")
        logger.info(f"Sync Time to Host: {profile.get('syncTime', False)}")
        logger.info(f"Power Log Enabled: {profile.get('powerLogEnabled', False)}")
        
        # Console-friendly summary
        print("\n" + "="*70)
        print("📋 CART PROFILE UPDATE FROM AZURE")
        print("="*70)
        print(f"Profile: {profile.get('name', 'N/A')}")
        print(f"Relock Timer: {profile.get('relockTimer', 'N/A')} seconds")
        print(f"Pharmacy Code: {profile.get('pharmacyCode', 'N/A')}")
        print(f"Manager Code: {profile.get('managerCode', 'N/A')}")
        print(f"Narcotic Code: {profile.get('narcCode', 'N/A')}")
        print("="*70 + "\n")
        
        success_count = 0
        total_commands = 0
        
        # Set Cart ID (I1 command)
        if cart_id:
            total_commands += 1
            success, _ = send_e2_write_command(f"I1{cart_id}", ser=ser)
            if success:
                logger.info(f"✓ Cart ID set to: {cart_id}")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to set Cart ID")
            time.sleep(0.2)

        # Set Pharmacy Code (P1 command)
        if profile.get('pharmacyCode'):
            total_commands += 1
            success, _ = send_e2_write_command(f"P1{profile['pharmacyCode']}", ser=ser)
            if success:
                logger.info(f"✓ Pharmacy code set to: {profile['pharmacyCode']}")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to set Pharmacy code")
            time.sleep(0.2)

        # Set Manager Code (M1 command)
        if profile.get('managerCode'):
            total_commands += 1
            success, _ = send_e2_write_command(f"M1{profile['managerCode']}", ser=ser)
            if success:
                logger.info(f"✓ Manager code set to: {profile['managerCode']}")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to set Manager code")
            time.sleep(0.2)

        # Set Narcotic Code (N1 command)
        if profile.get('narcCode'):
            total_commands += 1
            success, _ = send_e2_write_command(f"N1{profile['narcCode']}", ser=ser)
            if success:
                logger.info(f"✓ Narcotic code set to: {profile['narcCode']}")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to set Narcotic code")
            time.sleep(0.2)

        # Set Relock Timer (T1 command) - E2 board echoes command but does NOT send OK
        # Following Windows service pattern: wait for echo only, no OK expected
        if profile.get('relockTimer'):
            total_commands += 1
            success, response = send_e2_write_command(f"T1{profile['relockTimer']}", expected_response=None, ser=ser)
            if success:
                logger.info(f"✓ Relock timer set to: {profile['relockTimer']} seconds")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to set Relock timer")
            time.sleep(0.2)

        # Sync Time to Host (D1 command) - if syncTime is enabled
        if profile.get('syncTime', False):
            total_commands += 1
            now = datetime.now()
            time_str = now.strftime("%y%m%d%H%M%S")
            success, response = send_e2_write_command(f"D1{time_str}", ser=ser)
            if success:
                logger.info(f"✓ E2 board time synced to: {now.strftime('%Y-%m-%d %H:%M:%S')}")
                success_count += 1
            else:
                logger.warning(f"✗ Failed to sync E2 board time")
            time.sleep(0.2)
        
        logger.info("=" * 60)
        logger.info(f"CART PROFILE SYNC COMPLETE: {success_count}/{total_commands} commands successful")
        logger.info("=" * 60)
        
        # Console-friendly result
        print("\n" + "="*70)
        if success_count == total_commands:
            print(f"✅ PROFILE SYNC: {success_count}/{total_commands} SUCCESSFUL")
        else:
            print(f"⚠️  PROFILE SYNC: {success_count}/{total_commands} SUCCESSFUL ({total_commands - success_count} failed)")
        print("="*70 + "\n")
        
        return success_count == total_commands
        
    except Exception as e:
        logger.error(f"Failed to apply cart profile: {str(e)}")
        logger.exception("Full traceback:")
        return False


# ============================================================
# BEACON (E3 task-light) — server-driven, dedup against last-sent state
# ============================================================

_BEACON_CMD_RE = re.compile(r'^Y[0-9]$')
_BEACON_COLOR_TO_CMD = {
    'off': 'Y0',
    'none': 'Y0',
    'clear': 'Y0',
    'remove': 'Y0',
    'green': 'Y1',
    'blue': 'Y2',
    'red': 'Y3',
    'purple': 'Y4',
    'lime': 'Y5',
    'orange': 'Y6',
    'yellow': 'Y7',
    'pink': 'Y8',
    'teal': 'Y9',
}


def _read_beacon_state():
    try:
        with open(BEACON_STATE_FILE) as f:
            return json.load(f) or {}
    except Exception:
        return {}


def _write_beacon_state(cmd):
    try:
        os.makedirs(os.path.dirname(BEACON_STATE_FILE), exist_ok=True)
        with open(BEACON_STATE_FILE, 'w') as f:
            json.dump({
                'last_command': cmd,
                'last_command_at': datetime.now(timezone.utc).isoformat(),
            }, f, indent=2)
    except Exception as e:
        logger.warning(f"Could not write beacon state: {e}")


def apply_beacon_command(beacon_cmd, ser=None):
    """Send a beacon command to the E3 task light.

    Designed for the "find this cart" UX: hospital operator clicks a button
    in Fleet Manager, server sets cartProfile.beacon/findMeBeacon to either
    "Y3" or a Fleet UI color such as "red", Pi gets it on next callhome and
    lights up the cart's task light. Operator clicks "stop" → server sets
    beacon to "Y0" or an empty/remove value, Pi turns off.

    Why dedup: the firmware holds the LED in the last-commanded state
    continuously. Re-sending the same command every callhome (a) wastes a
    serial write and (b) hits the rapid-Y firmware bug we saw on Build 123
    when several Y commands fire too close together. We persist the last
    sent command in BEACON_STATE_FILE and only act on changes.

    E3-only — caller must gate on CONFIG['cart_type'] == 'E3'.

    Args:
        beacon_cmd: server-supplied string. Accepts Y0-Y9 or Fleet UI color names.
        ser: shared serial connection from the surrounding E2Serial block.

    Returns:
        True on success or no-op (no change / no command).
        False on send failure.
    """
    if beacon_cmd is None:
        return True

    raw_beacon_cmd = str(beacon_cmd).strip()
    if raw_beacon_cmd == '':
        raw_beacon_cmd = 'Y0'

    normalized_cmd = raw_beacon_cmd.upper()
    if not _BEACON_CMD_RE.match(normalized_cmd):
        normalized_cmd = _BEACON_COLOR_TO_CMD.get(raw_beacon_cmd.lower(), '')

    if not normalized_cmd or not _BEACON_CMD_RE.match(normalized_cmd):
        logger.warning(
            f"Invalid beacon command from server: {beacon_cmd!r} "
            "(must match Y0-Y9 or a known Fleet color). Ignoring."
        )
        return True  # don't fail the cycle on bad server data

    state = _read_beacon_state()
    last_cmd = state.get('last_command')
    if last_cmd == normalized_cmd:
        logger.debug(f"Beacon already at {normalized_cmd}; no-op")
        return True

    success, _ = send_e2_write_command(normalized_cmd, expected_response=None, ser=ser)
    if not success:
        logger.warning(f"✗ Failed to send beacon command {normalized_cmd}")
        return False

    logger.info(f"✓ Beacon: {last_cmd!r} → {normalized_cmd} (from {beacon_cmd!r})")
    _write_beacon_state(normalized_cmd)
    return True

def _read_roaming_alert_state():
    try:
        with open(CONFIG['roaming_alert_state_file']) as f:
            return json.load(f) or {}
    except Exception:
        return {}

def _write_roaming_alert_state(command, alert_active):
    try:
        os.makedirs(os.path.dirname(CONFIG['roaming_alert_state_file']), exist_ok=True)
        with open(CONFIG['roaming_alert_state_file'], 'w') as f:
            json.dump({
                'last_command': command,
                'alert_active': bool(alert_active),
                'last_command_at': datetime.now(timezone.utc).isoformat(),
            }, f, indent=2)
    except Exception as e:
        logger.warning(f"Could not write roaming alert state: {e}")

def apply_roaming_alert_command(alert_active, ser=None):
    """Send Build126 E3 roaming alert command.

    C1 tells the cart firmware that the current AP is not on the assigned
    whitelist, causing the operator-facing beep/OLED alert. C0 clears the
    alert once the cart is back on an approved AP or the whitelist is inactive.
    """
    desired_cmd = 'C1' if alert_active else 'C0'
    state = _read_roaming_alert_state()
    if state.get('last_command') == desired_cmd:
        logger.debug(f"Roaming alert already at {desired_cmd}; no-op")
        return True

    success, _ = send_e2_write_command(desired_cmd, expected_response=None, ser=ser)
    if not success:
        logger.warning(f"✗ Failed to send roaming alert command {desired_cmd}")
        return False

    logger.info(f"✓ Roaming alert command sent: {state.get('last_command')!r} → {desired_cmd}")
    _write_roaming_alert_state(desired_cmd, alert_active)
    return True


def write_users_to_e2_board(cart_users, cart_type=None, ser=None):
    """Write user list to E2/E3 board via U1 command

    Automatically adapts the U1 format based on cart type:
    - E2: 4-field format (UserID, UserName, Group, NarcAccess)
    - E3 (Care Pro): 6-field format (adds StandPos, SeatPos for height presets)

    Args:
        cart_users: List of user objects from Azure response
                   Each user has: userId, userName, narcAccess (boolean),
                   and optionally: prefWsfcStand, prefWsfcSit (height positions)
        cart_type: 'E2' or 'E3' — if None, reads from CONFIG
        ser: Optional shared serial connection (from E2Serial context manager)

    Returns:
        True if successful, False otherwise
    """
    if cart_type is None:
        cart_type = CONFIG.get('cart_type', 'E2')
    
    is_e3 = (cart_type == 'E3')
    
    try:
        logger.info("=" * 60)
        logger.info(f"WRITING USER LIST TO {cart_type} BOARD")
        if is_e3:
            logger.info("Mode: E3 (Care Pro) — 6-field format with height presets")
        else:
            logger.info("Mode: E2 — 4-field format (no height data)")
        logger.info("=" * 60)
        logger.info(f"Users to write: {len(cart_users)}")
        
        # Console-friendly user list
        print("\n" + "="*70)
        print(f"👥 USER SYNC: {len(cart_users)} users from Azure ({cart_type} format)")
        print("="*70)
        for idx, user in enumerate(cart_users, 1):
            narc = "🔒 Narc" if user.get('narcAccess', False) else "   "
            if is_e3:
                stand = user.get('prefWsfcStand', 0)
                sit = user.get('prefWsfcSit', 0)
                height_info = f" Stand:{stand} Sit:{sit}" if stand or sit else ""
            else:
                height_info = ""
            print(f"{idx}. {user.get('userId', '????')} - {user.get('userName', 'Unknown'):20s} {narc}{height_info}")
        if len(cart_users) == 0:
            print("   (Empty user list - all users will be removed)")
        print("="*70 + "\n")
        
        # Open serial connection (or use shared one)
        owns_connection = ser is None
        if owns_connection:
            ser = serial.Serial(
                port=CONFIG['e2_serial_port'],
                baudrate=CONFIG['e2_baudrate'],
                timeout=15  # Longer timeout for user list write
            )
            time.sleep(0.5)
        ser.reset_input_buffer()
        
        # Send U1 command to start user list write
        logger.info("Sending U1 command to start user list write...")
        ser.write(b"U1\r\n")
        time.sleep(7.0)  # Care-E2 firmware needs settle time before large U1 writes
        
        # Read echo
        echo = ser.read(100).decode('utf-8', errors='ignore').strip()
        logger.debug(f"U1 echo: {repr(echo)}")
        
        # Send each user (or empty line if no users to clear the list)
        if len(cart_users) > 0:
            for idx, user in enumerate(cart_users):
                user_id = user.get('userId', '')
                user_name = user.get('userName', '')
                narc_access = 'Y' if user.get('narcAccess', False) else 'N'
                
                if is_e3:
                    # E3 (Care Pro) — 6-field format with height presets
                    # Azure returns None when no preset set yet — default to 0
                    stand_pos = int(user.get('prefWsfcStand') or 0)
                    sit_pos = int(user.get('prefWsfcSit') or 0)
                    user_line = f"{user_id}\t{user_name}\tNurse\t{narc_access}\t{stand_pos}\t{sit_pos}\r\n"
                    logger.info(f"Writing user {idx + 1}/{len(cart_users)}: {user_id} - {user_name} (Narc: {narc_access}, Stand: {stand_pos}, Sit: {sit_pos})")
                else:
                    # E2 — 4-field legacy format (no height data)
                    # Format: UserID\tUserName\tGroup\tNarcAccess\r\n
                    user_line = f"{user_id}\t{user_name}\tNurse\t{narc_access}\r\n"
                    logger.info(f"Writing user {idx + 1}/{len(cart_users)}: {user_id} - {user_name} (Narc: {narc_access})")
                
                ser.write(user_line.encode('utf-8'))
                time.sleep(0.10)  # Care-E2 firmware needs pacing for large user lists
        else:
            # Empty user list - send just a newline to clear all users
            logger.info("Clearing all users from E2 board (empty list)")
            ser.write(b"\r\n")
        
        # Wait for processing and check for OK response
        logger.info("Waiting for E2 board to process user list...")
        time.sleep(20)  # Give E2 board time to commit large user lists
        
        # Read response
        response = ""
        start_time = time.time()
        while time.time() - start_time < 5:
            if ser.in_waiting:
                response += ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
                time.sleep(0.1)
            else:
                time.sleep(0.1)
                if response:
                    break
        
        if owns_connection:
            ser.close()

        logger.debug(f"U1 response: {repr(response)}")

        # Check for OK or error codes
        # Care-E2 firmware may return U5 <zero-based last accepted row> after
        # a large U1 list. U5 1117 is success for a 1118-user list; a lower
        # value means the board timed out before accepting the full list.
        u5_match = re.search(r'\bU5\s+(\d+)', response)
        if u5_match:
            accepted_count = int(u5_match.group(1)) + 1
            if accepted_count >= len(cart_users):
                logger.info(f"User list write completed: U5 after final row ({accepted_count}/{len(cart_users)} accepted)")
                logger.info("=" * 60)
                logger.info(f"USER LIST SYNC COMPLETE: {len(cart_users)} users written")
                logger.info("=" * 60)
                print("\n" + "="*70)
                print(f"USER SYNC COMPLETE: {len(cart_users)} users written to E2 board")
                print("="*70 + "\n")
                return True
            logger.error(f"User list write incomplete: board accepted {accepted_count}/{len(cart_users)} users before U5 timeout")
            return False

        if "OK" in response:
            logger.info("✓ User list write successful (OK received)")
            logger.info("=" * 60)
            logger.info(f"USER LIST SYNC COMPLETE: {len(cart_users)} users written")
            logger.info("=" * 60)

            # Console-friendly result
            print("\n" + "="*70)
            print(f"✅ USER SYNC COMPLETE: {len(cart_users)} users written to E2 board")
            print("="*70 + "\n")
            return True
        elif "U2" in response:
            logger.error("✗ User list write failed: Memory full (U2)")
            return False
        elif "U3" in response:
            logger.error("✗ User list write failed: Invalid format (U3)")
            return False
        elif "U4" in response:
            logger.error("✗ User list write failed: Checksum error (U4)")
            return False
        elif "U5" in response:
            logger.error("✗ User list write failed: Timeout (U5)")
            return False
        elif "U7" in response:
            logger.error("✗ User list write failed: Unknown error (U7)")
            return False
        else:
            # No explicit OK, but no error either - consider success
            logger.warning(f"User list write completed (no explicit OK, response: {repr(response)})")
            logger.info("=" * 60)
            logger.info(f"USER LIST SYNC COMPLETE: {len(cart_users)} users written")
            logger.info("=" * 60)
            return True

    except Exception as e:
        logger.error(f"Error writing users to E2 board: {str(e)}")
        logger.exception("Full traceback:")
        return False


# ============================================================
# HEIGHT SYNC: U0 Read-Back → Azure (v1.0.25)
# ============================================================

# ── U0 record validation (v1.0.34 — Bug 1 defense) ────────────────────────────
# Guards against CDC-ACM framing bleed that polluted Azure with entries like
# userId='788' (truncated from 7788) and DefaultNurse.sit=7788 (alton's ID
# bleeding into sit slot). See project_session_apr16 memory for history.
_U0_USERID_RE   = re.compile(r'^\d{4,6}$')                    # board PINs are 4-6 digits (tightened v1.0.34 after seeing '12312345' concat garbage)
_U0_USERNAME_RE = re.compile(r'^[A-Za-z][A-Za-z0-9 _.\-]{0,29}$')
_U0_POS_MAX     = 999                                          # plausible encoder cap

def _validate_u0_record(parts):
    """Validate one tab-split U0 record.

    Returns ('ok', user_dict) on success, ('drop', reason_str) on a
    validation failure, or None if the record is too short to even attempt.
    """
    if len(parts) < 4:
        return None

    user_id = parts[0].strip()
    if not _U0_USERID_RE.match(user_id):
        return ('drop', f"userId={user_id!r} not 4-6 digits (likely CDC truncation)")

    user_name = parts[1].strip() if len(parts) > 1 else ''
    if not _U0_USERNAME_RE.match(user_name):
        return ('drop', f"userName={user_name!r} for id={user_id} not a plausible name")

    narc_raw = parts[3].strip().upper() if len(parts) > 3 else ''
    if narc_raw not in ('Y', 'N', ''):
        return ('drop', f"narcAccess={narc_raw!r} for id={user_id} not Y/N")

    def _parse_pos(raw, field_name):
        if not raw:
            return 0, None
        if not raw.isdigit():
            return None, f"{field_name}={raw!r} not numeric"
        val = int(raw)
        if val > _U0_POS_MAX:
            return None, f"{field_name}={val} > {_U0_POS_MAX} (likely userID bleed)"
        return val, None

    stand_raw = parts[4].strip() if len(parts) > 4 else ''
    sit_raw   = parts[5].strip() if len(parts) > 5 else ''
    stand_pos, err = _parse_pos(stand_raw, 'standPos')
    if err:
        return ('drop', f"id={user_id}: {err}")
    sit_pos, err = _parse_pos(sit_raw, 'seatPos')
    if err:
        return ('drop', f"id={user_id}: {err}")

    return ('ok', {
        'userId':     user_id,
        'userName':   user_name,
        'group':      parts[2].strip() if len(parts) > 2 else '',
        'narcAccess': narc_raw == 'Y',
        'standPos':   stand_pos,
        'seatPos':    sit_pos,
    })


def _u0_raw_read(ser, settle_ms=500, max_seconds=10):
    """Issue U0 on `ser` and accumulate the full decoded response.

    Kept separate from the validator so the retry loop can call it multiple
    times cheaply.
    """
    ser.reset_input_buffer()
    ser.write(b"U0\r\n")
    ser.flush()
    time.sleep(settle_ms / 1000.0)

    raw = ""
    start = time.time()
    no_data_count = 0
    while time.time() - start < max_seconds:
        if ser.in_waiting:
            raw += ser.read(ser.in_waiting).decode('utf-8', errors='ignore')
            no_data_count = 0
            time.sleep(0.05)
            # EOT: firmware sends empty line last — two consecutive newlines
            if '\r\n\r\n' in raw or raw.endswith('\r\n\n') or raw.endswith('\n\n'):
                break
        else:
            no_data_count += 1
            time.sleep(0.1)
            if no_data_count > 15 and len(raw) > 3:
                break
    return raw


def read_users_from_e2_board(ser=None):
    """Read full user list from E3 board via U0, with retry + strict validation.

    The U0 response is a series of tab-delimited lines, one per user:
        UserID\\tUserName\\tGroup\\tNarcAccess\\tStandPos\\tSeatPos\\r\\n

    v1.0.34: 3-attempt retry + field-level validation (`_validate_u0_record`)
    defends against CDC-ACM framing bleed (Bug 1). Corrupt records — truncated
    user IDs, numeric fields bled into the name slot, positions exceeding the
    plausible encoder range — are dropped so they never reach Azure.

    Args:
        ser: Optional shared serial connection (from E2Serial context manager).

    Returns:
        List of valid user dicts. Empty on serial failure or all-invalid response.
    """
    owns_connection = ser is None
    users = []
    final_raw = ""
    try:
        logger.info("=" * 60)
        logger.info("U0: Reading user list FROM E3 board")
        logger.info("=" * 60)

        if owns_connection:
            ser = serial.Serial(
                port=CONFIG['e2_serial_port'],
                baudrate=CONFIG['e2_baudrate'],
                timeout=5
            )
            time.sleep(0.3)

        MAX_ATTEMPTS = 3
        for attempt in range(1, MAX_ATTEMPTS + 1):
            raw = _u0_raw_read(ser)
            final_raw = raw

            if not raw.strip():
                logger.warning(f"U0: empty response on attempt {attempt}/{MAX_ATTEMPTS}")
                if attempt < MAX_ATTEMPTS:
                    time.sleep(0.3)
                    continue
                break

            validated = []
            dropped   = []
            for line in raw.splitlines():
                line = line.strip()
                if not line or line.startswith('U0') or line.startswith('U4'):
                    continue
                parts = line.split('\t')
                verdict = _validate_u0_record(parts)
                if verdict is None:
                    dropped.append(('too-short', repr(line)))
                    continue
                status, payload = verdict
                if status == 'ok':
                    validated.append(payload)
                else:
                    dropped.append((payload, repr(line)))

            # CLEAN: no dropped records at all — accept and return
            if not dropped:
                users = validated
                break

            # Had at least one dropped record. Log each drop once per attempt.
            logger.warning(f"U0: attempt {attempt}/{MAX_ATTEMPTS} — "
                           f"{len(validated)} valid, {len(dropped)} dropped")
            for reason, bad_line in dropped[:10]:
                logger.warning(f"  U0 DROP — {reason} — raw={bad_line}")

            # Retry to try for a fully-clean read (which is the common case
            # when Bug 1's CDC-ACM framing glitch eats a byte — next read is
            # often clean). Only on the last attempt do we settle for whatever
            # records did pass validation.
            if attempt < MAX_ATTEMPTS:
                time.sleep(0.3)
                continue
            users = validated
            logger.warning(f"U0: exhausted {MAX_ATTEMPTS} attempts — keeping {len(validated)} valid record(s), discarding {len(dropped)} garbage")
            break

        if owns_connection:
            ser.close()

        logger.debug(f"U0 raw response ({len(final_raw)} bytes): {repr(final_raw[:500])}")
        logger.info(f"U0: Parsed {len(users)} valid user(s) from E3 board")
        for u in users:
            logger.info(f"  {u['userId']:10s} {u['userName']:20s}  Stand:{u['standPos']:3d}  Sit:{u['seatPos']:3d}")

    except serial.SerialException as e:
        logger.warning(f"U0: Serial error reading user list (board disconnected?): {e}")
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass
    except Exception as e:
        logger.error(f"U0: Unexpected error: {e}")
        logger.exception("Full traceback:")
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass

    return users


def _load_height_state():
    """Load last-uploaded height state from disk.

    Returns dict keyed by userId: {'standPos': int, 'seatPos': int}
    """
    try:
        path = CONFIG['height_state_file']
        if os.path.exists(path):
            with open(path, 'r') as f:
                return json.load(f)
    except Exception as e:
        logger.debug(f"height_state load failed: {e}")
    return {}


def _save_height_state(state):
    """Persist height state to disk."""
    try:
        os.makedirs(os.path.dirname(CONFIG['height_state_file']), exist_ok=True)
        with open(CONFIG['height_state_file'], 'w') as f:
            json.dump(state, f, indent=2)
    except Exception as e:
        logger.warning(f"height_state save failed: {e}")


def upload_height_changes_to_azure(board_users, token):
    """Compare board heights against last-uploaded state and POST changes.

    Only runs on E3 (Care Pro) carts — E2 boards use the 4-field U1 format
    and do not store height presets.

    The endpoint expects an array of:
        [{ "userId": "7788", "prefWsfcStand": "75", "prefWsfcSit": "40" }]

    Args:
        board_users: List returned by read_users_from_e2_board()
        token:       Valid MSAL Bearer token

    Returns:
        True if no changes or upload succeeded, False on error.
    """
    if CONFIG.get('cart_type') != 'E3':
        logger.info("Height sync: E2 board — skipping (E3-only feature)")
        return True

    if not board_users:
        logger.info("Height sync: no users returned from board — skipping")
        return True

    last_state = _load_height_state()
    changed = []

    for user in board_users:
        uid = user['userId']
        stand = user['standPos']
        sit   = user['seatPos']

        # Only include if heights are non-zero (default 0 means no preset saved yet)
        if stand == 0 and sit == 0:
            logger.debug(f"Height sync: {uid} has no presets yet (0/0) — skipping")
            continue

        prev = last_state.get(uid, {})
        if prev.get('standPos') != stand or prev.get('seatPos') != sit:
            logger.info(f"Height CHANGED — {uid}: stand {prev.get('standPos','?')}→{stand}  sit {prev.get('seatPos','?')}→{sit}")
            changed.append({
                'userId':        uid,
                'prefWsfcStand': str(stand),
                'prefWsfcSit':   str(sit)
            })
        else:
            logger.debug(f"Height unchanged — {uid}: stand={stand} sit={sit}")

    if not changed:
        logger.info("Height sync: no changes detected — nothing to upload")
        return True

    logger.info("=" * 60)
    logger.info(f"HEIGHT SYNC: Uploading {len(changed)} changed user(s) to Azure")
    logger.info("=" * 60)
    print("\n" + "="*70)
    print(f"📐 HEIGHT SYNC: {len(changed)} user(s) with updated presets")
    for c in changed:
        print(f"   {c['userId']:10s}  Stand: {c['prefWsfcStand']:>4s}  Sit: {c['prefWsfcSit']:>4s}")
    print("="*70 + "\n")

    try:
        url = f"{CONFIG['cartusers_endpoint']}/{CONFIG['facility_id']}/"
        headers = {
            'Authorization': f'Bearer {token}',
            'Content-Type': 'application/json'
        }
        resp = requests.post(url, headers=headers, json=changed, timeout=30)

        logger.info(f"CallHomeCartUsers → HTTP {resp.status_code}")
        logger.debug(f"Response body: {repr(resp.text[:300])}")

        if resp.status_code in (200, 201, 204):
            logger.info("✓ Height sync uploaded successfully")
            print(f"✅ HEIGHT SYNC: Uploaded {len(changed)} user(s) — HTTP {resp.status_code}")

            # Persist new state so we don't re-upload unchanged values
            new_state = dict(last_state)  # preserve users not on this board
            for u in board_users:
                new_state[u['userId']] = {'standPos': u['standPos'], 'seatPos': u['seatPos']}
            _save_height_state(new_state)
            return True
        else:
            logger.warning(f"✗ Height sync failed: HTTP {resp.status_code} — {resp.text[:200]}")
            return False

    except Exception as e:
        logger.error(f"Height sync upload error: {e}")
        return False


def read_e2_board_data(ser=None):
    """Read all necessary data from E2 board

    Args:
        ser: Optional shared serial connection (from E2Serial context manager).
             If None, opens and closes its own connection.
    """
    owns_connection = ser is None
    try:
        if owns_connection:
            logger.info("Opening E2 board serial connection...")
            ser = serial.Serial(
                port=CONFIG['e2_serial_port'],
                baudrate=CONFIG['e2_baudrate'],
                timeout=2
            )
            time.sleep(0.5)
            ser.reset_input_buffer()
            ser.reset_output_buffer()
        
        data = {}
        
        # Read cart model/firmware version (G0)
        # Format: "G0\rCare-E2\t{CartID}\t{Version}" or "G0\rCare-E3\t{CartID}\t{Version}"
        # Build126 E3 boards can intermittently return only "Car"; use more
        # attempts and preserve the last complete identity instead of
        # downgrading a Pro cart to E2 on a partial read.
        g0_response = ""
        for g0_attempt in range(7):
            g0_response = read_e2_board_command(ser, 'G0', timeout=4)
            if '\t' in g0_response:
                break  # Got a complete response with tab-delimited fields
            logger.debug(f"G0 attempt {g0_attempt + 1}/7 incomplete: {repr(g0_response)}, retrying...")
            time.sleep(0.5)
            ser.reset_input_buffer()
        
        data['firmware'] = g0_response
        logger.info(f"E2 Cart Firmware: {repr(data['firmware'])}")
        
        # Parse Cart ID and detect cart type from G0 response
        # G0 returns: "Care-E2\tCartID\tVersion" or "Care-E3\tCartID\tVersion"
        # NOTE: The lab E3 board (no RTC battery) sometimes returns a truncated G0
        # with no tab even after 3 retries. In that case we preserve the existing
        # cart_type rather than silently downgrading it to E2.
        try:
            g0_parts = data['firmware'].replace('G0\r', '').split('\t')

            # Only update cart_type if G0 returned a complete (tab-delimited) response.
            # A single-field response means the board didn't answer fully — keep prior value.
            if '\t' in data['firmware']:
                model_str = g0_parts[0].strip().upper()
                firmware_version = g0_parts[2].strip() if len(g0_parts) >= 3 else None
                if 'E3' in model_str or 'E51' in model_str or 'PRO' in model_str:
                    CONFIG['cart_type'] = 'E3'
                else:
                    CONFIG['cart_type'] = 'E2'
                logger.info(f"✓ Cart type detected: {CONFIG['cart_type']} (from G0: {g0_parts[0].strip()})")
                cart_id_for_state = g0_parts[1].strip() if len(g0_parts) >= 2 else CONFIG.get('cart_id')
                save_cart_type_state(CONFIG['cart_type'], cart_id_for_state, firmware_version, data['firmware'])
            else:
                partial_model = data['firmware'].upper()
                if 'E3' in partial_model or 'PRO' in partial_model:
                    CONFIG['cart_type'] = 'E3'
                    save_cart_type_state(CONFIG['cart_type'], CONFIG.get('cart_id'), None, data['firmware'])
                    logger.warning(f"G0 was partial but identified E3: {repr(data['firmware'][:60])}")
                elif not restore_cart_type_from_state(
                    f"G0 returned no tab after 7 attempts ({repr(data['firmware'][:60])})"
                ):
                    logger.warning(
                        f"G0 returned no tab after 7 attempts ({repr(data['firmware'][:60])}) — "
                        f"keeping default cart_type={CONFIG['cart_type']}"
                    )

            # Parse Cart ID (second field) — only when response is complete
            if len(g0_parts) >= 2:
                cart_id_from_g0 = g0_parts[1].strip()
                if cart_id_from_g0:  # Accept any cart ID from E2 board (including default)
                    CONFIG['cart_id'] = cart_id_from_g0
                    logger.info(f"✓ Cart ID from E2 board: {cart_id_from_g0}")
        except Exception as e:
            logger.debug(f"Could not parse Cart ID/type from G0: {e}")
        
        time.sleep(0.2)  # Delay between commands
        
        # Read serial number (E0) — with same retry logic as G0 for E3 framing
        # Format: "E0\r{CartID}\t{CartID}\t{DateTime}"
        for e0_attempt in range(3):
            data['serial'] = read_e2_board_command(ser, 'E0')
            if '\t' in data['serial']:
                break
            logger.debug(f"E0 attempt {e0_attempt + 1} incomplete: {repr(data['serial'])}, retrying...")
            time.sleep(0.5)
            ser.reset_input_buffer()
        logger.info(f"E2 Serial: {repr(data['serial'])}")
        
        # Parse Cart ID from E0 response (backup if G0 failed)
        if CONFIG['cart_id'] == 'UNKNOWN':
            try:
                e0_parts = data['serial'].replace('E0\r', '').split('\t')
                if len(e0_parts) >= 1:
                    cart_id_from_e0 = e0_parts[0].strip()
                    if cart_id_from_e0:  # Accept any cart ID from E2 board
                        CONFIG['cart_id'] = cart_id_from_e0
                        logger.info(f"✓ Cart ID from E2 board (E0): {cart_id_from_e0}")
            except Exception as e:
                logger.debug(f"Could not parse Cart ID from E0: {e}")
        
        # Read battery status (B0) — with retry for E3 framing
        for b0_attempt in range(3):
            data['battery'] = read_e2_board_command(ser, 'B0')
            if '\t' in data['battery']:
                break
            logger.debug(f"B0 attempt {b0_attempt + 1} incomplete: {repr(data['battery'])}, retrying...")
            time.sleep(0.5)
            ser.reset_input_buffer()
        logger.info(f"E2 Battery: {data['battery']}")
        time.sleep(0.2)
        
        # Read cabinet status (S0) — with retry for E3 framing
        # Format: "CL\t1234\t23603232323212121212121262"
        for s0_attempt in range(3):
            data['status'] = read_e2_board_command(ser, 'S0')
            if '\t' in data['status']:
                break
            logger.debug(f"S0 attempt {s0_attempt + 1} incomplete: {repr(data['status'])}, retrying...")
            time.sleep(0.5)
            ser.reset_input_buffer()
        logger.info(f"E2 Status: {data['status']}")
        
        # Extract drawer configuration from S0 response
        # S0 returns: status_code TAB id TAB drawer_config
        try:
            parts = data['status'].split('\t')
            if len(parts) >= 3:
                data['drawer_config'] = parts[2].strip()
                logger.info(f"E2 Drawer Config (from S0): {data['drawer_config']}")
            else:
                # Fallback: read H0 for number of rows
                data['drawer_config'] = read_e2_board_command(ser, 'H0')
                logger.info(f"E2 Drawer Config (from H0): {data['drawer_config']}")
        except Exception as e:
            logger.error(f"Error parsing drawer config from S0: {e}")
            data['drawer_config'] = read_e2_board_command(ser, 'H0')
        
        time.sleep(0.3)
        
        # Read audit logs (L0) - longer timeout for multiple logs (can be many entries)
        audit_response = read_e2_board_command(ser, 'L0', timeout=10)
        logger.info(f"Raw audit response length: {len(audit_response)} chars, lines: {len(audit_response.split(chr(10)))}")
        logger.debug(f"Raw audit response: {audit_response[:500]}")  # First 500 chars
        data['audit_logs'] = parse_e2_audit_logs(audit_response)
        logger.info(f"E2 Audit Logs: Found {len(data['audit_logs'])} entries")
        
        if owns_connection:
            ser.close()
        return data

    except serial.SerialException as e:
        logger.error(f"Could not access E2 board: {str(e)}")
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass
        return None
    except Exception as e:
        logger.error(f"Error reading E2 board: {str(e)}")
        logger.exception("Full traceback:")
        if owns_connection and ser and hasattr(ser, 'is_open') and ser.is_open:
            try:
                ser.close()
            except Exception:
                pass
        return None

def get_log_hash(log):
    """Generate unique hash for an audit log entry"""
    # Create hash from key fields that uniquely identify a log
    log_string = f"{log['userId']}_{log['userName']}_{log['openDate']}_{log['closeDate']}_{log['openDrawers']}_{log['closeDrawers']}"
    return hashlib.md5(log_string.encode()).hexdigest()

def load_sent_logs():
    """Load sent audit log hashes as an ordered list (oldest first).

    v1.0.33: Returns a list (not a set) to preserve insertion order so
    pruning in save_sent_logs correctly discards the oldest entries.

    LOAD ORDER (v1.0.27):
      1. tmpfs (/var/log/) — fast, in-memory, current run's working set
      2. persistent mirror (/var/lib/hmpd/) — survives reboots
      3. legacy path (/home/pi/) — backwards-compat with pre-v1.0.27 boards
    On first run after a reboot, tmpfs is empty so we restore from persistent.
    """
    for path in [SENT_LOGS_TMPFS, SENT_LOGS_PERSIST, '/home/pi/sent_audit_logs.json']:
        try:
            if os.path.exists(path):
                with open(path, 'r') as f:
                    data = json.load(f)
                if not isinstance(data, list):
                    data = list(data)
                # If restored from persistent/legacy, prime the tmpfs copy
                if path != SENT_LOGS_TMPFS:
                    try:
                        with open(SENT_LOGS_TMPFS, 'w') as f:
                            json.dump(data, f)
                        logger.debug('Restored sent_logs from ' + path + ' into tmpfs')
                    except Exception:
                        pass
                return data
        except Exception as e:
            logger.debug('Could not load sent logs from ' + path + ': ' + str(e))
    return []

def save_sent_logs(sent_hashes):
    """Save sent audit log hashes (ordered list, oldest first).

    v1.0.33: Input is an ordered list. Pruning takes [-5000:] which
    correctly keeps the newest 5000 entries and discards the oldest.
    """
    try:
        hash_list = sent_hashes if isinstance(sent_hashes, list) else list(sent_hashes)
        if len(hash_list) > 5000:
            hash_list = hash_list[-5000:]
            logger.info('Pruned sent log hashes from ' + str(len(sent_hashes)) + ' to 5000')

        # Write to tmpfs (fast, no SD wear)
        with open(SENT_LOGS_TMPFS, 'w') as f:
            json.dump(hash_list, f)

        # Flush to persistent storage (survives reboot)
        try:
            os.makedirs(os.path.dirname(SENT_LOGS_PERSIST), exist_ok=True)
            with open(SENT_LOGS_PERSIST, 'w') as f:
                json.dump(hash_list, f)
        except Exception as pe:
            logger.warning('Could not flush sent_logs to persistent: ' + str(pe))

        logger.info('Saved ' + str(len(hash_list)) + ' sent log hashes')
    except Exception as e:
        logger.error('Could not save sent logs: ' + str(e))

def parse_e2_audit_logs(response):
    """Parse audit log response from E2 board
    
    Format varies by cart model:
    - 14-char drawer configs: UserID UserName DrawerData(14) Date Time DrawerData(14) Date Time
    - 26-char drawer configs: UserID UserName DrawerData(26) Date Time DrawerData(26) Date Time
    
    Date format: MM/DD/YY (with extra spaces possible)
    Time format: HH:MM:SS
    """
    logs = []
    
    if not response:
        return logs
    
    # Pattern: UserID(4) UserName(variable) DrawerData(variable, even length) Date Time DrawerData Date Time
    # Drawer data is variable length but always even (pairs of digits)
    # Date has optional extra spaces: "09/08/25  15:50:17" or "09/08/25 15:50:17"
    pattern = r'(\d{4})\t(\w+)\t(\d+)\t([\d/]+)\s+([\d:]+)\t(\d+)\t([\d/]+)\s+([\d:]+)'
    
    for match in re.finditer(pattern, response):
        try:
            user_id = match.group(1)
            user_name = match.group(2)
            open_drawers = match.group(3)
            open_date = match.group(4).strip()
            open_time = match.group(5).strip()
            close_drawers = match.group(6)
            close_date = match.group(7).strip()
            close_time = match.group(8).strip()
            
            # Validate drawer data is even length (pairs)
            if len(open_drawers) % 2 != 0 or len(close_drawers) % 2 != 0:
                logger.warning(f"Invalid drawer data length: open={len(open_drawers)}, close={len(close_drawers)}")
                continue
            
            # Parse dates - handle both "MM/DD/YY" formats
            # E2 board stores times in local timezone
            open_dt = datetime.strptime(f"{open_date} {open_time}", "%m/%d/%y %H:%M:%S")
            close_dt = datetime.strptime(f"{close_date} {close_time}", "%m/%d/%y %H:%M:%S")
            
            # Read system timezone and convert E2 times to UTC
            try:
                import pytz
                # Read timezone from system; Windows/dev tests may not have /etc/timezone.
                try:
                    with open('/etc/timezone', 'r') as f:
                        local_tz_name = f.read().strip() or 'UTC'
                except FileNotFoundError:
                    local_tz_name = 'UTC'
                local_tz = pytz.timezone(local_tz_name)
                
                # Make timezone-aware and convert to UTC
                open_dt_local = local_tz.localize(open_dt)
                close_dt_local = local_tz.localize(close_dt)
                open_dt_utc = open_dt_local.astimezone(pytz.utc)
                close_dt_utc = close_dt_local.astimezone(pytz.utc)
            except Exception as tz_error:
                # Fallback: use system timezone offset if pytz fails
                logger.warning(f"Timezone conversion failed, using system UTC offset: {tz_error}")
                # Get the system's current UTC offset
                import time
                if time.daylight:
                    utc_offset_seconds = time.altzone
                else:
                    utc_offset_seconds = time.timezone
                # timezone gives seconds west of UTC, so negate it
                from datetime import timedelta
                utc_offset = timedelta(seconds=-utc_offset_seconds)
                # Apply offset to convert local time to UTC
                open_dt_utc = open_dt + utc_offset
                close_dt_utc = close_dt + utc_offset
            
            log = {
                "userId": user_id,
                "userName": user_name,
                "openDate": open_dt_utc.strftime("%Y-%m-%dT%H:%M:%S") + "Z",
                "closeDate": close_dt_utc.strftime("%Y-%m-%dT%H:%M:%S") + "Z",
                "openDrawers": open_drawers,
                "closeDrawers": close_drawers,
                "drawersOpenedAtOpen": False,
                "drawersOpenAtClose": False
            }
            logs.append(log)
            logger.debug(f"Parsed audit log: {user_name} on {open_date} (drawer config: {len(open_drawers)} chars)")
        except ValueError as e:
            logger.warning(f"Could not parse audit log entry, error: {e}")
    
    return logs

def filter_new_logs(logs):
    """Filter out audit logs that have already been sent.

    v1.0.33: Uses ordered list + set for O(1) lookup with correct pruning.
    """
    sent_list = load_sent_logs()       # ordered list (oldest first)
    sent_set = set(sent_list)          # O(1) lookup
    new_logs = []

    for log in logs:
        log_hash = get_log_hash(log)
        if log_hash not in sent_set:
            new_logs.append(log)
            sent_list.append(log_hash)
            sent_set.add(log_hash)

    if new_logs:
        save_sent_logs(sent_list)
        logger.info(f"Found {len(new_logs)} new audit logs (filtered {len(logs) - len(new_logs)} already sent)")
    else:
        logger.info(f"No new audit logs (all {len(logs)} already sent)")

    return new_logs

def read_tdi_hid_feature(vendor_id, product_id, report_id):
    """Read HID Feature Report from TDI Power Supply
    
    This reads low-level HID Feature Reports directly from the TDI Power,
    similar to how Windows PowerDisplayService does it.
    
    Args:
        vendor_id: USB Vendor ID (0x04d8 for Microchip or 0x0483 for STM)
        product_id: USB Product ID (0xf55b for TDI Power)
        report_id: HID Report ID to read
    
    Returns:
        bytes: Raw HID Feature Report data, or None if error
    """
    try:
        # Open HID device
        device = hid.device()
        device.open(vendor_id, product_id)
        
        # Read feature report
        # Report ID is the first byte, followed by data
        data = device.get_feature_report(report_id, 65)  # 65 bytes max for HID reports
        
        device.close()
        return data
        
    except Exception as e:
        logger.debug(f"HID read error (VID:0x{vendor_id:04x} PID:0x{product_id:04x} Report:{report_id}): {e}")
        return None

def parse_hid_power_value(data, byte_offset, scale=1.0):
    """Parse power value from HID Feature Report
    
    TDI Power stores values as little-endian integers in the HID report.
    Windows uses RequestToMatch() which extracts values at specific byte offsets.
    
    Args:
        data: Raw HID Feature Report bytes
        byte_offset: Byte offset in report (0-indexed)
        scale: Scaling factor (e.g., 0.1 for values that need division by 10)
    
    Returns:
        float: Parsed and scaled value, or 0.0 if error
    """
    try:
        if data is None or len(data) < byte_offset + 2:
            return 0.0
        
        # Extract 2-byte little-endian integer
        # HID reports typically store multi-byte values as little-endian
        value = struct.unpack_from('<H', data, byte_offset)[0]
        return value * scale
        
    except Exception as e:
        logger.debug(f"HID parse error at offset {byte_offset}: {e}")
        return 0.0

def get_tdi_hid_data():
    """Read current and load from TDI Power Supply via HID

    Requires temporarily stopping NUT driver to get exclusive access.
    To prevent NUT Monitor from triggering a shutdown when driver stops,
    we must stop NUT Monitor first.

    CRITICAL INVARIANT (do NOT break): nut-monitor.service MUST stay masked
    on field carts.  upsmon.conf:6 has SHUTDOWNCMD="/sbin/shutdown -h +0" —
    if nut-monitor is unmasked and running, the brief HID-read pause below
    will trip its DEADTIME and shut the cart down mid-shift.  The
    `systemctl stop nut-monitor.service` call here is defense-in-depth, not
    a substitute for masking.  See the "Critical Invariants" section of
    docs/PRODUCTION_READINESS.md.
    """
    data = {'output_current': 0.0, 'output_load': 0, 'temperature': 22}
    
    try:
        # Stop both NUT monitor and driver
        # Stopping monitor prevents "Communication lost" -> "Shutdown" sequence
        logger.info("Stopping NUT services for HID access...")
        subprocess.run(["systemctl", "stop", "nut-monitor.service"], check=False)
        subprocess.run(["systemctl", "stop", "nut-driver@tdi.service"], check=False)
        time.sleep(0.5)  # Wait for release
        
        # Find TDI device
        # Try STMicroelectronics first (E3 carts), then Microchip (E2 carts)
        dev = usb.core.find(idVendor=0x0483, idProduct=0xf55b)
        is_stmicro = False
        
        if dev:
            is_stmicro = True
            logger.info(f"Found STMicro TDI Power Supply (0483:f55b)")
        else:
            dev = usb.core.find(idVendor=0x04d8, idProduct=0xf55b)
            if dev:
                logger.info(f"Found Microchip TDI Power Supply (04d8:f55b)")
        
        if not dev:
            logger.warning("TDI HID device not found (checked 0483:f55b and 04d8:f55b)")
            return data
            
        # Detach kernel driver if needed (though stopping service usually does this)
        if dev.is_kernel_driver_active(0):
            try:
                dev.detach_kernel_driver(0)
            except usb.core.USBError as e:
                logger.warning(f"Could not detach kernel driver: {e}")

        try:
            dev.set_configuration()
        except:
            pass  # Already configured or busy
            
        # Read Report 84: Temperature (Only supported on Microchip)
        if not is_stmicro:
            try:
                # Feature Report 84 (0x54)
                # 65 bytes: ReportID + 64 bytes data
                # Value is at index 1 and 2 (Little Endian)
                data_84 = dev.ctrl_transfer(0xA1, 0x01, (3 << 8) | 84, 0, 65, timeout=1000)
                if len(data_84) >= 3:
                    # Convert raw ADC value to Celsius
                    raw_temp = struct.unpack_from("<H", bytes(data_84), 1)[0]
                    logger.debug(f"HID Report 84 raw: {raw_temp}")
            except Exception as e:
                logger.warning(f"Could not read HID Report 84: {e}")
        
        # Read Report 70: Output Current
        try:
            # Feature Report 70 (0x46)
            # Microchip: 65 bytes, Value at index 1 (uint16) * 0.1 -> Amps
            # STMicro: 3 bytes, Value at index 1 (uint16) -> Amps?
            data_70 = dev.ctrl_transfer(0xA1, 0x01, (3 << 8) | 70, 0, 65, timeout=1000)
            
            if len(data_70) >= 3:
                raw_current = struct.unpack_from("<H", bytes(data_70), 1)[0]
                data['output_current'] = float(raw_current) * 0.1
                logger.info(f"✓ HID Report 70: current={data['output_current']}A")
            else:
                logger.warning(f"HID Report 70 too short: {len(data_70)} bytes")
                
        except Exception as e:
            logger.warning(f"Could not read HID Report 70: {e}")
            
        # Read Report 30: Output Load
        try:
            # Feature Report 30 (0x1E)
            # Microchip: 65 bytes, Value at index 1 (uint8) -> Percent
            # STMicro: 2 bytes, Value at index 1 (uint8) -> Percent
            data_30 = dev.ctrl_transfer(0xA1, 0x01, (3 << 8) | 30, 0, 65, timeout=1000)
            
            if len(data_30) >= 2:
                raw_load = data_30[1]
                data['output_load'] = int(raw_load)
                logger.info(f"✓ HID Report 30: load={data['output_load']}%")
            else:
                logger.warning(f"HID Report 30 too short: {len(data_30)} bytes")
                
        except Exception as e:
            logger.warning(f"Could not read HID Report 30: {e}")
            
    except Exception as e:
        logger.error(f"HID read error: {str(e)}")
        
    finally:
        # Release USB device properly before restarting NUT
        try:
            if dev:
                usb.util.dispose_resources(dev)
        except:
            pass
        
        # Always restart services. ExecStopPost in the systemd unit provides
        # a safety net if this finally block never runs (SIGKILL), but we still
        # restart here for the normal path to minimize the NUT-down window.
        logger.debug("Restarting NUT services...")
        time.sleep(1.0)  # v1.0.32: reduced from 3.0s — ExecStopPost is the safety net now
        subprocess.run(["systemctl", "start", "nut-driver@tdi.service"], check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        time.sleep(1.5)  # v1.0.32: reduced from 3.0s
        subprocess.run(["systemctl", "start", "nut-monitor.service"], check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        
    return (data['temperature'], data['output_current'], data['output_load'])

def get_power_data():
    """Get power data from TDI Power Supply via NUT (Network UPS Tools)"""
    try:
        # Read from NUT using upsc command
        result = subprocess.run(
            ['upsc', 'tdi@localhost'],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        if result.returncode != 0:
            logger.error(f"Failed to read UPS data: {result.stderr}")
            return None
        
        # Parse upsc output into dictionary
        ups_data = {}
        for line in result.stdout.strip().split('\n'):
            if ':' in line:
                key, value = line.split(':', 1)
                ups_data[key.strip()] = value.strip()
        
        # Extract and format data
        battery_runtime_sec = int(float(ups_data.get('battery.runtime', 0)))
        runtime_hours = battery_runtime_sec // 3600
        runtime_mins = (battery_runtime_sec % 3600) // 60
        runtime_secs = battery_runtime_sec % 60
        
        # Get UPS status for conditional logic
        ups_status = ups_data.get('ups.status', 'UNKNOWN')
        
        # Get temperature, output current, and load directly from TDI Power via HID
        # Windows: Service1.cs lines 2257-2266 (Temperature from Report 84)
        # Windows: Service1.cs line 426: OutputCurrent = RequestToMatch(49, 132, 70) * 0.1
        # Windows: Service1.cs line 427: OutputLoad = RequestToMatch(53, 132, 30)
        # NUT doesn't expose these HID Feature Reports correctly, so we read them directly
        temp_celsius, output_current, output_load = get_tdi_hid_data()
        
        battery_voltage = float(ups_data.get('battery.voltage', 12.0))
        
        # Input voltage and frequency: TDI Power doesn't report these via HID
        # Windows solution: Hardcode when on utility power (Service1.cs lines 424-425)
        if 'OL' in ups_status:  # On Line (mains power)
            input_voltage = CONFIG['mains_voltage']    # v1.0.33: configurable via .env MAINS_VOLTAGE
            input_frequency = CONFIG['mains_frequency']  # v1.0.33: configurable via .env MAINS_FREQUENCY
        else:
            input_voltage = 0  # On battery, no input
            input_frequency = 0
        
        # Get TDI Power Supply serial number and update CONFIG if not already set
        tdi_serial = ups_data.get('device.serial', CONFIG['cart_serial'])
        if tdi_serial and tdi_serial != 'UNKNOWN' and CONFIG['cart_serial'] == 'UNKNOWN':
            CONFIG['cart_serial'] = tdi_serial
            logger.info(f"✓ TDI Power Supply Serial: {tdi_serial}")
        
        return {
            'battery_capacity': ups_data.get('battery.charge', '0'),
            'battery_voltage': str(battery_voltage),
            'battery_state': 'Discharging' if 'DISCHRG' in ups_status else 'Charging',
            'serial_number': tdi_serial,
            'firmware': '2.08.02 Rev 7',  # TDI firmware not exposed via NUT or any known HID report; value from Windows Service1.cs
            'manufacturer': ups_data.get('device.mfr', 'AstrodyneTDI'),
            'model': ups_data.get('device.model', 'TDI Power SPS5958-LF').strip(),
            'ip_address': get_local_ip(),
            'battery_installed': '',  # v1.0.33: Not available from NUT — send empty, Azure handles null
            'battery_runtime': f"{runtime_hours:02d}:{runtime_mins:02d}:{runtime_secs:02d}",
            'battery_temp': str(temp_celsius),  # Temperature in Celsius
            'output_current': output_current,  # Amps
            'output_load': output_load,  # Percentage
            'input_voltage': input_voltage,  # Volts
            'input_frequency': input_frequency,  # Hz
            'ups_status': ups_status
        }
    except subprocess.TimeoutExpired:
        logger.error("Timeout reading UPS data")
        return None
    except Exception as e:
        logger.error(f"Error getting power data: {str(e)}")
        return None

def format_access_point(mac, ssid, signal):
    """Format access point information"""
    try:
        ssid_padded = f"{ssid:<30}"
        mac_clean = ''.join(c.lower() for c in mac if c.isalnum())
        signal_value = abs(int(float(signal.replace('dBm', '').strip())))
        signal_formatted = f"{signal_value:02d}"
        return f"{ssid_padded},{mac_clean},{signal_formatted}"
    except Exception as e:
        logger.error(f"Error formatting AP: {str(e)}")
        return "\u0000" * 30 + ",000000000000,00"

def build_drawer_config_from_e2_status(drawer_config_raw):
    """Build drawer configuration string from E2 S0 (Cabinet Status) command
    
    The S0 command returns the actual drawer configuration directly from the E2 board.
    No need to rely on audit logs - this is the authoritative source!
    
    Format: Variable-length string where each pair represents one drawer
    Examples: 
      - "2320121212121212" = 8 drawers (16 chars)
      - "23603232323212121212121262" = 13 drawers (26 chars)
    
    Different cart models have different numbers of drawers.
    """
    try:
        # Check if we got a valid drawer config (must be even length, all digits)
        if len(drawer_config_raw) > 0 and len(drawer_config_raw) % 2 == 0 and drawer_config_raw.isdigit():
            # Count active drawers for logging
            active_drawers = 0
            num_drawers = len(drawer_config_raw) // 2
            for i in range(0, len(drawer_config_raw), 2):
                drawer_state = drawer_config_raw[i:i+2]
                if drawer_state != '00':
                    active_drawers += 1
            
            logger.info(f"Using drawer config from S0: {drawer_config_raw} ({num_drawers} drawers, {active_drawers} active)")
            return drawer_config_raw
        else:
            # If we can't parse it, log error but don't use a fake default
            # Azure should handle missing/invalid drawer configs gracefully
            logger.error(f"Invalid drawer config from S0 (length: {len(drawer_config_raw)}, content: {repr(drawer_config_raw)})")
            # Return empty string - let Azure handle it
            return ""
        
    except Exception as e:
        logger.error(f"Error processing drawer config from S0: {e}")
        return ""

def create_device_payload(e2_data, power_data):
    """Create device payload for Azure"""
    try:
        # Get WiFi info
        ap_ssid, ap_mac, ap_signal = get_wifi_info()
        current_ap = format_access_point(ap_mac, ap_ssid, ap_signal) if all([ap_ssid, ap_mac, ap_signal]) else "\u0000" * 30 + ",000000000000,00"
        
        # Update AP history for semi-RTLS tracking
        aP1, aP2, aP3 = update_ap_history(current_ap)

        ap_whitelist_report = None
        if CONFIG.get('ap_whitelist_report_fields'):
            try:
                ap_whitelist_report = create_ap_whitelist_report(ap_mac)
            except Exception as ap_report_err:
                logger.warning(f"AP whitelist diagnostic fields skipped: {ap_report_err}")
        
        # Get drawer configuration from E2 S0 command
        # S0 returns the actual drawer configuration (length varies by cart model)
        drawer_config_raw = e2_data.get('drawer_config', '').strip()
        drawer_config = build_drawer_config_from_e2_status(drawer_config_raw)
        
        # Parse firmware from E2 - G0 returns "Care-E2\tDefault\t2.0.0"
        firmware_raw = e2_data.get('firmware', '2.0.0').strip()
        # In degraded mode firmware_raw='UNAVAILABLE' — handle gracefully
        if firmware_raw == 'UNAVAILABLE':
            firmware = 'UNAVAILABLE'
        elif '\t' in firmware_raw:
            parts = firmware_raw.split('\t')
            firmware = parts[-1].strip()
        else:
            version_match = re.search(r'\d+\.\d+\.\d+', firmware_raw)
            firmware = version_match.group(0) if version_match else '2.0.0'
        
        logger.info(f"Parsed cartFirmware: {firmware}")
        
        payload = {
            "id": "",
            "_self": "",
            "hostname": socket.gethostname(),
            "assetTag": None,  # Windows sends null
            "softwareVersion": SCRIPT_VERSION,  # HMPD Python script version
            "facilityId": CONFIG['facility_id'],
            "cartDrawerConfig": drawer_config,
            "cartId": CONFIG['cart_id'],
            "cartSN": CONFIG['cart_id'],  # CRITICAL FIX: Windows sends cartId as cartSN!
            "currentAP": current_ap,
            "aP1": aP1,  # Previous AP (most recent before current) - Semi-RTLS tracking
            "aP2": aP2,  # Second previous AP
            "aP3": aP3,  # Third previous AP (oldest)
            "cartFirmware": firmware,
            "ipAddress": power_data.get('ip_address', '192.168.0.116'),
            "psBattInstalledDate": datetime.strptime(power_data['battery_installed'], "%Y-%m-%dT%H:%M:%S").strftime("%m/%d/%Y %H:%M:%S") if power_data.get('battery_installed') else None,
            "psFirmware": power_data.get('firmware', '2.08.02').replace(' Rev 7', '').replace('20802', '2.08.02'),
            "psManufacturer": power_data.get('manufacturer', 'TDI'),
            "psSN": power_data.get('serial_number', CONFIG['cart_serial']),
            "psModel": power_data.get('model', 'TDI Power SPS5958-LF'),
            "lastCallHome": None,
            "updateProfileOnNextConnect": False,  # Server-managed flag — set by Fleet Manager when profile changes are made
            "updateUsersOnNextConnect": False,  # Server-managed flag — set by Fleet Manager when user/height changes are made
            "lastAuditLogTransmission": None,
            "lastUpdateApplied": None
        }

        if ap_whitelist_report:
            payload.update(ap_whitelist_report)
        
        # DETAILED DEBUG LOGGING
        import json
        logger.info("=" * 60)
        logger.info("CALLHOME REQUEST PAYLOAD (formatted):")
        logger.info(json.dumps(payload, indent=2))
        logger.info("=" * 60)
        
        return payload
    except Exception as e:
        logger.error(f"Error creating device payload: {str(e)}")
        return None

def cache_failed_payload(payload, payload_type="device"):
    """Cache a failed payload for retry on next run
    
    Args:
        payload: The payload that failed to send
        payload_type: Type of payload (device, audit, power)
    """
    try:
        cache_file = CONFIG['failed_payloads_file']
        cached = []
        
        # Load existing cache
        if os.path.exists(cache_file):
            try:
                with open(cache_file, 'r') as f:
                    cached = json.load(f)
            except:
                cached = []
        
        # Add new failed payload with timestamp
        cached.append({
            'type': payload_type,
            'payload': payload,
            'timestamp': datetime.now(timezone.utc).isoformat(),
            'attempts': 1
        })
        
        # Keep only last 50 failed payloads to prevent unbounded growth
        if len(cached) > 50:
            cached = cached[-50:]
        
        # Save cache
        with open(cache_file, 'w') as f:
            json.dump(cached, f)
        
        logger.info(f"Cached failed {payload_type} payload for retry ({len(cached)} total cached)")
        
    except Exception as e:
        logger.error(f"Failed to cache payload: {e}")

def retry_cached_payloads(token):
    """Retry sending any cached failed payloads
    
    Args:
        token: Valid authentication token
    
    Returns:
        Number of successfully sent cached payloads
    """
    cache_file = CONFIG['failed_payloads_file']
    
    if not os.path.exists(cache_file):
        return 0
    
    try:
        with open(cache_file, 'r') as f:
            cached = json.load(f)
    except:
        return 0
    
    if not cached:
        return 0
    
    logger.info(f"Retrying {len(cached)} cached payloads...")
    
    success_count = 0
    remaining = []
    
    for item in cached:
        payload = item['payload']
        payload_type = item.get('type', 'device')
        attempts = item.get('attempts', 1)
        
        # Try to send
        success = send_data_internal(CONFIG['endpoint'], payload, token)
        
        if success:
            success_count += 1
            logger.info(f"✓ Successfully sent cached {payload_type} payload")
        else:
            # Keep for retry, but limit attempts
            if attempts < 10:  # Max 10 retry attempts
                item['attempts'] = attempts + 1
                remaining.append(item)
            else:
                logger.warning(f"Dropping {payload_type} payload after {attempts} failed attempts")
    
    # Save remaining failed payloads
    try:
        with open(cache_file, 'w') as f:
            json.dump(remaining, f)
    except:
        pass
    
    if success_count > 0:
        logger.info(f"✓ Sent {success_count} cached payloads, {len(remaining)} remaining")
    
    return success_count

def send_data_internal(endpoint, payload, token):
    """Internal send function without caching (used by retry logic)"""
    try:
        headers = {
            'Authorization': f'Bearer {token}',
            'Content-Type': 'application/json',
            'Accept': 'application/json'
        }
        
        response = requests.post(
            endpoint,
            headers=headers,
            json=payload,
            timeout=30
        )
        
        return response.status_code == 200
        
    except Exception as e:
        return False

def send_data(endpoint, payload, token, return_response=False, cache_on_failure=True):
    """Send data to Azure endpoint
    
    Args:
        endpoint: Azure endpoint URL
        payload: JSON payload to send
        token: Authentication token
        return_response: If True, return response object instead of boolean
        cache_on_failure: If True, cache payload for retry if send fails
    
    Returns:
        If return_response=True: response object or None
        If return_response=False: True if status 200, False otherwise
    """
    try:
        headers = {
            'Authorization': f'Bearer {token}',
            'Content-Type': 'application/json',
            'Accept': 'application/json'
        }
        
        logger.info(f"Sending payload to {endpoint}")
        logger.debug(json.dumps(payload, indent=2))
        
        response = requests.post(
            endpoint,
            headers=headers,
            json=payload,
            timeout=30
        )
        
        logger.info(f"Response status code: {response.status_code}")
        logger.info("=" * 60)
        logger.info("CALLHOME RESPONSE BODY (formatted):")
        try:
            response_json = response.json()
            logger.info(json.dumps(response_json, indent=2))
        except:
            logger.info(response.text)
        logger.info("=" * 60)
        
        if return_response:
            return response if response.status_code == 200 else None
        else:
            return response.status_code == 200
        
    except Exception as e:
        logger.error(f"Error sending data: {str(e)}")
        
        # Cache for retry if enabled
        if cache_on_failure and payload:
            cache_failed_payload(payload, "device")
        
        return None if return_response else False

def create_power_log_payload(power_data, board_time=None):
    """Create power log payload for Azure

    Args:
        power_data: Power data dict from get_power_data()
        board_time: Optional pre-read board RTC time (avoids extra serial open).
                    If None, uses Pi system time directly.
    """
    try:
        # v1.0.32: Use pre-read board time if available (from Phase 1 serial read),
        # avoiding an extra serial port open just for a timestamp.
        e2_time = board_time
        
        if e2_time:
            # E2 board time is in local timezone, convert to UTC
            try:
                import pytz
                # Read timezone from system; Windows/dev tests may not have /etc/timezone.
                try:
                    with open('/etc/timezone', 'r') as f:
                        local_tz_name = f.read().strip() or 'UTC'
                except FileNotFoundError:
                    local_tz_name = 'UTC'
                local_tz = pytz.timezone(local_tz_name)
                
                # Make timezone-aware and convert to UTC
                e2_time_local = local_tz.localize(e2_time)
                now = e2_time_local.astimezone(pytz.utc)
                logger.debug(f"Using E2 board time for power log: {now.strftime('%Y-%m-%d %H:%M:%S')} UTC")
            except Exception as tz_error:
                logger.warning(f"Timezone conversion failed for E2 time: {tz_error}")
                # Fallback to Pi system time
                now = datetime.now(timezone.utc)
                logger.warning("Falling back to Pi system time for power log")
        else:
            # E2 board time not available (expected on lab E3 boards with no RTC battery).
            # Use Pi system time (kept accurate by sync_clocks HTTPS tier).
            now = datetime.now(timezone.utc)
            logger.info("Board RTC time not available — using Pi system time for power log (normal on lab E3 board)")
        
        pk = f"{now.year}-{now.month:02d}-{CONFIG['facility_id']}"
        
        # v1.0.33: battery_installed is empty (not available from NUT)
        batt_installed_raw = power_data.get('battery_installed', '')
        if batt_installed_raw:
            battery_install_date = datetime.strptime(batt_installed_raw, "%Y-%m-%dT%H:%M:%S").replace(tzinfo=timezone.utc)
            battery_age = (now - battery_install_date).days // 365
        else:
            battery_age = 0  # Unknown — cannot compute without install date
        
        # Temperature is already in Celsius from get_power_data() (converted from ADC via polynomial)
        temp_c = int(float(power_data.get('battery_temp', 0)))
        
        payload = {
            "pk": pk,
            "logDate": now.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z",  # UTC timestamp with Z indicator
            "hostname": socket.gethostname(),
            "psSN": power_data.get('serial_number', CONFIG['cart_serial']),
            "batteryCapacity": int(float(power_data.get('battery_capacity', 0))),
            "batteryChargeState": power_data.get('battery_state', 'Unknown'),
            "batteryVoltage": float(power_data.get('battery_voltage', 0)),
            "LRTLB": power_data.get('battery_runtime', '00:00:00'),
            "inputVolt": power_data.get('input_voltage', 0),  # Hardcoded 120V when on mains
            "inputFreq": power_data.get('input_frequency', 0),  # Hardcoded 60Hz when on mains
            "outputVolt": CONFIG['mains_voltage'],  # v1.0.33: configurable, nominal output matches input
            "outputCurr": power_data.get('output_current', 0.0),  # From NUT battery.current
            "outputLoad": power_data.get('output_load', 0),  # Calculated from current * voltage
            "outputSource": "Battery" if "DISCHRG" in power_data.get('ups_status', '') else "Utility Power",
            "temp": temp_c,  # Temperature in Celsius (from polynomial conversion)
            "batteryAge": battery_age,
            "facilityId": CONFIG['facility_id']
        }
        
        logger.info(f"Power log: Temp={temp_c}°C, Current={power_data.get('output_current', 0)}A, Load={power_data.get('output_load', 0)}%, InputV={power_data.get('input_voltage', 0)}V")
        
        return payload
    except Exception as e:
        logger.error(f"Error creating power log payload: {str(e)}")
        logger.exception("Full traceback:")
        return None

def load_power_log_state():
    """Load power log state from file
    
    Returns:
        dict with 'enabled', 'interval_minutes', 'last_sent_time'
    """
    try:
        if os.path.exists(CONFIG['power_log_state_file']):
            with open(CONFIG['power_log_state_file'], 'r') as f:
                return json.load(f)
        else:
            # Default state: enabled, 2 minute interval, never sent
            return {
                'enabled': True,
                'interval_minutes': 2,
                'last_sent_time': None
            }
    except Exception as e:
        logger.warning(f"Error loading power log state: {e}")
        return {
            'enabled': True,
            'interval_minutes': 2,
            'last_sent_time': None
        }

def save_power_log_state(enabled, interval_minutes):
    """Save power log enabled and interval settings to state file
    
    Args:
        enabled: Boolean, whether power logging is enabled
        interval_minutes: Integer, interval in minutes between power logs
    """
    try:
        # Load existing state to preserve last_sent_time
        state = load_power_log_state()
        
        # Update settings
        state['enabled'] = enabled
        state['interval_minutes'] = interval_minutes
        
        # Ensure directory exists
        os.makedirs(os.path.dirname(CONFIG['power_log_state_file']), exist_ok=True)
        
        # Write state
        with open(CONFIG['power_log_state_file'], 'w') as f:
            json.dump(state, f, indent=2)
        
        logger.debug(f"Saved power log state: enabled={enabled}, interval={interval_minutes} minutes")
    except Exception as e:
        logger.error(f"Error saving power log state: {e}")

def update_last_power_log_time():
    """Update the last power log sent time to now"""
    try:
        state = load_power_log_state()
        state['last_sent_time'] = datetime.now(timezone.utc).isoformat()
        
        # Ensure directory exists
        os.makedirs(os.path.dirname(CONFIG['power_log_state_file']), exist_ok=True)
        
        with open(CONFIG['power_log_state_file'], 'w') as f:
            json.dump(state, f, indent=2)
        
        logger.debug(f"Updated last power log time: {state['last_sent_time']}")
    except Exception as e:
        logger.error(f"Error updating power log time: {e}")

def get_current_call_home_interval():
    """Get current call home interval from systemd timer
    
    Returns:
        int: Current interval in minutes, or None if unable to read
    """
    try:
        result = subprocess.run(
            ['systemctl', 'show', 'hmpd_python.timer', '--property=TimersCalendar'],
            capture_output=True, text=True, timeout=10
        )
        # Try to extract interval from OnUnitActiveSec
        result2 = subprocess.run(
            ['grep', 'OnUnitActiveSec', '/etc/systemd/system/hmpd_python.timer'],
            capture_output=True, text=True, timeout=10
        )
        if result2.returncode == 0:
            # Parse "OnUnitActiveSec=3min" or "OnUnitActiveSec=10min"
            match = re.search(r'OnUnitActiveSec=(\d+)min', result2.stdout)
            if match:
                return int(match.group(1))
        return None
    except Exception as e:
        logger.debug(f"Could not read current timer interval: {e}")
        return None

def update_call_home_interval(interval_minutes):
    """Update the systemd timer with new call home interval from Azure
    
    Args:
        interval_minutes: Integer, interval in minutes (10-240)
    
    Returns:
        bool: True if successful, False otherwise
    """
    try:
        # Validate interval (Azure allows 10-240 minutes)
        interval_minutes = int(interval_minutes)
        if interval_minutes < 10 or interval_minutes > 240:
            logger.warning(f"Call home interval {interval_minutes} out of range (10-240), ignoring")
            return False
        
        # Check current interval to avoid unnecessary updates
        current_interval = get_current_call_home_interval()
        if current_interval == interval_minutes:
            logger.debug(f"Call home interval already set to {interval_minutes} minutes")
            return True
        
        timer_file = '/etc/systemd/system/hmpd_python.timer'
        
        # Read current timer file
        with open(timer_file, 'r') as f:
            timer_content = f.read()
        
        # Update OnUnitActiveSec value
        new_content = re.sub(
            r'OnUnitActiveSec=\d+min',
            f'OnUnitActiveSec={interval_minutes}min',
            timer_content
        )
        
        if new_content == timer_content:
            logger.warning("Could not find OnUnitActiveSec in timer file")
            return False
        
        # Write updated timer file
        with open(timer_file, 'w') as f:
            f.write(new_content)
        
        # Reload systemd daemon
        subprocess.run(['systemctl', 'daemon-reload'], check=True, timeout=30)
        
        # Restart timer to apply new interval
        subprocess.run(['systemctl', 'restart', 'hmpd_python.timer'], check=True, timeout=30)
        
        logger.info(f"✓ Call home interval updated from {current_interval}min to {interval_minutes}min")
        return True
        
    except Exception as e:
        logger.error(f"Error updating call home interval: {e}")
        return False

def should_send_power_log():
    """Check if power log should be sent based on enabled flag and interval
    
    Returns:
        True if power log should be sent, False otherwise
    """
    try:
        state = load_power_log_state()
        
        # Check if power logging is enabled
        if not state.get('enabled', True):
            return False
        
        # Check if enough time has elapsed since last send
        last_sent = state.get('last_sent_time')
        if last_sent is None:
            # Never sent before, send now
            return True
        
        # Parse last sent time
        last_sent_dt = datetime.fromisoformat(last_sent)
        now = datetime.now(timezone.utc)
        
        # Calculate elapsed time in minutes
        elapsed_minutes = (now - last_sent_dt).total_seconds() / 60
        
        # Get interval from state and ensure it's an integer
        interval_minutes = int(state.get('interval_minutes', 2))
        
        # Send if interval has elapsed
        should_send = elapsed_minutes >= interval_minutes
        
        if should_send:
            logger.debug(f"Power log interval elapsed: {elapsed_minutes:.1f} >= {interval_minutes} minutes")
        else:
            logger.debug(f"Power log interval not elapsed: {elapsed_minutes:.1f} < {interval_minutes} minutes")
        
        return should_send
        
    except Exception as e:
        logger.error(f"Error checking power log interval: {e}")
        # On error, default to sending (safer to send than not send)
        return True

# ============================================================
# OTA SELF-UPDATE (v1.0.27)
# ============================================================

# OTA manifest URLs. Tried in order; first reachable wins.
#
# v1.0.41: Primary moved off the user's personal Dropbox to a public GitHub raw
# URL on Howard-Medical/sip-releases. Dropbox URL kept as a fallback for ONE
# release to cover hospitals where GitHub is firewalled — will be removed in
# v1.0.42 once SRHS + Abrazo carts are confirmed reaching GitHub. Same threat
# model as v1.0.38: the URLs are code constants. The writer set is now the
# Howard-Medical GitHub org rather than "anyone with the Dropbox link."
#
# v1.0.38: HARDCODED — env override removed. Previously os.getenv() allowed an
# attacker with shell access (e.g. via SSH pi:123) to write a malicious
# OTA_MANIFEST_URL into /home/pi/.env or a systemd drop-in and pwn the cart on
# the next OTA tick. The SHA256 in the manifest is NOT a signature: whoever
# writes the manifest also writes the hash, so URL redirection = arbitrary code
# execution as root. Until manifest signing (Ed25519) lands, the URL is a code
# constant.
#
# Manifest JSON shape: { "version": "1.0.41", "url": "https://...", "sha256": "<hex>" }
# Regenerate with: scripts/ota/build_ota_manifest.py
OTA_MANIFEST_URL_PRIMARY = (
    'https://raw.githubusercontent.com/Howard-Medical/sip-releases/main/'
    'daemon-manifest.json'
)
OTA_MANIFEST_URL_FALLBACK = (
    'https://www.dropbox.com/scl/fi/pqhb1xtcxjo26h2g5w2mp/hmpd_manifest.json'
    '?rlkey=g55bt70yxkhwg0cl55u8lqvqw&st=7lfqzvmr&dl=1'
)
OTA_MANIFEST_URLS = (OTA_MANIFEST_URL_PRIMARY, OTA_MANIFEST_URL_FALLBACK)

# E3 firmware OTA — Dropbox-hosted Intel-HEX binary for the Care Pro (E3) NXP board.
# Manifest JSON shape: { "firmware_version": "2.1.36", "url": "https://...&dl=1", "sha256": "<hex>" }
# Regenerate with: scripts/ota/build_e3_firmware_manifest.py
# Empty string disables the feature (E2 carts always skip).
# PLACEHOLDER URL — replace with the production Dropbox link once Mike Breland
# publishes the first real .hex.
E3_FIRMWARE_MANIFEST_URL = os.getenv(
    'E3_FIRMWARE_MANIFEST_URL',
    ''
)
E3_FIRMWARE_STAGING_DIR = '/var/lib/hmpd/firmware_staging'
E3_FIRMWARE_STATE_FILE  = '/var/lib/hmpd/e3_firmware_state.json'
E3_FLASH_IN_PROGRESS    = '/var/lib/hmpd/e3_flash_in_progress.json'
E3_LAST_FLASH_FILE      = '/var/lib/hmpd/last_e3_flash.json'

# Beacon (E3 task-light) state — server sets cartProfile.beacon (or
# response_data.beacon) to Y0-Y9; the firmware holds the LED in the last
# state continuously, so we only send a command on state CHANGE.
# Y0 = off; Y1-Y9 = colors. E2 carts have no task light — gated by cart_type.
BEACON_STATE_FILE = '/var/lib/hmpd/beacon_state.json'

def check_and_apply_ota_update():
    """Check Azure Blob for a newer version of hmpd_python.py and apply it.

    Flow:
      1. Download manifest JSON (fast, ~200 bytes)
      2. Compare manifest version against SCRIPT_VERSION
      3. If newer: download new script, verify SHA256, atomic replace, log & exit
         so the next systemd timer tick runs the new version automatically.
      4. If same or older: log and continue normally.

    Atomic replace: write to .tmp file first, then os.replace() — safe even if power
    is lost mid-download (the current script is never touched until checksum passes).

    Returns:
        True  — update was applied (caller should exit so systemd restarts cleanly)
        False — no update available or update failed (continue normal run)
    """
    try:
        # v1.0.41: Iterate primary then fallback so a hospital firewall blocking
        # GitHub still picks up updates via Dropbox during the migration window.
        manifest = None
        for _ota_url in OTA_MANIFEST_URLS:
            try:
                logger.info('OTA: Checking for updates at ' + _ota_url[:80])
                resp = requests.get(_ota_url, timeout=10)
                if resp.status_code == 200:
                    manifest = resp.json()
                    break
                logger.debug('OTA: manifest HTTP ' + str(resp.status_code) + ' at ' + _ota_url[:80])
            except (requests.RequestException, ValueError) as e:
                logger.debug('OTA: manifest fetch failed at ' + _ota_url[:80] + ': ' + str(e))
        if manifest is None:
            logger.debug('OTA: no manifest URL reachable — skipping')
            return False
        remote_version = manifest.get('version', '')
        remote_url     = manifest.get('url', '')
        remote_sha256  = manifest.get('sha256', '')

        if not remote_version or not remote_url or not remote_sha256:
            logger.debug('OTA: manifest missing fields — skipping')
            return False

        # Compare semantic versions (simple tuple comparison)
        def _ver(v):
            try:
                return tuple(int(x) for x in v.strip().split('.'))
            except Exception:
                return (0, 0, 0)

        if _ver(remote_version) <= _ver(SCRIPT_VERSION):
            logger.info('OTA: already up to date (local=' + SCRIPT_VERSION + ' remote=' + remote_version + ')')
            return False

        logger.info('OTA: NEW VERSION AVAILABLE: ' + SCRIPT_VERSION + ' -> ' + remote_version)
        logger.info('OTA: Downloading from ' + remote_url)

        dl = requests.get(remote_url, timeout=60)
        if dl.status_code != 200:
            logger.warning('OTA: download failed (HTTP ' + str(dl.status_code) + ')')
            return False

        # Verify SHA256 checksum before touching anything
        import hashlib as _hl
        actual_sha256 = _hl.sha256(dl.content).hexdigest()
        if actual_sha256.lower() != remote_sha256.lower():
            logger.error('OTA: CHECKSUM MISMATCH — aborting update')
            logger.error('OTA:   expected ' + remote_sha256)
            logger.error('OTA:   got      ' + actual_sha256)
            return False

        # Atomic replace: write to .tmp, syntax-check, backup, rename
        script_path = os.path.abspath(__file__)
        tmp_path    = script_path + '.ota_tmp'
        with open(tmp_path, 'wb') as f:
            f.write(dl.content)
        os.chmod(tmp_path, 0o755)

        # v1.0.33: Syntax-check BEFORE replacing (catches SyntaxError, import typos)
        try:
            py_compile.compile(tmp_path, doraise=True)
        except py_compile.PyCompileError as pce:
            logger.error('OTA: SYNTAX ERROR in downloaded script — aborting update')
            logger.error('OTA:   %s', pce)
            try:
                os.unlink(tmp_path)
            except OSError:
                pass
            return False

        # v1.0.33: Backup current script for manual rollback
        backup_path = script_path + '.previous'
        try:
            import shutil
            shutil.copy2(script_path, backup_path)
            logger.info('OTA: Backed up current script to %s', backup_path)
        except Exception as bk_err:
            logger.warning('OTA: Could not create backup (proceeding anyway): %s', bk_err)

        os.replace(tmp_path, script_path)  # Atomic on Linux

        logger.info('OTA: Update applied successfully (' + remote_version + ')')
        logger.info('OTA: Exiting — systemd timer will restart with new version on next tick')

        # Write a flag so hmpd-status can show the last update time
        try:
            with open('/var/lib/hmpd/last_ota_update', 'w') as f:
                f.write('version=' + remote_version + '\n')
                f.write('timestamp_utc=' + datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ') + '\n')
        except Exception:
            pass

        return True  # Caller should exit cleanly

    except Exception as e:
        logger.warning('OTA: check failed (non-fatal): ' + str(e))
        return False


# ============================================================
# E3 FIRMWARE OTA (Pi-driven flash via W1 + HID bootloader)
# ============================================================

def _read_last_e3_flash_version():
    """Return the new_version recorded by the most recent flash, or None."""
    try:
        with open(E3_LAST_FLASH_FILE) as f:
            return (json.load(f) or {}).get('new_version')
    except Exception:
        return None


def _read_e3_firmware_state():
    try:
        with open(E3_FIRMWARE_STATE_FILE) as f:
            return json.load(f) or {}
    except Exception:
        return {}


def _write_e3_firmware_state(state):
    try:
        os.makedirs(os.path.dirname(E3_FIRMWARE_STATE_FILE), exist_ok=True)
        with open(E3_FIRMWARE_STATE_FILE, 'w') as f:
            json.dump(state, f, indent=2)
    except Exception as e:
        logger.warning('E3-OTA: state write failed: ' + str(e))


def _ver_tuple(v):
    try:
        return tuple(int(x) for x in str(v).strip().split('.'))
    except Exception:
        return (0, 0, 0)


def _invoke_e3_flasher(hex_path, expected_version=None, resume=False):
    """Run daemon/hmpd_flash_e3.py as a subprocess.

    The daemon is already holding /var/lib/hmpd/hmpd.lock; we pass --no-lock
    so the flasher doesn't try to grab it again. Returns the flasher's exit
    code (0 = success).
    """
    flasher_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                'hmpd_flash_e3.py')
    if not os.path.isfile(flasher_path):
        logger.error('E3-OTA: flasher not found at ' + flasher_path)
        return 1
    cmd = ['python3', flasher_path, hex_path, '--no-lock']
    if expected_version:
        cmd.extend(['--expected-version', expected_version])
    if resume:
        cmd.append('--resume-bootloader')
    logger.info('E3-OTA: invoking ' + ' '.join(cmd))
    try:
        # No timeout — a long erase + program can legitimately take 60+ seconds.
        # The bootloader's no-timeout-during-program protects against indefinite
        # hangs at the firmware level.
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
        if result.stdout:
            logger.info('E3-OTA: flasher stdout:\n' + result.stdout)
        if result.stderr:
            # Flasher logs to stderr by design; INFO-level for the daemon log
            logger.info('E3-OTA: flasher log:\n' + result.stderr)
        return result.returncode
    except subprocess.TimeoutExpired:
        logger.error('E3-OTA: flasher timed out (10 min) — cart may be stuck in bootloader')
        return 2
    except Exception as e:
        logger.error('E3-OTA: flasher invocation failed: ' + str(e))
        return 1


def resume_pending_e3_flash():
    """Called early in main(). If a prior flash was interrupted, attempt
    to resume it before the regular telemetry cycle starts.

    Trigger: e3_flash_in_progress.json exists. The cart is most likely
    stuck in bootloader mode; the flasher's --resume-bootloader path skips
    the W1 trigger and goes straight to programming the recorded .hex.
    """
    if not os.path.exists(E3_FLASH_IN_PROGRESS):
        return
    try:
        with open(E3_FLASH_IN_PROGRESS) as f:
            state = json.load(f) or {}
    except Exception as e:
        logger.warning('E3-OTA: in-progress file unreadable, removing: ' + str(e))
        try: os.unlink(E3_FLASH_IN_PROGRESS)
        except Exception: pass
        return

    hex_path = state.get('hex_path')
    expected_version = state.get('expected_version')
    if not hex_path or not os.path.exists(hex_path):
        logger.warning('E3-OTA: in-progress flag set but staged hex missing — clearing')
        try: os.unlink(E3_FLASH_IN_PROGRESS)
        except Exception: pass
        return

    logger.warning('=' * 60)
    logger.warning('E3-OTA: resuming interrupted firmware flash')
    logger.warning('  hex:     ' + hex_path)
    logger.warning('  version: ' + str(expected_version))
    logger.warning('=' * 60)
    rc = _invoke_e3_flasher(hex_path, expected_version=expected_version, resume=True)
    if rc == 0:
        logger.info('E3-OTA: resume flash succeeded')
        new_ver = _read_last_e3_flash_version() or expected_version
        st = _read_e3_firmware_state()
        st['last_applied_version'] = new_ver
        st['last_check_utc'] = datetime.now(timezone.utc).isoformat()
        _write_e3_firmware_state(st)
        # Also remove the staged hex now that it's applied
        try: os.unlink(hex_path)
        except Exception: pass
    else:
        logger.error('E3-OTA: resume flash returned exit code ' + str(rc))


def check_and_apply_e3_firmware_update(running_e3_version=None):
    """Fetch the E3 firmware manifest, compare to last-applied version, flash if newer.

    Skips entirely if:
      - cart is not E3
      - manifest URL is unset (feature disabled)
      - manifest fetch fails or shape is wrong
      - cart is on battery (defer to next cycle when AC is restored)

    Returns True if a flash was applied (caller should expect serial state
    refresh on the next cycle), False otherwise.
    """
    if CONFIG.get('cart_type') != 'E3':
        return False
    if not E3_FIRMWARE_MANIFEST_URL:
        logger.debug('E3-OTA: manifest URL unset — feature disabled')
        return False

    try:
        resp = requests.get(E3_FIRMWARE_MANIFEST_URL, timeout=10)
        if resp.status_code != 200:
            logger.info('E3-OTA: manifest HTTP ' + str(resp.status_code) + ' — skipping')
            return False
        manifest = resp.json()
    except Exception as e:
        logger.info('E3-OTA: manifest fetch failed (non-fatal): ' + str(e))
        return False

    fw_version = manifest.get('firmware_version', '')
    fw_url     = manifest.get('url', '')
    fw_sha256  = manifest.get('sha256', '').lower()
    if not fw_version or not fw_url or not fw_sha256:
        logger.info('E3-OTA: manifest missing required fields — skipping')
        return False

    state = _read_e3_firmware_state()
    last_applied = state.get('last_applied_version')

    # First-run reconciliation: if we've never recorded a state and the
    # cart is already on the manifest version, just record it. Don't reflash.
    if last_applied is None and running_e3_version:
        if fw_version in running_e3_version or _ver_tuple(running_e3_version) == _ver_tuple(fw_version):
            logger.info('E3-OTA: first run — cart already on manifest version ' + fw_version + ', recording state')
            state['last_applied_version'] = running_e3_version
            state['last_applied_sha256']  = fw_sha256
            state['last_check_utc']       = datetime.now(timezone.utc).isoformat()
            _write_e3_firmware_state(state)
            return False

    # Always update the last_check timestamp
    state['last_check_utc'] = datetime.now(timezone.utc).isoformat()

    if _ver_tuple(fw_version) <= _ver_tuple(last_applied or '0.0.0'):
        logger.info('E3-OTA: cart already on or ahead of manifest (last_applied=' +
                    str(last_applied) + ' manifest=' + fw_version + ')')
        _write_e3_firmware_state(state)
        return False

    logger.info('=' * 60)
    logger.info('E3-OTA: NEW FIRMWARE AVAILABLE: ' + str(last_applied) + ' -> ' + fw_version)
    logger.info('=' * 60)

    # Power gate — refuse to flash on battery, defer to a later cycle.
    try:
        upsc = subprocess.run(['upsc', 'tdi@localhost'], capture_output=True,
                              text=True, timeout=5)
        ups_status = ''
        ups_charge = 0.0
        for ln in upsc.stdout.splitlines():
            if ln.startswith('ups.status:'):
                ups_status = ln.split(':', 1)[1].strip()
            elif ln.startswith('battery.charge:'):
                try: ups_charge = float(ln.split(':', 1)[1].strip())
                except Exception: pass
        if 'OL' not in ups_status or ups_charge < 30:
            logger.warning('E3-OTA: deferring — power gate (status=' + ups_status +
                           ' charge=' + str(ups_charge) + '%)')
            _write_e3_firmware_state(state)
            return False
    except Exception as e:
        logger.warning('E3-OTA: power probe failed, deferring: ' + str(e))
        _write_e3_firmware_state(state)
        return False

    # Stage the hex (persistent, survives reboot for resume-on-startup)
    try:
        os.makedirs(E3_FIRMWARE_STAGING_DIR, exist_ok=True)
        hex_path = os.path.join(E3_FIRMWARE_STAGING_DIR,
                                'e3_firmware_' + fw_sha256[:16] + '.hex')
        logger.info('E3-OTA: downloading ' + fw_url)
        dl = requests.get(fw_url, timeout=120)
        if dl.status_code != 200:
            logger.error('E3-OTA: download HTTP ' + str(dl.status_code))
            _write_e3_firmware_state(state)
            return False
        actual = hashlib.sha256(dl.content).hexdigest().lower()
        if actual != fw_sha256:
            logger.error('E3-OTA: SHA256 MISMATCH — expected ' + fw_sha256 + ' got ' + actual)
            _write_e3_firmware_state(state)
            return False
        with open(hex_path, 'wb') as f:
            f.write(dl.content)
        logger.info('E3-OTA: staged ' + hex_path + ' (' + str(len(dl.content)) + ' bytes)')
    except Exception as e:
        logger.error('E3-OTA: staging failed: ' + str(e))
        _write_e3_firmware_state(state)
        return False

    # Invoke the flasher subprocess. Daemon lock is held by us; flasher uses --no-lock.
    rc = _invoke_e3_flasher(hex_path, expected_version=fw_version, resume=False)

    if rc == 0:
        logger.info('E3-OTA: flash succeeded — recording state and removing staged hex')
        state['last_applied_version'] = fw_version
        state['last_applied_sha256']  = fw_sha256
        _write_e3_firmware_state(state)
        try: os.unlink(hex_path)
        except Exception: pass
        return True

    if rc == 2:
        # Flasher left the cart in the bootloader. Keep the staged hex and the
        # in-progress flag so the next cycle (or a daemon restart) can resume.
        logger.error('E3-OTA: flash interrupted (rc=2) — staged hex retained for resume')
    elif rc == 3:
        # Post-flash app verification failed. The cart booted into something —
        # could be the new firmware reporting an unexpected version string, or
        # the app failed to come up at all. Don't loop on it; clear the state
        # and surface the failure.
        logger.error('E3-OTA: post-flash app verification FAILED (rc=3)')
        try: os.unlink(hex_path)
        except Exception: pass
    else:
        logger.error('E3-OTA: flash precondition or invocation failed (rc=' + str(rc) + ')')
        try: os.unlink(hex_path)
        except Exception: pass

    _write_e3_firmware_state(state)
    return False


def main():
    """Main execution function"""
    logger.info("=" * 60)
    logger.info(f"HMPD Python v{SCRIPT_VERSION} - Starting")
    logger.info("=" * 60)

    # v1.0.33: Concurrent-run protection — only one instance at a time.
    # flock is automatically released on process exit (even on SIGKILL).
    try:
        os.makedirs('/var/lib/hmpd', exist_ok=True)
        _lock_fd = open('/var/lib/hmpd/hmpd.lock', 'w')
        fcntl.flock(_lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (IOError, OSError):
        logger.warning("Another instance is already running — exiting")
        return False

    # LAST_ATTEMPT HEARTBEAT (v1.0.27): Written immediately at startup, before any I/O.
    # Distinguishes a HANGING run (last_attempt stale, last_callhome stale) from a
    # FAILING run (last_attempt fresh, last_callhome stale). Critical for field triage.
    try:
        _ts = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
        with open('/var/lib/hmpd/last_attempt', 'w') as _f:
            _f.write('timestamp_utc=' + _ts + '\n')
            _f.write('version=' + SCRIPT_VERSION + '\n')
    except Exception:
        pass  # Non-fatal

    # E3 FIRMWARE OTA — startup resume. If a prior callhome started a flash and
    # then died (power, kill, reboot), the cart may be parked in the HID
    # bootloader. Resume the flash before doing anything else — both because
    # leaving the cart in bootloader is bad (no audit logs, no telemetry) and
    # because no other serial work can succeed until the app is back.
    try:
        resume_pending_e3_flash()
    except Exception as _e:
        logger.warning("E3-OTA resume check failed (non-fatal): " + str(_e))
    
    # Console-friendly header
    print("\n" + "="*70)
    print(f"🚀 HMPD Python v{SCRIPT_VERSION} - Manual CallHome")
    print(f"📅 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*70 + "\n")
    
    # Run pre-callhome health checks (NUT, WiFi, memory, watchdog)
    run_health_checks()
    
    # Clock sync is handled inside run_health_checks() via sync_clocks().
    # The old e2_time_synced flag has been replaced with delta-based sync
    # (new board year<2020 triggers immediate sync; healthy boards just log drift).
    
    # Get authentication token
    token = get_auth_token()
    if not token:
        logger.error("Failed to get authentication token")
        return False
    
    # Retry any cached failed payloads from previous runs
    retry_cached_payloads(token)
    
    # ── PHASE 1: Serial READ (v1.0.32 — single connection) ────────────────────
    # DECOUPLING (v1.0.27): E2 board failure is no longer fatal. If the board is
    # unavailable (USB crash, cable issue, NXP bootloader timing), we still send
    # power telemetry and WiFi data — giving Azure visibility that the Pi is alive.
    board_time = None  # Cached for create_power_log_payload (avoids extra serial open)
    board_users = []
    try:
        with E2Serial() as ser:
            e2_data = read_e2_board_data(ser=ser)
            if e2_data is not None:
                # Cache board time from D0 for power log timestamp
                board_time = read_e2_board_time(ser=ser)
                # HEIGHT SYNC (v1.0.25): Read user heights from board
                try:
                    board_users = read_users_from_e2_board(ser=ser)
                except Exception as height_err:
                    logger.warning(f"Height sync read failed (non-fatal): {height_err}")
    except serial.SerialException:
        e2_data = None  # Board unavailable — fall through to degraded mode

    e2_available = e2_data is not None
    if not e2_available:
        logger.warning("E2 board unavailable — proceeding in DEGRADED MODE (power+WiFi only)")
        e2_data = {
            'firmware': 'UNAVAILABLE',
            'serial': 'UNAVAILABLE',
            'battery': '',
            'status': '',
            'drawer_config': '',
            'audit_logs': []
        }

    # Upload height changes (network only, no serial needed)
    if e2_available and board_users:
        try:
            upload_height_changes_to_azure(board_users, token)
        except Exception as height_err:
            logger.warning(f"Height sync upload failed (non-fatal): {height_err}")
    elif not e2_available:
        logger.info("Height sync skipped — E2 board unavailable (degraded mode)")
    
    # Log detected cart type prominently
    cart_type = CONFIG['cart_type']
    logger.info("=" * 60)
    if cart_type == 'E3':
        logger.info("🏥 CART TYPE: Care Pro (E3) — Height presets ACTIVE")
    else:
        logger.info("🏥 CART TYPE: Care-E2 — Height presets DISABLED (4-field U1)")
    logger.info(f"   AP Whitelist: Available on both E2 and E3")
    logger.info("=" * 60)
    
    # Get power data
    # DECOUPLING (v1.0.46): UPS/NUT failure is no longer fatal — mirrors the
    # v1.0.27 E2-board decoupling above. A cart with a dead/absent TDI module
    # used to send NOTHING and simply vanish from the Fleet Manager dashboard
    # (the exact carts that most need visibility, e.g. Hartford's known
    # power-problem carts). Now it calls home with empty power fields; the
    # power LOG is skipped while degraded (no fabricated readings).
    power_data = get_power_data()
    power_available = power_data is not None
    if not power_available:
        logger.warning("TDI power data unavailable — proceeding in DEGRADED MODE (board+WiFi only)")
        power_data = {
            'battery_capacity': '',
            'battery_voltage': '',
            'battery_state': '',
            'serial_number': CONFIG['cart_serial'],
            'firmware': '',
            'manufacturer': '',
            'model': '',
            'ip_address': get_local_ip(),
            'battery_installed': '',
            'battery_runtime': '',
            'battery_temp': '',
            'output_current': 0,
            'output_load': 0,
            'input_voltage': 0,
            'input_frequency': 0,
            'ups_status': 'UNAVAILABLE'
        }

    # Check AP whitelist compliance against currently stored whitelist
    ap_compliant, whitelist_active = True, False
    try:
        _, ap_mac_check, _ = get_wifi_info()
        ap_compliant, whitelist_active = check_ap_whitelist(ap_mac_check)
    except Exception as e:
        logger.debug(f"AP whitelist check failed: {e}")

    roaming_alert_active = bool(whitelist_active and not ap_compliant)
    if e2_available:
        if CONFIG.get('cart_type') == 'E3':
            try:
                with E2Serial() as ser:
                    apply_roaming_alert_command(roaming_alert_active, ser=ser)
            except serial.SerialException as _se:
                logger.warning(f"Roaming alert serial command failed: {_se}")
        elif roaming_alert_active:
            logger.info(
                f"Roaming alert command skipped — cart_type={CONFIG.get('cart_type')} "
                "(C1/C0 is E3/Pro firmware only)"
            )

    # Create and send device payload
    device_payload = create_device_payload(e2_data, power_data)
    if device_payload:
        # Send device data and get response (for cart profile sync)
        response = send_data(CONFIG['endpoint'], device_payload, token, return_response=True)
        if response:
            logger.info("✓ Successfully sent device data to Azure")
            
            # Check for cart profile in response
            try:
                response_data = response.json()
                logger.debug(f"Azure response data: {json.dumps(response_data, indent=2)}")
                
                # Check if this is a new record (first time cart)
                new_record = response_data.get('newRecord', False)
                logger.info(f"New Record: {new_record}")
                
                # Only apply profile if NOT a new record (same logic as Windows service)
                if not new_record:
                    # v1.0.32: Initialize write-phase variables before any branching
                    _profile_to_write = None
                    _profile_cart_id = None
                    _profile_asset_tag = None
                    _users_to_write = None
                    _beacon_cmd = None

                    # Check for cart profile
                    cart_profile = response_data.get('cartProfile')
                    if cart_profile and cart_profile.get('name'):
                        logger.info(f"Cart profile received from Azure: {cart_profile.get('name')}")

                        # Store power log settings from Azure profile
                        power_log_enabled = cart_profile.get('powerLogEnabled', True)  # Default to True for backward compatibility
                        # v1.0.43: Azure occasionally returns powerLogInterval as '' or null (seen on SRHS Dustin cart).
                        # Stock int(...) raised ValueError and aborted the rest of the post-callhome handler (drawer
                        # codes never written, users never applied). Treat blank/non-numeric as "use the 2-minute default."
                        raw_power_log_interval = cart_profile.get('powerLogInterval', 2)
                        try:
                            power_log_interval = int(raw_power_log_interval or 2)
                        except (TypeError, ValueError):
                            logger.warning(f"Invalid powerLogInterval from Azure: {raw_power_log_interval!r}; falling back to default 2 minutes")
                            power_log_interval = 2

                        logger.info(f"Power Log Enabled: {power_log_enabled}")
                        logger.info(f"Power Log Interval: {power_log_interval} minutes")
                        
                        # Save power log settings to state file
                        save_power_log_state(power_log_enabled, power_log_interval)
                        
                        # Update call home interval from Azure profile (10-240 minutes)
                        call_home_interval = cart_profile.get('callHomeInterval')
                        if call_home_interval is not None:
                            call_home_interval = int(call_home_interval)
                            logger.info(f"Call Home Interval from Azure: {call_home_interval} minutes")
                            if update_call_home_interval(call_home_interval):
                                logger.info("✓ Call home interval updated from Azure")
                            else:
                                logger.debug("Call home interval not changed")
                        
                        # AP Whitelist — save whenever received from Azure (independent of relockTimer)
                        # v1.0.36: Azure sends apWhitelistCluster at the TOP LEVEL of the response
                        # (not inside cartProfile). Check response_data first, then cart_profile as fallback.
                        # Format: {"name": "...", "apWhitelistItems": [{"name": "AP1", "macAddress": "00:12:25:55:22:88"}]}
                        ap_cluster = response_data.get('apWhitelistCluster') or cart_profile.get('apWhitelistCluster')
                        ap_whitelist_flat = response_data.get('apWhitelist') or cart_profile.get('apWhitelist')  # backward compat
                        if ap_cluster is not None:
                            items = ap_cluster.get('apWhitelistItems') or []
                            bssid_list = [item.get('macAddress', '') for item in items if item and item.get('macAddress')]
                            cluster_name = ap_cluster.get('name', 'unnamed')
                            save_ap_whitelist(bssid_list)
                            if bssid_list:
                                logger.info(f"✓ AP Whitelist received from cluster '{cluster_name}': {len(bssid_list)} approved BSSIDs")
                            else:
                                logger.info(f"✓ AP Whitelist cluster '{cluster_name}' is empty — no BSSID restrictions")
                        elif ap_whitelist_flat is not None:
                            # Legacy flat format: apWhitelist = ["bssid1", "bssid2"]
                            save_ap_whitelist(ap_whitelist_flat)
                            if ap_whitelist_flat:
                                logger.info(f"✓ AP Whitelist received (flat): {len(ap_whitelist_flat)} approved BSSIDs")
                            else:
                                logger.info("✓ AP Whitelist cleared (no BSSID restrictions)")

                        # ── PHASE 2: Serial WRITE (v1.0.32 — single connection) ─────
                        # Only apply if RelockTimer is present (same logic as Windows)
                        if cart_profile.get('relockTimer'):
                            _profile_to_write = cart_profile
                            _profile_cart_id = response_data.get('cartId')
                            _profile_asset_tag = response_data.get('assetTag')
                        else:
                            logger.info("Cart profile received but no relockTimer - skipping profile sync")
                    else:
                        logger.info("No cart profile in Azure response")

                    # Beacon — server-driven find-me workflow for E3 task light.
                    # Operator clicks "Find this cart" in Fleet Manager → server sets
                    # beacon/findMeBeacon = "Y3" (or chosen color) along with updateProfileOnNextConnect
                    # → Pi sends Y command on this callhome → cart lights up. Operator
                    # clicks "Stop" → server sets beacon/findMeBeacon = "Y0" → Pi turns off.
                    # Independent of cartProfile.relockTimer (so a beacon-only update
                    # doesn't need a full profile push). E2 carts ignore — gated below.
                    _beacon_cmd = (
                        response_data.get('beacon')
                        or response_data.get('findMeBeacon')
                        or (cart_profile or {}).get('beacon')
                        or (cart_profile or {}).get('findMeBeacon')
                    )
                    if _beacon_cmd:
                        logger.info(f"Beacon command received from Azure: {_beacon_cmd!r}")

                    # Check for user list in response
                    cart_users = response_data.get('cartUsers')
                    if cart_users is not None:  # Check for None specifically (empty list is valid)
                        logger.info(f"User list received from Azure: {len(cart_users)} users")
                        _users_to_write = cart_users
                    else:
                        # Fallback: call the dedicated cartusersrequest endpoint
                        logger.info("No user list in callhome response — trying cartusersrequest endpoint...")
                        try:
                            users_url = f"{CONFIG['cartusers_endpoint']}/{CONFIG['facility_id']}/"
                            users_headers = {
                                "Authorization": f"Bearer {token}",
                                "Content-Type": "application/json"
                            }
                            users_response = requests.post(
                                users_url,
                                headers=users_headers,
                                json=[],  # Diego's endpoint expects array body (Postman collection confirms)
                                timeout=30
                            )
                            if users_response.status_code == 200:
                                if users_response.text and users_response.text.strip():
                                    users_data = users_response.json()
                                    if users_data:
                                        logger.info(f"✓ User list from cartusersrequest: {len(users_data)} users")
                                        _users_to_write = users_data
                                    else:
                                        logger.info("cartusersrequest returned empty list — no users to sync")
                                else:
                                    logger.info("cartusersrequest returned 200 with empty body — no users assigned")
                            else:
                                logger.warning(f"cartusersrequest returned {users_response.status_code} — skipping user sync")
                        except Exception as ue:
                            logger.warning(f"cartusersrequest endpoint failed: {str(ue)} — skipping user sync")

                    # Execute all serial writes in a single connection
                    if e2_available and (_profile_to_write or _users_to_write is not None or _beacon_cmd):
                        try:
                            with E2Serial() as ser:
                                if _profile_to_write:
                                    profile_success = apply_cart_profile(_profile_to_write, _profile_cart_id, _profile_asset_tag, ser=ser)
                                    if profile_success:
                                        logger.info("✓ Cart profile applied successfully")
                                    else:
                                        logger.warning("⚠ Cart profile application had errors")
                                if _users_to_write is not None:
                                    users_success = write_users_to_e2_board(_users_to_write, CONFIG['cart_type'], ser=ser)
                                    if users_success:
                                        logger.info("✓ User list synced successfully")
                                    else:
                                        logger.warning("⚠ User list sync had errors")
                                if _beacon_cmd:
                                    if CONFIG.get('cart_type') == 'E3':
                                        apply_beacon_command(_beacon_cmd, ser=ser)
                                    else:
                                        logger.info(
                                            f"Beacon command {_beacon_cmd!r} ignored — "
                                            f"cart_type={CONFIG.get('cart_type')} (E2 has no task light)"
                                        )
                        except serial.SerialException as _se:
                            logger.warning(f"Serial write phase failed: {_se}")
                else:
                    logger.info("New record detected - skipping profile sync (will sync on next call home)")
                    
            except Exception as e:
                logger.error(f"Error processing Azure response: {str(e)}")
                logger.exception("Full traceback:")
        else:
            logger.error("✗ Failed to send device data")
    
    # Filter and send only new audit logs
    if e2_data.get('audit_logs'):
        new_logs = filter_new_logs(e2_data['audit_logs'])
        if new_logs:
            logs_endpoint = f"{CONFIG['endpoint']}/{CONFIG['facility_id']}/{socket.gethostname()}/{CONFIG['cart_id']}/{CONFIG['cart_serial']}"
            success = send_data(logs_endpoint, new_logs, token)
            if success:
                logger.info(f"✓ Successfully sent {len(new_logs)} new audit logs to Azure")
            else:
                logger.error("✗ Failed to send audit logs")
        else:
            logger.info("No new audit logs to send (all previously sent)")
    else:
        logger.info("No audit logs found on E2 board")
    
    # Create and send power log (only if enabled and interval elapsed)
    # v1.0.46: never send a power log built from the degraded-mode stub —
    # empty/zero readings would pollute the power history with fake rows.
    if not power_available:
        logger.info("Power log skipped — TDI power data unavailable (degraded mode)")
    elif should_send_power_log():
        power_log_payload = create_power_log_payload(power_data, board_time=board_time)
        if power_log_payload:
            power_endpoint = f"{CONFIG['endpoint']}/{CONFIG['facility_id']}/{socket.gethostname()}"
            success = send_data(power_endpoint, power_log_payload, token)
            if success:
                logger.info("✓ Successfully sent power log to Azure")
                logger.info(f"Power log details: {power_log_payload}")
                # Update last power log time
                update_last_power_log_time()
            else:
                logger.error("✗ Failed to send power log")
    else:
        state = load_power_log_state()
        if not state.get('enabled', True):
            logger.info("Power logging disabled in Azure profile - skipping power log")
        else:
            logger.info(f"Power log interval not elapsed (interval: {state.get('interval_minutes', 2)} minutes) - skipping power log")
    
    # ── AP Whitelist Enforcement (v1.0.37 — SAFE DISCONNECT) ────────────────
    # Hartford Pro default: whitelist mismatch means "wrong assigned
    # location/wing", so keep the cart connected and let Fleet Manager surface
    # the signal. Legacy disconnect/roam enforcement is opt-in only.
    if whitelist_active and not ap_compliant and not CONFIG.get('ap_whitelist_enforce_disconnect'):
        logger.warning("=" * 60)
        logger.warning("AP WHITELIST VIOLATION detected — notification-only mode")
        logger.warning("Cart stays connected; Fleet Manager should flag the assignment/location mismatch.")
        logger.warning("Set AP_WHITELIST_ENFORCE_DISCONNECT=1 only for explicit legacy enforcement tests.")
        logger.warning("=" * 60)
    # Legacy enforcement safety net: never disconnect WiFi unless an approved AP
    # is actually in range. Without this, a misconfigured whitelist can strand
    # the cart until physical intervention.
    #
    # Defense layers:
    #   1. Scan nearby APs before disconnecting
    #   2. Only disconnect if at least one approved BSSID is visible
    #   3. After disconnect, verify connectivity was restored
    #   4. If connectivity lost, force reconnect to ANY available network
    elif whitelist_active and not ap_compliant:
        logger.warning("=" * 60)
        logger.warning("AP WHITELIST VIOLATION detected — legacy enforcement enabled")
        logger.warning("=" * 60)
        try:
            # Detect wireless interface
            _iface = 'wlan0'
            _iw = subprocess.run(['ip', 'link', 'show'], capture_output=True, text=True, timeout=5)
            for _line in _iw.stdout.split('\n'):
                if 'wlan' in _line or 'wlx' in _line:
                    _parts = _line.strip().split(':')
                    if len(_parts) >= 2:
                        _iface = _parts[1].strip()
                        break

            # SAFETY CHECK 1: Scan for approved APs in range
            whitelist = load_ap_whitelist()
            _scan_result = subprocess.run(
                ['nmcli', '-t', '-f', 'BSSID', 'dev', 'wifi', 'list', '--rescan', 'yes'],
                capture_output=True, text=True, timeout=15
            )
            _nearby_macs = set()
            for _line in _scan_result.stdout.strip().split('\n'):
                _mac = _line.strip().replace('\\:', ':').lower().replace(':', '').replace('-', '')
                if _mac:
                    _nearby_macs.add(_mac)

            _approved_in_range = [b for b in whitelist if b in _nearby_macs]

            if not _approved_in_range:
                # ── NO APPROVED AP IN RANGE — DO NOT DISCONNECT ──────────
                logger.warning("=" * 60)
                logger.warning("AP WHITELIST: SKIPPING DISCONNECT — no approved AP in range!")
                logger.warning(f"  Whitelist has {len(whitelist)} approved BSSIDs")
                logger.warning(f"  Nearby APs found: {len(_nearby_macs)}")
                logger.warning(f"  Approved in range: 0")
                logger.warning("  Disconnecting would leave cart with NO connectivity.")
                logger.warning("  Cart stays connected — will retry on next callhome.")
                logger.warning("  ACTION: Verify AP Whitelist Cluster in Fleet Manager.")
                logger.warning("=" * 60)
            else:
                # ── APPROVED AP AVAILABLE — SAFE TO DISCONNECT ───────────
                logger.warning(f"AP WHITELIST: {len(_approved_in_range)} approved AP(s) in range — proceeding with disconnect")
                logger.warning('Disconnecting interface: ' + _iface)
                subprocess.run(['nmcli', 'dev', 'disconnect', _iface], check=False,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

                # SAFETY CHECK 2: Verify connectivity was restored
                # Give NetworkManager up to 30s to roam to an approved AP
                _reconnected = False
                for _wait in range(6):  # 6 × 5s = 30s max
                    time.sleep(5)
                    _ip_check = subprocess.run(
                        ['ip', '-4', 'addr', 'show', _iface],
                        capture_output=True, text=True, timeout=5
                    )
                    if 'inet ' in _ip_check.stdout:
                        _reconnected = True
                        logger.info(f"AP WHITELIST: Connectivity restored after {(_wait + 1) * 5}s")
                        break

                if not _reconnected:
                    # ── CONNECTIVITY LOST — EMERGENCY RECONNECT ──────────
                    logger.error("=" * 60)
                    logger.error("AP WHITELIST: CONNECTIVITY LOST after disconnect!")
                    logger.error("Emergency reconnect — forcing connection to any available network")
                    logger.error("=" * 60)
                    subprocess.run(['nmcli', 'dev', 'connect', _iface], check=False,
                                   capture_output=True, timeout=15)
                    time.sleep(5)
                    # Final check
                    _ip_final = subprocess.run(
                        ['ip', '-4', 'addr', 'show', _iface],
                        capture_output=True, text=True, timeout=5
                    )
                    if 'inet ' in _ip_final.stdout:
                        logger.info("AP WHITELIST: Emergency reconnect succeeded — cart is online")
                    else:
                        logger.critical("AP WHITELIST: Emergency reconnect FAILED — cart may be offline until next boot")
        except Exception as _e:
            logger.error(f"AP WHITELIST enforcement error (non-fatal): {_e}")

    # ── E3 FIRMWARE OTA (v1.0.39 — Pi-driven flash via W1 + HID bootloader) ──
    # Runs after telemetry + AP-whitelist work so a flash never blocks a callhome.
    # E2 carts and feature-disabled (no manifest URL) are no-ops. A flash takes
    # ~60s and only proceeds on AC power with battery >= 30%.
    try:
        _running_e3_version = None
        if e2_available:
            _fw = (e2_data.get('firmware') or '').strip()
            if _fw and _fw != 'UNAVAILABLE':
                _running_e3_version = _fw.split('\t')[-1].strip()
        check_and_apply_e3_firmware_update(running_e3_version=_running_e3_version)
    except Exception as _e:
        logger.warning("E3-OTA check failed (non-fatal): " + str(_e))

    logger.info("=" * 60)
    logger.info("HMPD Python - Completed")
    logger.info("=" * 60)

    # PERSISTENT HEARTBEAT (v1.0.26): Write last successful callhome timestamp to
    # persistent storage (/var/lib/hmpd/ is on eMMC/SD, NOT tmpfs). This survives
    # reboots and lets support staff verify field units with one command:
    #   cat /var/lib/hmpd/last_callhome
    try:
        os.makedirs('/var/lib/hmpd', exist_ok=True)
        _heartbeat_path = '/var/lib/hmpd/last_callhome'
        _now_utc = datetime.now(timezone.utc)
        _ts_utc = _now_utc.strftime('%Y-%m-%dT%H:%M:%SZ')
        _ts_local = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        _heartbeat_lines = [
            'timestamp_utc=' + _ts_utc,
            'timestamp_local=' + _ts_local,
            'hostname=' + socket.gethostname(),
            'version=' + SCRIPT_VERSION,
            'cart_id=' + str(CONFIG['cart_id']),
            'cart_type=' + str(CONFIG['cart_type']),
            'facility_id=' + str(CONFIG['facility_id']),
            'e2_status=' + ('OK' if e2_available else 'DEGRADED'),  # v1.0.28
        ]
        with open(_heartbeat_path, 'w') as _hf:
            _hf.write('\n'.join(_heartbeat_lines) + '\n')
        logger.info('Heartbeat written: ' + _ts_utc)
    except Exception as _he:
        logger.warning('Heartbeat write failed (non-fatal): ' + str(_he))

    # ── .env boot-partition backup (v1.0.32: encrypted) ────────────────────────
    # After every successful callhome, encrypt and mirror .env to the FAT32 boot
    # partition. FAT32 survives most SD card corruption scenarios that kill ext4.
    # v1.0.32: Encrypted with machine-id-derived key — FAT32 ignores chmod 600.
    try:
        _src = '/home/pi/.env'
        _plaintext = open(_src, 'rb').read()
        _encrypted = _encrypt_env(_plaintext)
        if _encrypted:
            _dst_candidates = ['/boot/firmware', '/boot']
            for _dst_dir in _dst_candidates:
                if os.path.isdir(_dst_dir) and os.access(_dst_dir, os.W_OK):
                    _dst_path = os.path.join(_dst_dir, 'hmpd_env_backup')
                    with open(_dst_path, 'wb') as _bf:
                        _bf.write(_encrypted)
                    logger.debug('.env backed up (encrypted) to ' + _dst_dir)
                    break
        else:
            logger.debug('.env backup skipped: encryption failed (no machine-id?)')
    except Exception as _be:
        logger.debug('.env backup skipped: ' + str(_be))  # Non-fatal

    # Console-friendly footer
    print("\n" + "="*70)
    print("✅ CALLHOME COMPLETED SUCCESSFULLY")
    print(f"📅 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*70 + "\n")

    # v1.0.33: Shutdown check moved to finally block in __main__ so it runs
    # even if main() throws an exception after the flag was set.
    return True

if __name__ == "__main__":
    try:
        # OTA check runs first — if update applied, exit cleanly so
        # systemd timer re-runs with the new script on the next tick.
        if check_and_apply_ota_update():
            exit(0)
        success = main()
        exit(0 if success else 1)
    except Exception as e:
        logger.error(f"Fatal error: {str(e)}")
        logger.exception("Full traceback:")
        exit(1)
    finally:
        # v1.0.33: ALWAYS check shutdown flag — runs even after exit() or exceptions.
        # exit() raises SystemExit (BaseException, not Exception), so the except
        # clause above doesn't catch it, but finally still runs.
        if CONFIG.get('shutdown_after_callhome'):
            logger.critical("=" * 60)
            logger.critical("INITIATING CLEAN SHUTDOWN — battery critically low")
            logger.critical("SD card protection: filesystem will be cleanly unmounted")
            logger.critical("=" * 60)
            subprocess.run(['shutdown', '-h', 'now'], check=False)
