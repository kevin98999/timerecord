import json
import calendar
import sqlite3
import shutil
import os
import re
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path
from tkinter import BOTH, END, LEFT, RIGHT, TOP, Button, Entry, Frame, Label, LabelFrame, Listbox, Radiobutton, StringVar, Tk, Toplevel, messagebox
from tkinter import filedialog, ttk
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape

import cv2
import numpy as np
from PIL import Image, ImageDraw, ImageFont, ImageOps, ImageTk


def app_base_dir():
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


APP_DIR = app_base_dir()
DATA_DIR = APP_DIR / "data"
FACE_DIR = DATA_DIR / "faces"
TEACHER_ATTENDANCE_PHOTO_DIR = DATA_DIR / "teacher_attendance_photos"
CHILDREN_DIR = APP_DIR / "children"
QR_DIR = DATA_DIR / "child_qrcodes"
CARD_DIR = DATA_DIR / "child_cards"
DAILY_EXPORT_DIR = DATA_DIR / "daily_exports"
FORM_DIR = DATA_DIR / "form"
DB_PATH = DATA_DIR / "attendance.db"
SETTINGS_PATH = DATA_DIR / "settings.json"
WEBAPP_HOST = "0.0.0.0"
WEBAPP_PORT = 8000
WEBAPP_PROCESS = None
WEBAPP_LOG_HANDLES = []
WEBAPP_URL_SETTING = "webapp_url"
WEBAPP_URL_ENV = "TIMERECORD_WEBAPP_URL"
DESKTOP_SYNC_TOKEN_SETTING = "desktop_sync_token"
DESKTOP_SYNC_TOKEN_ENV = "TIMERECORD_DESKTOP_SYNC_TOKEN"
FACE_SIZE = (128, 128)
MATCH_THRESHOLD = 55.0
FACE_DETECT_SCALE_FACTOR = 1.08
FACE_DETECT_MIN_NEIGHBORS = 3
FACE_DETECT_MIN_SIZE = (45, 45)
AUTO_SCAN_INTERVAL_SECONDS = 1.0
REMOTE_ATTENDANCE_PULL_INTERVAL_MS = 10000
AUTO_RECORD_COOLDOWN_SECONDS = 20.0
CHILD_RECORD_COOLDOWN_SECONDS = 20 * 60
TEACHER_RECORD_COOLDOWN_SECONDS = 30 * 60
DAILY_CLOSEOUT_TIME = "23:50"
TEACHER_FACE_SAMPLE_COUNT = 10
POSITION_GUIDANCE_COOLDOWN_SECONDS = 8.0
POSITION_CENTER_TOLERANCE = 0.12
FACE_MIN_SIZE_RATIO = 0.18
FACE_MAX_SIZE_RATIO = 0.52
QR_MIN_SIZE_RATIO = 0.16
QR_MAX_SIZE_RATIO = 0.58
ROLE_LABELS = {
    "children": "Child",
    "teachers": "Teacher",
}

ROLE_VALUES = {
    "Child": "children",
    "Teacher": "teachers",
}


def local_ipv4_addresses():
    addresses = set()
    try:
        hostname = socket.gethostname()
        for info in socket.getaddrinfo(hostname, None, socket.AF_INET):
            address = info[4][0]
            if not address.startswith(("127.", "169.254.")):
                addresses.add(address)
    except OSError:
        pass

    try:
        probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            probe.connect(("8.8.8.8", 80))
            address = probe.getsockname()[0]
            if not address.startswith(("127.", "169.254.")):
                addresses.add(address)
        finally:
            probe.close()
    except OSError:
        pass
    return sorted(addresses)


def webapp_access_urls():
    remote_url = configured_webapp_url()
    if remote_url:
        return [remote_url]
    hosts = ["127.0.0.1"] + local_ipv4_addresses()
    return [f"http://{host}:{WEBAPP_PORT}" for host in hosts]

EVENT_LABELS = {
    "checkin": "Check In",
    "checkout": "Check Out",
}
OPERATION_LABELS = {
    "self": "Self",
    "system": "System",
}


def attendance_source_label(source):
    return OPERATION_LABELS["self"] if source == "desktop" else OPERATION_LABELS["system"]


def attendance_operator_name(name, source, operator_name=""):
    operator_name = (operator_name or "").strip()
    if operator_name:
        return operator_name
    return name if source == "desktop" else OPERATION_LABELS["system"]

ATTENDANCE_PROMPT_VOICE = "Voice greeting"
ATTENDANCE_PROMPT_BELL = "System bell only"
ATTENDANCE_PROMPT_VALUES = {ATTENDANCE_PROMPT_VOICE, ATTENDANCE_PROMPT_BELL}

CLASS_NAMES = ("1ç­", "2ç­", "3ç­", "4ç­")


def now_text():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def normalize_remote_attendance_timestamp(value):
    event_time = datetime.strptime(value, "%Y-%m-%d %H:%M:%S")
    now_local = datetime.now()
    if event_time > now_local + timedelta(minutes=5):
        local_from_utc = event_time.replace(tzinfo=timezone.utc).astimezone().replace(tzinfo=None)
        if local_from_utc <= now_local + timedelta(minutes=5):
            return local_from_utc.strftime("%Y-%m-%d %H:%M:%S")
    return event_time.strftime("%Y-%m-%d %H:%M:%S")


def ensure_dirs():
    DATA_DIR.mkdir(exist_ok=True)
    FACE_DIR.mkdir(exist_ok=True)
    TEACHER_ATTENDANCE_PHOTO_DIR.mkdir(exist_ok=True)
    CHILDREN_DIR.mkdir(exist_ok=True)
    QR_DIR.mkdir(exist_ok=True)
    CARD_DIR.mkdir(exist_ok=True)
    DAILY_EXPORT_DIR.mkdir(exist_ok=True)
    FORM_DIR.mkdir(exist_ok=True)


def load_settings():
    try:
        with SETTINGS_PATH.open("r", encoding="utf-8") as file:
            settings = json.load(file)
    except (OSError, json.JSONDecodeError):
        return {}
    return settings if isinstance(settings, dict) else {}


def save_settings(settings):
    ensure_dirs()
    try:
        with SETTINGS_PATH.open("w", encoding="utf-8") as file:
            json.dump(settings, file, indent=2, ensure_ascii=False)
    except OSError:
        pass


def normalize_webapp_url(value):
    if not isinstance(value, str):
        return ""
    value = value.strip()
    if not value:
        return ""
    if not re.match(r"^https?://", value, re.IGNORECASE):
        value = "https://" + value
    return value.rstrip("/")


def configured_webapp_url():
    env_value = normalize_webapp_url(os.environ.get(WEBAPP_URL_ENV))
    if env_value:
        return env_value
    return normalize_webapp_url(load_settings().get(WEBAPP_URL_SETTING))


def configured_desktop_sync_token():
    env_value = os.environ.get(DESKTOP_SYNC_TOKEN_ENV, "").strip()
    if env_value:
        return env_value
    value = load_settings().get(DESKTOP_SYNC_TOKEN_SETTING, "")
    return value.strip() if isinstance(value, str) else ""


def check_remote_webapp(url, timeout=5):
    if not url:
        return False, "missing URL"
    request = urllib.request.Request(url, headers={"User-Agent": "TimeRecordDesktop/1.0"})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = getattr(response, "status", 0)
            if 200 <= status < 500:
                return True, f"HTTP {status}"
            return False, f"HTTP {status}"
    except urllib.error.HTTPError as exc:
        if 200 <= exc.code < 500:
            return True, f"HTTP {exc.code}"
        return False, f"HTTP {exc.code}"
    except (OSError, urllib.error.URLError) as exc:
        return False, str(exc)


def post_remote_attendance(payload, timeout=8):
    remote_url = configured_webapp_url()
    token = configured_desktop_sync_token()
    if not remote_url or not token:
        return False, "remote sync is not configured"
    endpoint = f"{remote_url}/api/desktop/attendance"
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    request = urllib.request.Request(
        endpoint,
        data=body,
        method="POST",
        headers={
            "Content-Type": "application/json; charset=utf-8",
            "X-TimeRecord-Token": token,
            "User-Agent": "TimeRecordDesktop/1.0",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = getattr(response, "status", 0)
            return 200 <= status < 300, f"HTTP {status}"
    except urllib.error.HTTPError as exc:
        return False, f"HTTP {exc.code}"
    except (OSError, urllib.error.URLError) as exc:
        return False, str(exc)


def fetch_remote_attendance(date_text=None, timeout=8):
    remote_url = configured_webapp_url()
    token = configured_desktop_sync_token()
    if not remote_url or not token:
        return False, "remote sync is not configured", []
    params = {"date": date_text or datetime.now().strftime("%Y-%m-%d"), "limit": "1000"}
    endpoint = f"{remote_url}/api/desktop/attendance?{urllib.parse.urlencode(params)}"
    request = urllib.request.Request(
        endpoint,
        method="GET",
        headers={
            "X-TimeRecord-Token": token,
            "User-Agent": "TimeRecordDesktop/1.0",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = getattr(response, "status", 0)
            data = json.loads(response.read().decode("utf-8"))
            if 200 <= status < 300 and data.get("ok"):
                records = data.get("records", [])
                return True, f"HTTP {status}", records if isinstance(records, list) else []
            return False, data.get("error", f"HTTP {status}"), []
    except urllib.error.HTTPError as exc:
        try:
            data = json.loads(exc.read().decode("utf-8"))
            return False, data.get("error", f"HTTP {exc.code}"), []
        except (OSError, json.JSONDecodeError):
            return False, f"HTTP {exc.code}", []
    except (OSError, urllib.error.URLError, json.JSONDecodeError) as exc:
        return False, str(exc), []


def log_desktop_sync(message):
    ensure_dirs()
    try:
        with (DATA_DIR / "desktop_sync.log").open("a", encoding="utf-8") as file:
            file.write(f"[{now_text()}] {message}\n")
    except OSError:
        pass


def load_attendance_prompt_setting():
    value = load_settings().get("attendance_prompt")
    if value in ATTENDANCE_PROMPT_VALUES:
        return value
    return ATTENDANCE_PROMPT_VOICE


def save_attendance_prompt_setting(value):
    if value not in ATTENDANCE_PROMPT_VALUES:
        return
    settings = load_settings()
    settings["attendance_prompt"] = value
    save_settings(settings)


def load_closed_dates_setting():
    values = load_settings().get("closed_dates", [])
    if not isinstance(values, list):
        return []

    closed_dates = []
    for value in values:
        if not isinstance(value, str):
            continue
        try:
            datetime.strptime(value, "%Y-%m-%d")
        except ValueError:
            continue
        closed_dates.append(value)
    return sorted(set(closed_dates))


def save_closed_dates_setting(closed_dates):
    valid_dates = []
    for value in closed_dates:
        try:
            valid_dates.append(datetime.strptime(str(value), "%Y-%m-%d").strftime("%Y-%m-%d"))
        except ValueError:
            continue
    settings = load_settings()
    settings["closed_dates"] = sorted(set(valid_dates))
    save_settings(settings)


def init_db():
    ensure_dirs()
    with connect_db() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS persons (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                role TEXT NOT NULL CHECK(role IN ('children', 'teachers')),
                class_name TEXT,
                photo_path TEXT NOT NULL,
                qr_token TEXT,
                created_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS attendance (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                person_id INTEGER NOT NULL,
                name TEXT NOT NULL,
                role TEXT NOT NULL,
                event_type TEXT NOT NULL CHECK(event_type IN ('checkin', 'checkout')),
                timestamp TEXT NOT NULL,
                snapshot_path TEXT,
                source TEXT NOT NULL DEFAULT 'system',
                operator_name TEXT,
                FOREIGN KEY(person_id) REFERENCES persons(id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS teacher_face_samples (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                person_id INTEGER NOT NULL,
                photo_path TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(person_id) REFERENCES persons(id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS class_names (
                name TEXT PRIMARY KEY,
                created_at TEXT NOT NULL
            )
            """
        )
        columns = {row[1] for row in conn.execute("PRAGMA table_info(persons)").fetchall()}
        if "qr_token" not in columns:
            conn.execute("ALTER TABLE persons ADD COLUMN qr_token TEXT")
        if "class_name" not in columns:
            conn.execute("ALTER TABLE persons ADD COLUMN class_name TEXT")
        attendance_columns = {row[1] for row in conn.execute("PRAGMA table_info(attendance)").fetchall()}
        if "snapshot_path" not in attendance_columns:
            conn.execute("ALTER TABLE attendance ADD COLUMN snapshot_path TEXT")
        if "source" not in attendance_columns:
            conn.execute("ALTER TABLE attendance ADD COLUMN source TEXT NOT NULL DEFAULT 'system'")
        if "operator_name" not in attendance_columns:
            conn.execute("ALTER TABLE attendance ADD COLUMN operator_name TEXT")
        class_count = conn.execute("SELECT COUNT(*) FROM class_names").fetchone()[0]
        if class_count == 0:
            conn.executemany(
                "INSERT INTO class_names(name, created_at) VALUES (?, ?)",
                [(name, now_text()) for name in CLASS_NAMES],
            )


def connect_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute("PRAGMA journal_mode=MEMORY")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn




def start_webapp():
    global WEBAPP_PROCESS, WEBAPP_LOG_HANDLES
    if configured_webapp_url():
        return True

    if WEBAPP_PROCESS is not None and WEBAPP_PROCESS.poll() is None:
        return True

    script_path = APP_DIR / "webapp.py"
    if not script_path.exists():
        return False

    ensure_dirs()
    stdout_log = (DATA_DIR / "webapp.log").open("a", encoding="utf-8")
    stderr_log = (DATA_DIR / "webapp.err.log").open("a", encoding="utf-8")
    WEBAPP_LOG_HANDLES = [stdout_log, stderr_log]
    stdout_log.write(f"\n[{now_text()}] Starting webapp.py on http://{WEBAPP_HOST}:{WEBAPP_PORT}\n")
    stdout_log.flush()

    creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    try:
        WEBAPP_PROCESS = subprocess.Popen(
            [
                sys.executable,
                str(script_path),
                "--host",
                WEBAPP_HOST,
                "--port",
                str(WEBAPP_PORT),
            ],
            cwd=str(APP_DIR),
            stdout=stdout_log,
            stderr=stderr_log,
            creationflags=creationflags,
        )
    except OSError as exc:
        stderr_log.write(f"[{now_text()}] Failed to start webapp.py: {exc}\n")
        stderr_log.flush()
        stop_webapp()
        return False
    return True


def webapp_status_message(webapp_started):
    remote_url = configured_webapp_url()
    if remote_url:
        connected, detail = check_remote_webapp(remote_url)
        sync_text = "attendance sync enabled" if configured_desktop_sync_token() else "attendance sync token missing"
        if connected:
            return f"System started; external web app connected: {remote_url}; {sync_text}"
        return f"System started; external web app not reachable: {remote_url} ({detail}); {sync_text}"

    if webapp_started:
        return "System started; web app: " + " | ".join(webapp_access_urls())
    return "System started; web app did not start"


def stop_webapp():
    global WEBAPP_PROCESS, WEBAPP_LOG_HANDLES
    process = WEBAPP_PROCESS
    WEBAPP_PROCESS = None
    if process is not None and process.poll() is None:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=5)

    for handle in WEBAPP_LOG_HANDLES:
        try:
            handle.close()
        except OSError:
            pass
    WEBAPP_LOG_HANDLES = []

def load_class_names():
    with connect_db() as conn:
        rows = conn.execute("SELECT name FROM class_names ORDER BY rowid").fetchall()
    return [row[0] for row in rows]


def speak(text):
    def worker():
        try:
            escaped = text.replace("'", "''")
            command = (
                "Add-Type -AssemblyName System.Speech; "
                "$s = New-Object System.Speech.Synthesis.SpeechSynthesizer; "
                "$s.Volume = 90; "
                "$s.Rate = -2; "
                "try { $s.SelectVoiceByHints([System.Speech.Synthesis.VoiceGender]::Female, [System.Speech.Synthesis.VoiceAge]::Adult) } catch { }; "
                f"$s.Speak('{escaped}')"
            )
            subprocess.run(
                ["powershell", "-NoProfile", "-Command", command],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=8,
                check=False,
            )
        except Exception:
            try:
                import winsound

                winsound.MessageBeep()
            except Exception:
                pass

    threading.Thread(target=worker, daemon=True).start()


def play_system_bell():
    def worker():
        try:
            import winsound

            winsound.Beep(1400, 180)
            winsound.Beep(1800, 220)
        except Exception:
            try:
                import winsound

                winsound.MessageBeep()
            except Exception:
                pass

    threading.Thread(target=worker, daemon=True).start()


def attendance_voice_prompt(person, event_type):
    name = person["name"]
    if event_type == "checkout":
        return f"THANK YOU {name}, SEE YOU NEXT TIME."
    if person["role"] == "children":
        return f"HELLO {name}, WELCOME TO DAYCARE, HAVE A NICE DAY."
    return f"HELLO {name}, WELCOME TO WORK, HAVE A NICE DAY."


def position_guidance_prompt(rect, frame_shape, min_size_ratio, max_size_ratio):
    if rect is None or frame_shape is None:
        return None
    frame_h, frame_w = frame_shape[:2]
    if frame_w <= 0 or frame_h <= 0:
        return None
    x, y, w, h = rect
    if w <= 0 or h <= 0:
        return None

    size_ratio = max(w / frame_w, h / frame_h)
    center_x = x + (w / 2)
    center_y = y + (h / 2)
    x_offset = (center_x - (frame_w / 2)) / frame_w
    y_offset = (center_y - (frame_h / 2)) / frame_h

    prompts = []
    if size_ratio < min_size_ratio:
        prompts.append("move closer")
    elif size_ratio > max_size_ratio:
        prompts.append("move farther away")

    if x_offset < -POSITION_CENTER_TOLERANCE:
        prompts.append("move right")
    elif x_offset > POSITION_CENTER_TOLERANCE:
        prompts.append("move left")

    if y_offset < -POSITION_CENTER_TOLERANCE:
        prompts.append("move down")
    elif y_offset > POSITION_CENTER_TOLERANCE:
        prompts.append("move up")

    if not prompts:
        return None
    if len(prompts) == 1:
        return prompts[0].capitalize() + "."
    return (prompts[0] + " and " + prompts[1]).capitalize() + "."


def qr_points_rect(qr_points, frame_width):
    if qr_points is None or len(qr_points) == 0 or frame_width <= 0:
        return None
    try:
        points = qr_points[0].astype(float)
        flipped_points = np.array([[frame_width - x, y] for x, y in points], dtype=np.float32)
        x, y, w, h = cv2.boundingRect(flipped_points.astype(np.int32))
    except (cv2.error, ValueError, TypeError, IndexError):
        return None
    if w <= 0 or h <= 0:
        return None
    return x, y, w, h


def detect_face(gray, cascade):
    if gray is None or gray.size == 0:
        return None
    try:
        faces = cascade.detectMultiScale(
            gray,
            scaleFactor=FACE_DETECT_SCALE_FACTOR,
            minNeighbors=FACE_DETECT_MIN_NEIGHBORS,
            minSize=FACE_DETECT_MIN_SIZE,
        )
    except cv2.error:
        return None
    if len(faces) == 0:
        return None
    x, y, w, h = sorted(faces, key=lambda item: item[2] * item[3], reverse=True)[0]
    return x, y, w, h


def normalize_face(gray, face_rect):
    if gray is None or face_rect is None or gray.size == 0:
        return None
    x, y, w, h = face_rect
    if w <= 0 or h <= 0:
        return None
    margin_x = int(w * 0.12)
    margin_y = int(h * 0.12)
    x1 = max(0, x - margin_x)
    y1 = max(0, y - margin_y)
    x2 = min(gray.shape[1], x + w + margin_x)
    y2 = min(gray.shape[0], y + h + margin_y)
    if x2 <= x1 or y2 <= y1:
        return None
    face = gray[y1:y2, x1:x2]
    if face.size == 0:
        return None
    try:
        face = cv2.resize(face, FACE_SIZE)
        face = cv2.equalizeHist(face)
    except cv2.error:
        return None
    return face


def read_gray_image(path_value):
    if not path_value:
        return None
    try:
        path = Path(path_value)
        if not path.exists():
            return None
        data = np.fromfile(str(path), dtype=np.uint8)
        if data.size == 0:
            return None
        return cv2.imdecode(data, cv2.IMREAD_GRAYSCALE)
    except (OSError, ValueError, cv2.error):
        return None


def load_known_faces():
    rows = []
    with connect_db() as conn:
        for row in conn.execute("SELECT id, name, role, photo_path FROM persons WHERE role IN ('teachers', 'children') ORDER BY id"):
            person_id, name, role, photo_path = row
            sample_paths = [photo_path]
            if role == "teachers":
                sample_paths.extend(
                    sample_row[0]
                    for sample_row in conn.execute(
                        "SELECT photo_path FROM teacher_face_samples WHERE person_id = ? ORDER BY id",
                        (person_id,),
                    )
                )
            for sample_path in dict.fromkeys(path for path in sample_paths if path):
                image = read_gray_image(sample_path)
                if image is None:
                    continue
                try:
                    image = cv2.resize(image, FACE_SIZE)
                    image = cv2.equalizeHist(image)
                except cv2.error:
                    continue
                rows.append(
                    {
                        "id": person_id,
                        "name": name,
                        "role": role,
                        "face": image.astype(np.float32),
                    }
                )
    return rows


def find_match(face, known_faces):
    if not known_faces:
        return None, None
    current = face.astype(np.float32)
    scores = []
    for person in known_faces:
        score = float(np.mean(np.abs(current - person["face"])))
        scores.append((score, person))
    score, person = min(scores, key=lambda item: item[0])
    if score <= MATCH_THRESHOLD:
        return person, score
    return None, score


def safe_filename(name):
    invalid_chars = '<>:"/\\|?*'
    cleaned = "".join("_" if char in invalid_chars else char for char in name).strip()
    return cleaned or "child"


def child_token(name):
    return f"CHILD:{name}"


def is_valid_child_qr_data(qr_data):
    return isinstance(qr_data, str) and qr_data.startswith("CHILD:") and len(qr_data) > len("CHILD:")


def create_qr_image(token, size=360):
    encoder = cv2.QRCodeEncoder_create()
    qr = encoder.encode(token)
    qr = cv2.copyMakeBorder(qr, 4, 4, 4, 4, cv2.BORDER_CONSTANT, value=255)
    qr = cv2.resize(qr, (size, size), interpolation=cv2.INTER_NEAREST)
    return Image.fromarray(qr).convert("RGB")


def create_card_qr_image(token, size=190):
    encoder = cv2.QRCodeEncoder_create()
    qr = encoder.encode(token)
    qr = cv2.resize(qr, (size, size), interpolation=cv2.INTER_NEAREST)
    return Image.fromarray(qr).convert("RGB")


def get_font(size, bold=False):
    font_names = ["msyhbd.ttc", "msyh.ttc", "simhei.ttf", "arial.ttf"] if bold else ["msyh.ttc", "simhei.ttf", "arial.ttf"]
    for font_name in font_names:
        font_path = Path("C:/Windows/Fonts") / font_name
        if font_path.exists():
            return ImageFont.truetype(str(font_path), size)
    return ImageFont.load_default()


def fit_image(image, size):
    return ImageOps.fit(image.convert("RGB"), size, method=Image.Resampling.LANCZOS, centering=(0.5, 0.35))


def read_xlsx_rows(path):
    ns = {
        "main": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
        "rel": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
        "pkgrel": "http://schemas.openxmlformats.org/package/2006/relationships",
    }
    with zipfile.ZipFile(path) as archive:
        shared_strings = []
        if "xl/sharedStrings.xml" in archive.namelist():
            shared_root = ET.fromstring(archive.read("xl/sharedStrings.xml"))
            for item in shared_root.findall("main:si", ns):
                text_parts = [node.text or "" for node in item.findall(".//main:t", ns)]
                shared_strings.append("".join(text_parts))

        sheet_path = "xl/worksheets/sheet1.xml"
        if "xl/workbook.xml" in archive.namelist() and "xl/_rels/workbook.xml.rels" in archive.namelist():
            workbook_root = ET.fromstring(archive.read("xl/workbook.xml"))
            first_sheet = workbook_root.find("main:sheets/main:sheet", ns)
            if first_sheet is not None:
                rel_id = first_sheet.attrib.get(f"{{{ns['rel']}}}id")
                rel_root = ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))
                for rel in rel_root.findall("pkgrel:Relationship", ns):
                    if rel.attrib.get("Id") == rel_id:
                        target = rel.attrib.get("Target", "worksheets/sheet1.xml")
                        sheet_path = "xl/" + target.lstrip("/")
                        break

        sheet_root = ET.fromstring(archive.read(sheet_path))
        rows = []
        for row_node in sheet_root.findall(".//main:sheetData/main:row", ns):
            row_values = []
            for cell in row_node.findall("main:c", ns):
                cell_ref = cell.attrib.get("r", "")
                match = re.match(r"([A-Z]+)", cell_ref)
                if match:
                    col_index = 0
                    for char in match.group(1):
                        col_index = col_index * 26 + (ord(char) - ord("A") + 1)
                    while len(row_values) < col_index - 1:
                        row_values.append("")

                cell_type = cell.attrib.get("t")
                if cell_type == "inlineStr":
                    value = "".join(node.text or "" for node in cell.findall(".//main:t", ns))
                else:
                    value_node = cell.find("main:v", ns)
                    value = value_node.text if value_node is not None and value_node.text is not None else ""
                    if cell_type == "s" and value:
                        try:
                            value = shared_strings[int(value)]
                        except (ValueError, IndexError):
                            value = ""
                row_values.append(str(value).strip())
            rows.append(row_values)
    return rows


def is_class_name_token(token):
    text = str(token or "").strip()
    if not text:
        return False
    compact = re.sub(r"\s+", "", text)
    return re.search(r"[\w\u4e00-\u9fff]+ç­", compact) is not None or re.fullmatch(r"(?:Class|class)?\d+", text) is not None


def normalize_class_name(value):
    text = str(value or "").strip()
    if not text:
        return ""
    if text.endswith(".0"):
        text = text[:-2]
    class_match = re.search(r"([\w\u4e00-\u9fff]+)ç­", re.sub(r"\s+", "", text))
    if class_match:
        return f"{class_match.group(1)}ç­"
    number_match = re.fullmatch(r"(?:Class|class)?(\d+)", text)
    if number_match:
        return f"{number_match.group(1)}ç­"
    return re.sub(r"\s+", " ", text)


def is_child_name_token(token):
    if not token:
        return False
    if is_class_name_token(token):
        return False
    normalized = token.strip()
    normalized_header = re.sub(r"[\s_-]+", "", normalized).casefold()
    if normalized_header in {
        "å§“å",
        "åå­—",
        "å„¿ç«¥",
        "å­©å­",
        "å¹¼å„¿",
        "ç­çº§",
        "ç­åˆ«",
        "name",
        "firstname",
        "lastname",
        "class",
        "classes",
        "group",
    }:
        return False
    return re.search(r"[\w\u4e00-\u9fff]", normalized) is not None


def parse_children_from_text(text):
    children = []
    seen_names = set()
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        tokens = [token.strip() for token in re.split(r"[\s,ï¼Œ;ï¼›|:ï¼š]+", line) if token.strip()]
        for index, token in enumerate(tokens):
            if not is_class_name_token(token):
                continue
            class_name = token
            candidates = []
            if index + 1 < len(tokens):
                candidates.append(tokens[index + 1])
            if index > 0:
                candidates.append(tokens[index - 1])
            for candidate in candidates:
                if is_child_name_token(candidate) and candidate not in seen_names:
                    children.append((candidate, class_name))
                    seen_names.add(candidate)
                    break

        compact_line = re.sub(r"\s+", "", line)
        for class_name, name in re.findall(r"([\w\u4e00-\u9fff]+ç­)([\w\u4e00-\u9fff]{2,20})", compact_line):
            if is_child_name_token(name) and name not in seen_names:
                children.append((name, class_name))
                seen_names.add(name)
        for name, class_name in re.findall(r"([\w\u4e00-\u9fff]{2,20})([\w\u4e00-\u9fff]+ç­)", compact_line):
            if is_child_name_token(name) and name not in seen_names:
                children.append((name, class_name))
                seen_names.add(name)
    return children


def parse_children_from_xlsx_rows(rows):
    children = []
    seen_names = set()
    for row in rows:
        name = xlsx_child_name(row)
        class_name = normalize_class_name(row[4]) if len(row) > 4 else ""
        if is_child_name_token(name) and class_name and name not in seen_names:
            children.append((name, class_name))
            seen_names.add(name)
    return children


def xlsx_child_name(row):
    first_name = row[0].strip() if len(row) > 0 else ""
    last_name = row[1].strip() if len(row) > 1 else ""
    return " ".join(part for part in (first_name, last_name) if part)


def xlsx_import_preview(rows, limit=8):
    preview_rows = []
    for row in rows:
        name = xlsx_child_name(row)
        class_name = row[4].strip() if len(row) > 4 else ""
        if name or class_name:
            preview_rows.append(f"A+B={name or '(empty)'} / E={class_name or '(empty)'}")
        if len(preview_rows) >= limit:
            break
    return "\n".join(preview_rows)


def save_child_placeholder_photo(name, class_name):
    safe_name = safe_filename(name)
    photo_path = CHILDREN_DIR / f"{safe_name}_placeholder.png"
    image = Image.new("RGB", (360, 360), (242, 251, 245))
    draw = ImageDraw.Draw(image)

    draw.ellipse((54, 34, 306, 286), fill=(232, 245, 239), outline=(205, 224, 246), width=6)
    draw.ellipse((136, 76, 224, 164), fill=(244, 181, 176), outline=(218, 142, 142), width=3)
    draw.pieslice((112, 50, 248, 170), 180, 360, fill=(101, 122, 145))
    draw.ellipse((116, 98, 146, 130), fill=(244, 181, 176))
    draw.ellipse((214, 98, 244, 130), fill=(244, 181, 176))
    draw.ellipse((156, 112, 166, 122), fill=(45, 57, 75))
    draw.ellipse((194, 112, 204, 122), fill=(45, 57, 75))
    draw.arc((164, 122, 196, 146), 20, 160, fill=(133, 66, 66), width=3)
    draw.rounded_rectangle((104, 186, 256, 278), radius=42, fill=(205, 224, 246), outline=(156, 176, 196), width=3)

    initial = name[:1].upper()
    initial_font = get_font(66, bold=True)
    initial_box = draw.textbbox((0, 0), initial, font=initial_font)
    draw.text(
        ((360 - (initial_box[2] - initial_box[0])) / 2, 202),
        initial,
        fill=(45, 57, 75),
        font=initial_font,
    )
    class_font = get_font(34)
    class_box = draw.textbbox((0, 0), class_name, font=class_font)
    draw.text(
        ((360 - (class_box[2] - class_box[0])) / 2, 304),
        class_name,
        fill=(58, 74, 92),
        font=class_font,
    )
    image.save(photo_path)
    return photo_path


def save_child_card(name, photo_path, token, class_name=""):
    safe_name = safe_filename(name)
    qr_image = create_card_qr_image(token, size=354)
    qr_path = QR_DIR / f"{safe_name}.png"
    card_path = CARD_DIR / f"{safe_name}_card.png"
    qr_image.save(qr_path)

    card = Image.new("RGB", (407, 534), "white")
    draw = ImageDraw.Draw(card)

    name_font = get_font(42)
    for size in range(42, 22, -1):
        name_font = get_font(size)
        text_box = draw.textbbox((0, 0), name, font=name_font)
        if text_box[2] - text_box[0] <= 360:
            break
    name_x = 24
    name_y = 0
    draw.text((name_x, name_y), name, fill=(0, 0, 0), font=name_font)
    name_box = draw.textbbox((name_x, name_y), name, font=name_font)

    qr_y = 104
    if class_name:
        class_font = get_font(34)
        for size in range(34, 18, -1):
            class_font = get_font(size)
            text_box = draw.textbbox((0, 0), class_name, font=class_font)
            if text_box[2] - text_box[0] <= 360:
                break
        class_probe_box = draw.textbbox((0, 0), class_name, font=class_font)
        class_y = name_box[3] - class_probe_box[1]
        draw.text((name_x, class_y), class_name, fill=(0, 0, 0), font=class_font)
        class_box = draw.textbbox((name_x, class_y), class_name, font=class_font)
        qr_y = max(qr_y, class_box[3] + 2)

    card.paste(qr_image, (21, qr_y))
    card.save(card_path)
    return qr_path, card_path


def save_teacher_attendance_snapshot(person, event_type, frame):
    if frame is None or person.get("role") != "teachers":
        return ""
    safe_name = safe_filename(person["name"])
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    path = TEACHER_ATTENDANCE_PHOTO_DIR / f"{timestamp}_{safe_name}_{event_type}.jpg"
    try:
        cv2.imwrite(str(path), frame)
    except cv2.error:
        return ""
    return str(path)


def sync_children_from_directory():
    image_exts = {".jpg", ".jpeg", ".png", ".bmp"}
    files = sorted(path for path in CHILDREN_DIR.iterdir() if path.is_file() and path.suffix.lower() in image_exts)
    created_or_updated = 0
    generated_cards = 0

    with connect_db() as conn:
        for photo_path in files:
            name = photo_path.stem.strip()
            if not name:
                continue
            token = child_token(name)
            row = conn.execute(
                "SELECT id FROM persons WHERE role = 'children' AND name = ?",
                (name,),
            ).fetchone()
            if row:
                conn.execute(
                    "UPDATE persons SET photo_path = ?, qr_token = ? WHERE id = ?",
                    (str(photo_path), token, row[0]),
                )
            else:
                conn.execute(
                    "INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at) VALUES (?, 'children', '', ?, ?, ?)",
                    (name, str(photo_path), token, now_text()),
                )
            save_child_card(name, photo_path, token)
            created_or_updated += 1
            generated_cards += 1

    return created_or_updated, generated_cards


def xlsx_col_name(index):
    name = ""
    while index:
        index, rem = divmod(index - 1, 26)
        name = chr(65 + rem) + name
    return name


def worksheet_xml(headers, rows):
    sheet_rows = [headers] + rows
    sheet_xml_rows = []
    for row_index, row in enumerate(sheet_rows, start=1):
        cells = []
        for col_index, value in enumerate(row, start=1):
            cell_ref = f"{xlsx_col_name(col_index)}{row_index}"
            value_text = escape(str(value))
            cells.append(f'<c r="{cell_ref}" t="inlineStr"><is><t>{value_text}</t></is></c>')
        sheet_xml_rows.append(f'<row r="{row_index}">{"".join(cells)}</row>')

    return (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
        "<sheetData>"
        + "".join(sheet_xml_rows)
        + "</sheetData></worksheet>"
    )


def write_xlsx_workbook(path, sheets):
    sheet_defs = []
    content_overrides = []
    workbook_relationships = []
    for index, sheet in enumerate(sheets, start=1):
        sheet_name = escape(sheet["name"])
        sheet_defs.append(f'<sheet name="{sheet_name}" sheetId="{index}" r:id="rId{index}"/>')
        content_overrides.append(
            f'<Override PartName="/xl/worksheets/sheet{index}.xml" '
            'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
        )
        workbook_relationships.append(
            f'<Relationship Id="rId{index}" '
            'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" '
            f'Target="worksheets/sheet{index}.xml"/>'
        )

    workbook = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        "<sheets>"
        + "".join(sheet_defs)
        + "</sheets></workbook>"
    )
    content_types = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/xl/workbook.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
        + "".join(content_overrides)
        + "</Types>"
    )
    root_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" '
        'Target="xl/workbook.xml"/></Relationships>'
    )
    workbook_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        + "".join(workbook_relationships)
        + "</Relationships>"
    )

    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("[Content_Types].xml", content_types)
        archive.writestr("_rels/.rels", root_rels)
        archive.writestr("xl/workbook.xml", workbook)
        archive.writestr("xl/_rels/workbook.xml.rels", workbook_rels)
        for index, sheet in enumerate(sheets, start=1):
            archive.writestr(
                f"xl/worksheets/sheet{index}.xml",
                worksheet_xml(sheet["headers"], sheet["rows"]),
            )


def write_xlsx(path, headers, rows):
    write_xlsx_workbook(path, [{"name": "Attendance Records", "headers": headers, "rows": rows}])


def write_legacy_xlsx(path, headers, rows):
    def col_name(index):
        name = ""
        while index:
            index, rem = divmod(index - 1, 26)
            name = chr(65 + rem) + name
        return name

    sheet_rows = [headers] + rows
    sheet_xml_rows = []
    for row_index, row in enumerate(sheet_rows, start=1):
        cells = []
        for col_index, value in enumerate(row, start=1):
            cell_ref = f"{col_name(col_index)}{row_index}"
            value_text = escape(str(value))
            cells.append(f'<c r="{cell_ref}" t="inlineStr"><is><t>{value_text}</t></is></c>')
        sheet_xml_rows.append(f'<row r="{row_index}">{"".join(cells)}</row>')

    worksheet = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
        "<sheetData>"
        + "".join(sheet_xml_rows)
        + "</sheetData></worksheet>"
    )
    workbook = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        '<sheets><sheet name="Attendance Records" sheetId="1" r:id="rId1"/></sheets></workbook>'
    )
    content_types = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/xl/workbook.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
        '<Override PartName="/xl/worksheets/sheet1.xml" '
        'ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
        "</Types>"
    )
    root_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" '
        'Target="xl/workbook.xml"/></Relationships>'
    )
    workbook_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" '
        'Target="worksheets/sheet1.xml"/></Relationships>'
    )

    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("[Content_Types].xml", content_types)
        archive.writestr("_rels/.rels", root_rels)
        archive.writestr("xl/workbook.xml", workbook)
        archive.writestr("xl/_rels/workbook.xml.rels", workbook_rels)
        archive.writestr("xl/worksheets/sheet1.xml", worksheet)


def ceil_to_interval(dt, minutes):
    discard = timedelta(
        minutes=dt.minute % minutes,
        seconds=dt.second,
        microseconds=dt.microsecond,
    )
    rounded = dt - discard
    if discard:
        rounded += timedelta(minutes=minutes)
    return rounded


def build_presence_summary_rows(rows):
    child_events = []
    for person_id, name, role, class_name, timestamp, event_type, *extra in rows:
        if role != "children":
            continue
        try:
            event_time = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S")
        except (TypeError, ValueError):
            continue
        try:
            event_id = int(extra[-1]) if extra else 0
        except (TypeError, ValueError):
            event_id = 0
        child_events.append(
            {
                "person_id": person_id,
                "name": name,
                "class_name": class_name or "Unassigned",
                "time": event_time,
                "event_type": event_type,
                "id": event_id,
            }
        )

    if not child_events:
        return []

    summary_rows = []
    dates = sorted({event["time"].date() for event in child_events})
    events_by_date = {
        date: sorted(
            (event for event in child_events if event["time"].date() == date),
            key=lambda event: (event["time"], event["id"]),
        )
        for date in dates
    }

    for date in dates:
        day_events = events_by_date[date]
        start_time = datetime.combine(date, datetime.min.time()).replace(hour=6)
        end_time = max(start_time, ceil_to_interval(day_events[-1]["time"], 15))
        current_children = {}
        event_index = 0
        slot_time = start_time

        while slot_time <= end_time:
            while event_index < len(day_events) and day_events[event_index]["time"] <= slot_time:
                event = day_events[event_index]
                if event["event_type"] == "checkin":
                    current_children[event["person_id"]] = event["class_name"]
                elif event["event_type"] == "checkout":
                    current_children.pop(event["person_id"], None)
                event_index += 1

            class_counts = {}
            for class_name in current_children.values():
                class_counts[class_name] = class_counts.get(class_name, 0) + 1
            class_text = "; ".join(f"{class_name}: {count}" for class_name, count in sorted(class_counts.items()))
            summary_rows.append(
                [
                    date.strftime("%Y-%m-%d"),
                    slot_time.strftime("%H:%M"),
                    len(current_children),
                    class_text,
                ]
            )
            slot_time += timedelta(minutes=15)

    return summary_rows


def acceo_date_text(value):
    return f"{value.month}/{value.day}/{value.year}"


def require_pymupdf():
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError(
            "PyMuPDF is required to generate PDF reports. "
            "Install dependencies with: python -m pip install -r requirements.txt, "
            "then rebuild the desktop app. "
            f"Details: {exc}"
        ) from exc
    return fitz


def monday_for_date(value):
    return value - timedelta(days=value.weekday())


def load_acceo_template_closed_offsets():
    template_paths = list(FORM_DIR.glob("Fiche assiduit*detaillee*.pdf"))
    if not template_paths:
        return {(2, 2), (3, 2)}

    try:
        import fitz

        doc = fitz.open(str(template_paths[0]))
        page = doc[0]
        words = page.get_text("words")
    except Exception:
        return {(2, 2), (3, 2)}

    closed_offsets = set()
    row_y = [325.0, 344.0]
    week_by_y = {325.0: 2, 344.0: 3}
    for x0, y0, _x1, _y1, text, *_rest in words:
        if text != "F":
            continue
        if not (280 <= y0 <= 360):
            continue
        week_index = min(row_y, key=lambda y: abs(y - y0))
        if abs(week_index - y0) > 8:
            continue
        if 290 <= x0 <= 310:
            closed_offsets.add((week_by_y[week_index], 2))

    return closed_offsets or {(2, 2), (3, 2)}


def load_children_for_acceo_report():
    with connect_db() as conn:
        return conn.execute(
            """
            SELECT id, name, COALESCE(class_name, '')
            FROM persons
            WHERE role = 'children'
            ORDER BY COALESCE(class_name, '') COLLATE NOCASE, name COLLATE NOCASE
            """
        ).fetchall()


def load_child_checkin_dates(start_date, end_date):
    start_text = start_date.strftime("%Y-%m-%d")
    end_text = end_date.strftime("%Y-%m-%d")
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT person_id, substr(timestamp, 1, 10)
            FROM attendance
            WHERE role = 'children'
              AND event_type = 'checkin'
              AND substr(timestamp, 1, 10) BETWEEN ? AND ?
            GROUP BY person_id, substr(timestamp, 1, 10)
            """,
            (start_text, end_text),
        ).fetchall()

    checkins = {}
    for person_id, date_text in rows:
        checkins.setdefault(person_id, set()).add(date_text)
    return checkins


def draw_text(page, x, y, text, size=9, bold=False):
    font = "helv"
    page.insert_text((x, y), str(text), fontsize=size, fontname=font, color=(0, 0, 0))


def draw_centered_text(page, x, y, width, text, size=9):
    text = str(text)
    text_width = fitz_get_text_length(text, size)
    draw_text(page, x + max((width - text_width) / 2, 0), y, text, size=size)


def fitz_get_text_length(text, size):
    try:
        import fitz

        return fitz.get_text_length(str(text), fontname="helv", fontsize=size)
    except Exception:
        return len(str(text)) * size * 0.5


def generate_acceo_detail_attendance_pdf(start_date, output_path):
    fitz = require_pymupdf()

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report()
    checkins = load_child_checkin_dates(start_date, end_date)
    closed_offsets = load_acceo_template_closed_offsets()
    closed_dates = set(load_closed_dates_setting())

    doc = fitz.open()
    day_names = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi", "Dimanche"]
    day_x = [185, 242, 299, 356, 413, 470, 527]
    day_width = 45
    row_y = [298, 317, 335, 354]
    now = datetime.now()

    for person_id, child_name, class_name in children:
        page = doc.new_page(width=612, height=792)
        page.draw_rect(fitz.Rect(51, 69, 574, 85), color=(0.5, 0.5, 0.5), fill=(0.5, 0.5, 0.5))
        draw_text(page, 428, 82, "Garderie L'Univers de Cassiopée", size=9)
        draw_text(
            page,
            51,
            64,
            f"Fiche d'assiduité détaillée du {acceo_date_text(start_date)}   au {acceo_date_text(end_date)}",
            size=12,
        )

        draw_text(page, 51, 103, "Nom de l'installation :", size=9)
        draw_text(page, 178, 103, "Installation 1", size=9)
        draw_text(page, 51, 117, "Nom de l'enfant :", size=9)
        draw_text(page, 178, 117, child_name, size=9)
        draw_text(page, 51, 130, "Nom du parent :", size=9)
        draw_text(page, 51, 143, "Nom du groupe :", size=9)
        draw_text(page, 178, 143, class_name or " ", size=9)
        draw_text(page, 51, 157, "Date de fin de fréquentation :", size=9)

        page.draw_rect(fitz.Rect(51.5, 169.5, 572, 258), color=(0, 0, 0), width=0.5)
        draw_text(page, 57, 184, "LÉGENDE", size=9)
        draw_text(page, 57, 199, "Codes de présences", size=9)
        draw_text(page, 318, 199, "Codes d'absence", size=9)
        legend_left = [
            ("P :", "Présence 1 jour"),
            ("R :", "Enfant remplaçant 1 jour"),
            ("E : Pédagogique 1 jour", ""),
            ("P½ :", "Présence ½ jour"),
            ("R½ :", "Enfant remplaçant ½ jour"),
            ("E½ :", "Pédagogique ½ jour"),
        ]
        legend_right = [
            ("A :", "Absence 1 jour"),
            ("M :", "Maladie 1 jour"),
            ("V :", "Vacances 1 jour"),
            ("F :", "Fermé 1 jour"),
            ("A½ :", "Absence ½ jour"),
            ("M½ :", "Maladie ½ jour"),
            ("V½ :", "Vacances ½ jour"),
        ]
        for idx, (code, label) in enumerate(legend_left):
            y = 215 + (idx % 3) * 18
            x = 57 if idx < 3 else 176
            draw_text(page, x, y, code, size=9)
            if label:
                draw_text(page, x + 24, y, label, size=9)
        for idx, (code, label) in enumerate(legend_right):
            y = 215 + (idx % 4) * 13
            x = 318 if idx < 4 else 438
            draw_text(page, x, y, code, size=9)
            draw_text(page, x + 24, y, label, size=9)

        page.draw_rect(fitz.Rect(51.5, 267, 572, 359), color=(0, 0, 0), width=0.5)
        header_y = 281
        draw_text(page, 69, header_y, "Semaine débutant le", size=9)
        for idx, day_name in enumerate(day_names):
            draw_centered_text(page, day_x[idx] - 8, header_y, day_width, day_name, size=9)

        for week_index, week_start in enumerate(week_starts):
            y = row_y[week_index]
            draw_text(page, 92 if week_index else 93, y, acceo_date_text(week_start), size=9)
            for day_index in range(7):
                current_date = week_start + timedelta(days=day_index)
                current_date_text = current_date.strftime("%Y-%m-%d")
                if current_date_text in closed_dates or (week_index, day_index) in closed_offsets:
                    code = "F"
                elif current_date_text in checkins.get(person_id, set()):
                    code = "P"
                else:
                    code = "A"
                draw_centered_text(page, day_x[day_index] - 6, y, 18, code, size=9)

        page.draw_rect(fitz.Rect(51.5, 369, 572, 425), color=(0, 0, 0), width=0.5)
        draw_text(page, 57, 390, "Signature du service de garde :", size=9)
        draw_text(page, 438, 390, "Date :", size=9)
        draw_text(page, 57, 414, "J'atteste que les renseignements inscrits sur cette fiche d'assiduité correspondent à la présence réelle de cet enfant.", size=7)

        page.draw_rect(fitz.Rect(51.5, 436, 572, 492), color=(0, 0, 0), width=0.5)
        draw_text(page, 57, 456, "Signature du parent :", size=9)
        draw_text(page, 438, 456, "Date :", size=9)
        draw_text(page, 57, 480, "J'atteste que les renseignements inscrits sur cette fiche d'assiduité correspondent à la présence réelle de mon enfant.", size=7)

        draw_text(page, 410, 767, f"Imprimé le {acceo_date_text(now.date())} à {now.strftime('%H:%M')}", size=8)
        draw_text(page, 515, 780, "Page 1 de 1", size=8)
        draw_text(page, 331, 790, "Ce rapport a été produit avec ACCEO Services de garde.", size=8)

    doc.save(str(output_path))
    doc.close()


def generate_acceo_summary_attendance_pdf(start_date, output_path):
    fitz = require_pymupdf()

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report()
    checkins = load_child_checkin_dates(start_date, end_date)
    closed_offsets = load_acceo_template_closed_offsets()
    closed_dates = set(load_closed_dates_setting())
    now = datetime.now()

    doc = fitz.open()
    day_short = ["Lun", "Mar", "Mer", "Jeu", "Ven", "Sam", "Dim"]
    day_x = [247, 274, 302, 329, 356, 383, 410]
    week_y = [285, 330, 375, 420]

    for person_id, child_name, class_name in children:
        page = doc.new_page(width=792, height=612)
        draw_text(page, 40, 48, "Garderie L'Univers de Cassiopée", size=9)
        draw_text(page, 40, 72, f"Fiche d'assiduité du {acceo_date_text(start_date)}  au {acceo_date_text(end_date)}", size=13)

        draw_text(page, 40, 105, "Groupe :", size=8)
        draw_text(page, 130, 105, class_name or " ", size=8)
        draw_text(page, 40, 120, "Dossier :", size=8)
        draw_text(page, 130, 120, str(person_id), size=8)
        draw_text(page, 40, 135, "Nom :", size=8)
        draw_text(page, 130, 135, child_name, size=8)
        draw_text(page, 40, 150, "Naissance :", size=8)
        draw_text(page, 40, 165, "Composante :", size=8)
        draw_text(page, 130, 165, "Garderie L'Univers de Cassiopée", size=8)
        draw_text(page, 40, 180, "Payeur principal :", size=8)
        draw_text(page, 40, 195, "Nom de l'établissement :", size=8)
        draw_text(page, 130, 195, "Garderie L'Univers de Cassiopée", size=8)
        draw_text(page, 40, 210, "Numéro d'établissement :", size=8)

        draw_text(page, 430, 105, "Légende :", size=8)
        legend = ["A : Absent", "E : Pédagogique", "F : Férié", "M : Maladie", "P : Présent", "R : Remplacement", "V : Vacances"]
        for idx, text in enumerate(legend):
            draw_text(page, 430 + (idx // 4) * 115, 120 + (idx % 4) * 15, text, size=8)

        draw_text(page, 430, 190, "Cumulatif des journées", size=8)
        draw_text(page, 548, 190, "Absence", size=8)
        draw_text(page, 620, 190, "Total", size=8)

        header_y = 265
        for idx, label in enumerate(day_short):
            draw_centered_text(page, day_x[idx] - 8, header_y, 22, label, size=8)
        draw_text(page, 445, header_y, "Absence", size=8)
        draw_text(page, 505, header_y, "Total", size=8)

        total_present = 0
        total_absent = 0
        for week_index, week_start in enumerate(week_starts):
            y = week_y[week_index]
            week_end = week_start + timedelta(days=6)
            week_present = 0
            week_absent = 0

            draw_text(page, 40, y, f"Du {acceo_date_text(week_start)}  au {acceo_date_text(week_end)}", size=8)
            draw_text(page, 40, y + 13, "Heures de garde", size=7)
            draw_text(page, 40, y + 26, "Équivalence en journée ou demi-journée", size=7)

            for day_index in range(7):
                current_date = week_start + timedelta(days=day_index)
                current_date_text = current_date.strftime("%Y-%m-%d")
                if current_date_text in closed_dates or (week_index, day_index) in closed_offsets:
                    code = "F"
                elif current_date_text in checkins.get(person_id, set()):
                    code = "P"
                    week_present += 1
                else:
                    code = "A"
                    week_absent += 1
                draw_centered_text(page, day_x[day_index] - 5, y, 18, code, size=9)

            total_present += week_present
            total_absent += week_absent
            draw_text(page, 455, y, str(week_absent), size=8)
            draw_text(page, 515, y, str(week_present), size=8)

        draw_text(page, 40, 485, "Nombre de jours de garde durant les quatre (4) semaines :", size=8)
        draw_text(page, 335, 485, str(total_present), size=8)
        draw_text(page, 430, 485, "Total depuis le 9/1/2025   :", size=8)
        draw_text(page, 560, 485, str(total_present), size=8)

        page.draw_line((40, 525), (370, 525), color=(0, 0, 0), width=0.5)
        page.draw_line((420, 525), (750, 525), color=(0, 0, 0), width=0.5)
        draw_text(page, 40, 542, "Signature du parent :", size=8)
        draw_text(page, 420, 542, "Signature du responsable :", size=8)
        draw_text(page, 40, 565, "Date :", size=8)
        draw_text(page, 420, 565, "Date :", size=8)
        draw_text(page, 40, 510, "Je déclare que les renseignements mentionnés sur cette fiche d'assiduité sont exacts.", size=8)

        draw_text(page, 610, 574, f"Imprimé le {acceo_date_text(now.date())} à {now.strftime('%H:%M')}", size=8)
        draw_text(page, 710, 590, "Page 1 de 1", size=8)
        draw_text(page, 530, 605, "Ce rapport a été produit avec ACCEO Services de garde.", size=8)

    doc.save(str(output_path))
    doc.close()


class AttendanceApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Daycare Attendance System")
        self.root.geometry("1380x680")
        self.root.minsize(1280, 640)

        self.cascade = cv2.CascadeClassifier(cv2.data.haarcascades + "haarcascade_frontalface_default.xml")
        self.qr_detector = cv2.QRCodeDetector()
        self.cap = cv2.VideoCapture(0, cv2.CAP_DSHOW)
        if not self.cap.isOpened():
            self.cap = cv2.VideoCapture(0)

        self.current_frame = None
        self.current_gray = None
        self.current_face_rect = None
        self.current_qr_rect = None
        self.current_qr_data = ""
        self.known_faces = load_known_faces()
        self.last_auto_scan_time = 0
        self.last_position_guidance_time = 0
        self.last_position_guidance_prompt = ""
        self.last_auto_record_times = {}
        self.daily_closeout_completed_date = None
        self.person_list_ids = []
        self.record_list_ids = []
        self.class_names = load_class_names()
        self.selected_class_name = self.class_names[0] if self.class_names else ""
        self.last_db_mtime = self.get_db_mtime()

        self.name_var = StringVar()
        self.role_var = StringVar(value="Child")
        self.class_var = StringVar(value=self.class_names[0] if self.class_names else "")
        self.person_sort_var = StringVar(value="Newest")
        self.attendance_prompt_var = StringVar(value=load_attendance_prompt_setting())
        self.attendance_prompt_var.trace_add("write", self.on_attendance_prompt_changed)
        self.status_var = StringVar(value="System started")

        self.build_ui()
        self.refresh_persons()
        self.refresh_records()
        self.update_camera()
        self.schedule_database_sync()
        self.schedule_remote_attendance_pull()
        self.schedule_daily_closeout()
        self.root.protocol("WM_DELETE_WINDOW", self.close)

    def on_attendance_prompt_changed(self, *args):
        save_attendance_prompt_setting(self.attendance_prompt_var.get())

    def make_button(self, parent, text, command, color, **pack_options):
        button = Button(
            parent,
            text=text,
            command=command,
            height=2,
            bg=color,
            activebackground=color,
            fg="#111111",
            activeforeground="#111111",
            relief="raised",
        )
        button.pack(**pack_options)
        return button

    def build_ui(self):
        main = Frame(self.root, padx=12, pady=12)
        main.pack(fill=BOTH, expand=True)

        left_controls = Frame(main, width=300)
        left_controls.pack(side=LEFT, fill=BOTH)
        left_controls.pack_propagate(False)

        center = Frame(main)
        center.pack(side=LEFT, fill=BOTH, expand=True, padx=12)

        right_controls = Frame(main, width=500)
        right_controls.pack(side=RIGHT, fill=BOTH)
        right_controls.pack_propagate(False)

        self.video_label = Label(center, bg="#111111", width=544, height=408)
        self.video_label.pack(anchor="n")

        Label(
            center,
            text="Teachers use face recognition. Children can use QR codes or face recognition. Check-in and check-out are recorded automatically.",
            fg="#1b5e20",
            wraplength=560,
            justify=LEFT,
        ).pack(fill="x", pady=(10, 0))

        Label(center, textvariable=self.status_var, anchor="w", fg="#1b5e20").pack(fill="x")

        setup_color = "#d8ecff"
        class_color = "#dff3ff"
        prompt_color = "#e3f7d9"
        stats_color = "#fff1bf"
        fiche_color = "#f0e7fb"
        danger_color = "#ffd7dc"

        form = LabelFrame(left_controls, text="Person Setup", padx=10, pady=10, bg=setup_color)
        form.pack(fill="x")

        Label(form, text="Name", bg=setup_color).pack(anchor="w")
        Entry(form, textvariable=self.name_var).pack(fill="x", pady=(2, 8))

        Label(form, text="Role", bg=setup_color).pack(anchor="w")
        ttk.Combobox(
            form,
            textvariable=self.role_var,
            values=("Child", "Teacher"),
            state="readonly",
        ).pack(fill="x", pady=(2, 8))

        self.make_button(form, "Add Person (Teacher: 10 Photos)", self.add_person, setup_color, fill="x", pady=(0, 0))
        self.make_button(form, "Import Children from children/list.xlsx", self.import_children_from_xlsx, setup_color, fill="x", pady=(0, 0))

        class_box = LabelFrame(left_controls, text="Class (Child only)", padx=10, pady=10, bg=class_color)
        class_box.pack(fill="x", pady=(10, 0))
        self.class_combo = ttk.Combobox(
            class_box,
            textvariable=self.class_var,
            values=self.class_names,
        )
        self.class_combo.pack(fill="x", pady=(2, 8))
        self.class_combo.bind("<<ComboboxSelected>>", self.on_class_selected)

        class_buttons = Frame(class_box, bg=class_color)
        class_buttons.pack(fill="x")
        self.make_button(class_buttons, "Add", self.add_class_name, class_color, side=LEFT, fill="x", expand=True)
        self.make_button(class_buttons, "Rename", self.rename_class_name, class_color, side=LEFT, fill="x", expand=True, padx=(8, 0))
        self.make_button(class_buttons, "Delete", self.delete_class_name, class_color, side=LEFT, fill="x", expand=True, padx=(8, 0))

        prompt_box = LabelFrame(left_controls, text="Attendance Prompt", padx=10, pady=10, bg=prompt_color)
        prompt_box.pack(fill="x", pady=(10, 0))
        prompt_inner = Frame(prompt_box, bg=prompt_color)
        prompt_inner.pack(fill="x")
        Radiobutton(
            prompt_inner,
            text="Voice greeting (HELLO...)",
            variable=self.attendance_prompt_var,
            value=ATTENDANCE_PROMPT_VOICE,
            bg=prompt_color,
            activebackground=prompt_color,
        ).pack(anchor="w")
        Radiobutton(
            prompt_inner,
            text="System bell only",
            variable=self.attendance_prompt_var,
            value=ATTENDANCE_PROMPT_BELL,
            bg=prompt_color,
            activebackground=prompt_color,
        ).pack(anchor="w", pady=(0, 0))

        reports_box = ttk.LabelFrame(left_controls, text="Reports", padding=10)
        reports_box.pack(fill="x", pady=(10, 0))
        self.make_button(reports_box, "Presence Summary", self.show_presence_summary, stats_color, fill="x")
        self.make_button(reports_box, "Export Excel", self.export_excel, stats_color, fill="x", pady=(0, 0))
        self.make_button(reports_box, "Generate 4-Week Fiche d'assiduité", self.open_acceo_detail_report_dialog, fiche_color, fill="x", pady=(14, 0))
        self.make_button(reports_box, "Manage Closed Dates (F)", self.open_closed_dates_dialog, fiche_color, fill="x", pady=(8, 0))

        persons_box = ttk.LabelFrame(right_controls, text="People", padding=10)
        persons_box.pack(fill=BOTH, expand=True, pady=(10, 0))
        sort_bar = Frame(persons_box)
        sort_bar.pack(fill="x", pady=(0, 6))
        Label(sort_bar, text="Sort").pack(side=LEFT, padx=(0, 8))
        self.person_sort_combo = ttk.Combobox(
            sort_bar,
            textvariable=self.person_sort_var,
            values=("Newest", "Name", "Class"),
            state="readonly",
            width=12,
        )
        self.person_sort_combo.pack(side=LEFT, fill="x", expand=True)
        self.person_sort_combo.bind("<<ComboboxSelected>>", self.on_person_sort_changed)
        person_columns = ("name", "role", "class", "created")
        self.person_list = ttk.Treeview(persons_box, columns=person_columns, show="headings", height=8, selectmode="extended")
        self.person_list.heading("name", text="Name")
        self.person_list.heading("role", text="Role")
        self.person_list.heading("class", text="Class")
        self.person_list.heading("created", text="Created")
        self.person_list.column("name", width=190, anchor="w")
        self.person_list.column("role", width=70, anchor="center")
        self.person_list.column("class", width=150, anchor="w")
        self.person_list.column("created", width=150, anchor="center")
        self.person_list.pack(fill=BOTH, expand=True)
        self.person_list.bind("<<TreeviewSelect>>", self.update_manual_attendance_buttons)
        manual_attendance_bar = Frame(persons_box)
        manual_attendance_bar.pack(fill="x", pady=(8, 0))
        self.manual_checkin_button = self.make_button(
            manual_attendance_bar,
            "Check In Selected Person",
            self.checkin_selected_person,
            prompt_color,
            side=LEFT,
            fill="x",
            expand=True,
            padx=(0, 4),
        )
        self.manual_checkout_button = self.make_button(
            manual_attendance_bar,
            "Check Out Selected Person",
            self.checkout_selected_person,
            prompt_color,
            side=LEFT,
            fill="x",
            expand=True,
            padx=(4, 0),
        )
        self.manual_attendance_button_color = prompt_color
        self.manual_attendance_disabled_color = "#eeeeee"
        self.update_manual_attendance_buttons()
        self.delete_person_button = self.make_button(persons_box, "Delete Selected Person(s) - Total: 0", self.delete_selected_person, danger_color, fill="x", pady=(0, 0))

        records_box = ttk.LabelFrame(right_controls, text="Recent Records", padding=10)
        records_box.pack(fill=BOTH, expand=True, pady=(10, 0))
        record_columns = ("time", "name", "role", "event", "by", "photo")
        self.record_list = ttk.Treeview(records_box, columns=record_columns, show="headings", height=9, selectmode="browse")
        self.record_list.heading("time", text="Time")
        self.record_list.heading("name", text="Name")
        self.record_list.heading("role", text="Role")
        self.record_list.heading("event", text="Event")
        self.record_list.heading("by", text="By")
        self.record_list.heading("photo", text="Photo")
        self.record_list.column("time", width=155, anchor="center")
        self.record_list.column("name", width=155, anchor="w")
        self.record_list.column("role", width=70, anchor="center")
        self.record_list.column("event", width=95, anchor="center")
        self.record_list.column("by", width=75, anchor="center")
        self.record_list.column("photo", width=80, anchor="center")
        self.record_list.pack(fill=BOTH, expand=True)
        self.delete_record_button = self.make_button(records_box, "Delete Selected Record - Checked In: 0", self.delete_selected_record, danger_color, fill="x", pady=(8, 0))

    def update_camera(self):
        try:
            ok, frame = self.cap.read()
        except cv2.error:
            ok, frame = False, None
        if ok and frame is not None:
            raw_frame = frame.copy()
            try:
                qr_data, qr_points, _ = self.qr_detector.detectAndDecode(raw_frame)
            except cv2.error:
                qr_data, qr_points = "", None
            self.current_qr_data = qr_data.strip() if qr_data else ""
            self.current_qr_rect = qr_points_rect(qr_points, raw_frame.shape[1])

            frame = cv2.flip(frame, 1)
            self.current_frame = frame.copy()
            try:
                gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
            except cv2.error:
                gray = None
            self.current_gray = gray
            self.current_face_rect = detect_face(gray, self.cascade)

            preview = frame.copy()
            if self.current_qr_rect is not None:
                x, y, w, h = self.current_qr_rect
                try:
                    cv2.rectangle(preview, (x, y), (x + w, y + h), (30, 120, 240), 3)
                except cv2.error:
                    pass
            if self.current_face_rect is not None:
                x, y, w, h = self.current_face_rect
                try:
                    cv2.rectangle(preview, (x, y), (x + w, y + h), (40, 190, 90), 2)
                except cv2.error:
                    pass
            try:
                self.auto_record_attendance()
            except Exception:
                self.status_var.set("Skipping invalid scan data. Continuing detection.")

            try:
                preview = cv2.cvtColor(preview, cv2.COLOR_BGR2RGB)
                preview = cv2.resize(preview, (544, 408))
                image = Image.fromarray(preview)
                self.photo = ImageTk.PhotoImage(image=image)
                self.video_label.configure(image=self.photo)
            except (cv2.error, ValueError):
                self.status_var.set("Skipping invalid camera frame. Continuing detection.")
        else:
            self.status_var.set("Cannot read camera. Please check the USB camera.")

        self.root.after(30, self.update_camera)

    def prompt_position_guidance(self, rect, frame_shape, min_size_ratio, max_size_ratio, allow_voice):
        if not allow_voice:
            return
        prompt = position_guidance_prompt(rect, frame_shape, min_size_ratio, max_size_ratio)
        if not prompt:
            return

        current_time = time.time()
        if (
            prompt == self.last_position_guidance_prompt
            and current_time - self.last_position_guidance_time < POSITION_GUIDANCE_COOLDOWN_SECONDS
        ):
            return
        if current_time - self.last_position_guidance_time < 1.0:
            return

        self.last_position_guidance_prompt = prompt
        self.last_position_guidance_time = current_time
        self.status_var.set(prompt)
        speak(prompt)

    def add_person(self):
        name = self.name_var.get().strip()
        role = ROLE_VALUES.get(self.role_var.get(), self.role_var.get())
        if not name:
            messagebox.showwarning("Notice", "Please enter a name.")
            return

        if role == "children":
            class_name = self.class_var.get().strip()
            if not class_name:
                messagebox.showwarning("Notice", "Please select a class for this child.")
                return
            if class_name not in self.class_names:
                messagebox.showwarning("Notice", "Please add this class before using it.")
                return
            if self.child_name_exists(name):
                messagebox.showwarning("Notice", "A child with this name already exists. Please enter a different name.")
                return
            self.add_child_from_upload(name, class_name)
            return

        if self.current_gray is None or self.current_face_rect is None:
            messagebox.showwarning("Notice", "Please keep the face visible in the camera view.")
            return

        faces = self.capture_teacher_face_samples()
        if len(faces) < TEACHER_FACE_SAMPLE_COUNT:
            messagebox.showwarning(
                "Notice",
                f"Captured {len(faces)} valid face samples. Teachers need {TEACHER_FACE_SAMPLE_COUNT}. Please adjust distance and try again.",
            )
            return

        timestamp = int(time.time())
        safe_name = safe_filename(name)
        photo_paths = []
        for index, face in enumerate(faces, start=1):
            filename = f"{timestamp}_{safe_name}_face_{index}.png"
            photo_path = FACE_DIR / filename
            cv2.imwrite(str(photo_path), face)
            photo_paths.append(photo_path)

        with connect_db() as conn:
            cursor = conn.execute(
                "INSERT INTO persons(name, role, photo_path, created_at) VALUES (?, ?, ?, ?)",
                (name, role, str(photo_paths[0]), now_text()),
            )
            person_id = cursor.lastrowid
            conn.executemany(
                "INSERT INTO teacher_face_samples(person_id, photo_path, created_at) VALUES (?, ?, ?)",
                [(person_id, str(path), now_text()) for path in photo_paths],
            )

        self.name_var.set("")
        self.reload_faces()
        self.refresh_persons()
        self.status_var.set(f"Added teacher: {name} with {len(photo_paths)} face samples")

    def add_child_from_upload(self, name, class_name):
        if self.child_name_exists(name):
            messagebox.showwarning("Notice", "A child with this name already exists. Please enter a different name.")
            return
        if not class_name:
            messagebox.showwarning("Notice", "Please select a class for this child.")
            return
        if class_name not in self.class_names:
            messagebox.showwarning("Notice", "Please add this class before using it.")
            return

        image_path = filedialog.askopenfilename(
            title="Select child photo",
            filetypes=(
                ("Image files", "*.jpg *.jpeg *.png *.bmp"),
                ("All files", "*.*"),
            ),
        )
        if not image_path:
            return

        source_path = Path(image_path)
        if source_path.suffix.lower() not in {".jpg", ".jpeg", ".png", ".bmp"}:
            messagebox.showwarning("Notice", "Please select a JPG, PNG, or BMP photo.")
            return

        try:
            with Image.open(source_path) as image:
                image.verify()
        except (OSError, ValueError):
            messagebox.showwarning("Notice", "Cannot read this photo. Please select another image.")
            return

        safe_name = safe_filename(name)
        photo_path = CHILDREN_DIR / f"{safe_name}{source_path.suffix.lower()}"
        try:
            if source_path.resolve() != photo_path.resolve():
                shutil.copy2(source_path, photo_path)
        except OSError:
            messagebox.showwarning("Notice", "Cannot copy the child photo. Please try another location.")
            return

        token = child_token(name)
        try:
            qr_path, card_path = save_child_card(name, photo_path, token, class_name)
        except (OSError, ValueError, cv2.error):
            messagebox.showwarning("Notice", "Cannot generate the child card from this photo.")
            return

        with connect_db() as conn:
            row = conn.execute(
                "SELECT id FROM persons WHERE role = 'children' AND name = ?",
                (name,),
            ).fetchone()
            if row:
                messagebox.showwarning("Notice", "A child with this name already exists. Please enter a different name.")
                return
            else:
                conn.execute(
                    "INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at) VALUES (?, 'children', ?, ?, ?, ?)",
                    (name, class_name, str(photo_path), token, now_text()),
                )

        self.name_var.set("")
        self.class_var.set(self.class_names[0] if self.class_names else "")
        self.refresh_persons()
        self.status_var.set(f"Added child: {name} ({class_name}). Card saved to {card_path}")
        messagebox.showinfo(
            "Complete",
            f"Child card generated.\nQR code:\n{qr_path}\nCard:\n{card_path}",
        )

    def import_children_from_xlsx(self):
        xlsx_path = CHILDREN_DIR / "list.xlsx"
        if not xlsx_path.exists():
            selected_path = filedialog.askopenfilename(
                title="Select children/list.xlsx",
                filetypes=(("Excel files", "*.xlsx"), ("All files", "*.*")),
            )
            if not selected_path:
                return
            xlsx_path = Path(selected_path)

        try:
            rows = read_xlsx_rows(xlsx_path)
        except (OSError, ValueError, KeyError, zipfile.BadZipFile, ET.ParseError) as exc:
            messagebox.showwarning("Notice", f"Cannot read children/list.xlsx.\n{exc}")
            return

        children = parse_children_from_xlsx_rows(rows)
        if not children:
            preview = xlsx_import_preview(rows)
            detail = f"\n\nRead from A/E columns:\n{preview}" if preview else ""
            messagebox.showwarning(
                "Notice",
                "No child names and classes were found in the Excel file.\n"
                "Please make sure A+B columns are child name and E column is class."
                f"{detail}",
            )
            return

        imported_count = 0
        skipped_count = 0
        added_classes = set()
        with connect_db() as conn:
            for name, class_name in children:
                existing_child = conn.execute(
                    "SELECT 1 FROM persons WHERE role = 'children' AND name = ? LIMIT 1",
                    (name,),
                ).fetchone()
                if existing_child:
                    skipped_count += 1
                    continue

                existing_class = conn.execute(
                    "SELECT 1 FROM class_names WHERE name = ? LIMIT 1",
                    (class_name,),
                ).fetchone()
                if not existing_class:
                    conn.execute(
                        "INSERT INTO class_names(name, created_at) VALUES (?, ?)",
                        (class_name, now_text()),
                    )
                    added_classes.add(class_name)

                photo_path = save_child_placeholder_photo(name, class_name)
                token = child_token(name)
                save_child_card(name, photo_path, token, class_name)
                conn.execute(
                    "INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at) VALUES (?, 'children', ?, ?, ?, ?)",
                    (name, class_name, str(photo_path), token, now_text()),
                )
                imported_count += 1

        self.refresh_class_names()
        self.refresh_persons()
        self.status_var.set(f"Imported {imported_count} children from children/list.xlsx; skipped {skipped_count} duplicates")
        messagebox.showinfo(
            "Complete",
            f"Imported {imported_count} children from:\n{xlsx_path}\n\n"
            f"Skipped duplicates: {skipped_count}\n"
            f"Added classes: {len(added_classes)}\n"
            f"Child cards saved in:\n{CARD_DIR}",
        )

    def child_name_exists(self, name):
        with connect_db() as conn:
            row = conn.execute(
                "SELECT 1 FROM persons WHERE role = 'children' AND name = ? LIMIT 1",
                (name,),
            ).fetchone()
        return row is not None

    def refresh_class_names(self):
        self.class_names = load_class_names()
        self.class_combo.configure(values=self.class_names)
        if self.class_var.get().strip() not in self.class_names:
            self.class_var.set(self.class_names[0] if self.class_names else "")
        self.selected_class_name = self.class_var.get().strip()

    def on_class_selected(self, _event=None):
        self.selected_class_name = self.class_var.get().strip()

    def add_class_name(self):
        class_name = self.class_var.get().strip()
        if not class_name:
            messagebox.showwarning("Notice", "Please enter a class name.")
            return
        if class_name in self.class_names:
            self.status_var.set(f"Class already exists: {class_name}")
            return

        with connect_db() as conn:
            conn.execute(
                "INSERT INTO class_names(name, created_at) VALUES (?, ?)",
                (class_name, now_text()),
            )
        self.refresh_class_names()
        self.class_var.set(class_name)
        self.selected_class_name = class_name
        self.status_var.set(f"Added class: {class_name}")

    def rename_class_name(self):
        old_name = self.selected_class_name.strip()
        new_name = self.class_var.get().strip()
        if not old_name or old_name not in self.class_names:
            messagebox.showwarning("Notice", "Please select a class to rename.")
            return
        if not new_name:
            messagebox.showwarning("Notice", "Please enter the new class name.")
            return
        if new_name == old_name:
            self.status_var.set(f"Class unchanged: {old_name}")
            return
        if new_name in self.class_names:
            messagebox.showwarning("Notice", "This class name already exists.")
            return

        with connect_db() as conn:
            conn.execute("UPDATE class_names SET name = ? WHERE name = ?", (new_name, old_name))
            conn.execute(
                "UPDATE persons SET class_name = ? WHERE role = 'children' AND class_name = ?",
                (new_name, old_name),
            )
        self.refresh_class_names()
        self.class_var.set(new_name)
        self.selected_class_name = new_name
        self.refresh_persons()
        self.status_var.set(f"Renamed class: {old_name} -> {new_name}")

    def delete_class_name(self):
        class_name = self.selected_class_name.strip() or self.class_var.get().strip()
        if not class_name or class_name not in self.class_names:
            messagebox.showwarning("Notice", "Please select a class to delete.")
            return

        with connect_db() as conn:
            child_count = conn.execute(
                "SELECT COUNT(*) FROM persons WHERE role = 'children' AND class_name = ?",
                (class_name,),
            ).fetchone()[0]
        if child_count:
            messagebox.showwarning("Notice", "This class is used by children and cannot be deleted.")
            return
        confirmed = messagebox.askyesno("Confirm", f"Delete class {class_name}?")
        if not confirmed:
            return

        with connect_db() as conn:
            conn.execute("DELETE FROM class_names WHERE name = ?", (class_name,))
        self.refresh_class_names()
        self.status_var.set(f"Deleted class: {class_name}")

    def capture_teacher_face_samples(self):
        faces = []
        attempts = 0
        prompted_sample_number = 0
        while len(faces) < TEACHER_FACE_SAMPLE_COUNT and attempts < TEACHER_FACE_SAMPLE_COUNT * 8:
            target_sample_number = len(faces) + 1
            if prompted_sample_number != target_sample_number:
                prompt = f"Please take photo {target_sample_number}."
                self.status_var.set(prompt)
                play_system_bell()
                prompted_sample_number = target_sample_number
                time.sleep(1.0)
            attempts += 1
            if attempts == 1:
                gray = self.current_gray
                face_rect = self.current_face_rect
            else:
                try:
                    ok, frame = self.cap.read()
                except cv2.error:
                    ok, frame = False, None
                if not ok or frame is None:
                    continue
                try:
                    frame = cv2.flip(frame, 1)
                    gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
                except cv2.error:
                    continue
                face_rect = detect_face(gray, self.cascade)
            face = normalize_face(gray, face_rect)
            if face is not None:
                faces.append(face)
                if len(faces) < TEACHER_FACE_SAMPLE_COUNT:
                    prompt = f"Photo {len(faces)} complete. Please take photo {len(faces) + 1}."
                else:
                    prompt = f"Photo {len(faces)} complete."
                self.status_var.set(prompt)
                play_system_bell()
                time.sleep(1.0)
            time.sleep(0.08)
        return faces

    def import_children(self):
        count, card_count = sync_children_from_directory()
        self.refresh_persons()
        self.status_var.set(f"Imported/updated {count} children and generated {card_count} QR cards")
        messagebox.showinfo(
            "Complete",
            f"Imported/updated {count} children.\nQR cards saved in:\n{CARD_DIR}",
        )

    def auto_record_attendance(self):
        current_time = time.time()
        if current_time - self.last_auto_scan_time < AUTO_SCAN_INTERVAL_SECONDS:
            return
        self.last_auto_scan_time = current_time

        if self.current_qr_data:
            if not is_valid_child_qr_data(self.current_qr_data):
                self.status_var.set("Skipping incomplete or invalid QR code. Continuing detection.")
                return
            person = self.find_child_by_qr(self.current_qr_data)
            if person is None:
                self.status_var.set("Unrecognized child QR code. Import children and generate QR cards first.")
                return
            self.record_person(person, current_time)
            return

        if self.current_qr_rect is not None:
            self.status_var.set("QR code detected but not readable. Please adjust the card position.")
            return

        if self.current_gray is None or self.current_face_rect is None:
            return
        face = normalize_face(self.current_gray, self.current_face_rect)
        if face is None:
            self.status_var.set("Skipping unclear face data. Continuing detection.")
            return
        person, score = find_match(face, self.known_faces)
        if person is None:
            score_text = "No face data" if score is None else f"Face match is too low: {score:.1f}"
            self.status_var.set(f"Auto recognition running: {score_text}")
            return

        self.record_person(person, current_time)

    def find_child_by_qr(self, qr_data):
        try:
            with connect_db() as conn:
                row = conn.execute(
                    "SELECT id, name, role FROM persons WHERE role = 'children' AND qr_token = ?",
                    (qr_data,),
                ).fetchone()
        except sqlite3.Error:
            self.status_var.set("Skipping QR lookup error. Continuing detection.")
            return None
        if not row:
            return None
        return {"id": row[0], "name": row[1], "role": row[2]}

    def record_person(self, person, current_time, event_type=None, enforce_cooldown=True, source="desktop"):
        person_id = person["id"]
        if enforce_cooldown:
            last_record_time = self.last_auto_record_times.get(person_id, 0)
            if person["role"] == "children":
                cooldown_seconds = CHILD_RECORD_COOLDOWN_SECONDS
            else:
                cooldown_seconds = TEACHER_RECORD_COOLDOWN_SECONDS
            elapsed_seconds = current_time - last_record_time
            if elapsed_seconds < cooldown_seconds:
                remaining_minutes = int((cooldown_seconds - elapsed_seconds + 59) // 60)
                self.status_var.set(f"{person['name']} already recorded. Please wait {remaining_minutes} minute(s).")
                return

        try:
            if event_type is None:
                event_type = self.next_event_type(person_id)
            elif event_type not in EVENT_LABELS:
                self.status_var.set("Skipping invalid attendance event.")
                return
            should_speak = self.is_first_event_today(person_id, event_type)
        except sqlite3.Error:
            self.status_var.set("Skipping attendance lookup error. Continuing detection.")
            return
        timestamp = now_text()
        snapshot_path = save_teacher_attendance_snapshot(person, event_type, self.current_frame)
        operator_name = person["name"] if source == "desktop" else OPERATION_LABELS["system"]
        try:
            with connect_db() as conn:
                conn.execute(
                    "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path, source, operator_name) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (person["id"], person["name"], person["role"], event_type, timestamp, snapshot_path, source, operator_name),
                )
        except sqlite3.Error:
            self.status_var.set("Skipping attendance save error. Continuing detection.")
            return

        self.last_auto_record_times[person_id] = current_time
        self.queue_remote_attendance_sync(
            {
                "person_id": person["id"],
                "name": person["name"],
                "role": person["role"],
                "event_type": event_type,
                "timestamp": timestamp,
                "source": source,
                "operator_name": operator_name,
            }
        )
        event_label = EVENT_LABELS[event_type]
        role_label = ROLE_LABELS.get(person["role"], person["role"])
        self.status_var.set(f"{person['name']} ({role_label}) {event_label} successful  {timestamp}")
        if self.attendance_prompt_var.get() == ATTENDANCE_PROMPT_BELL:
            play_system_bell()
        elif should_speak:
            speak(attendance_voice_prompt(person, event_type))
        self.refresh_records()
        self.update_manual_attendance_buttons()

    def queue_remote_attendance_sync(self, payload):
        if not configured_webapp_url() or not configured_desktop_sync_token():
            return
        worker = threading.Thread(target=self.remote_attendance_sync_worker, args=(payload,), daemon=True)
        worker.start()

    def remote_attendance_sync_worker(self, payload):
        ok, detail = post_remote_attendance(payload)
        person_name = payload.get("name", "Unknown")
        event_label = EVENT_LABELS.get(payload.get("event_type"), payload.get("event_type", "event"))
        if ok:
            message = f"Network sync complete: {person_name} {event_label}"
        else:
            message = f"Network sync failed: {person_name} {event_label} ({detail})"
        log_desktop_sync(message)
        try:
            self.root.after(0, lambda: self.status_var.set(message))
        except RuntimeError:
            pass

    def schedule_remote_attendance_pull(self):
        if configured_webapp_url() and configured_desktop_sync_token():
            worker = threading.Thread(target=self.remote_attendance_pull_worker, daemon=True)
            worker.start()
        self.root.after(REMOTE_ATTENDANCE_PULL_INTERVAL_MS, self.schedule_remote_attendance_pull)

    def remote_attendance_pull_worker(self):
        ok, detail, records = fetch_remote_attendance()
        if not ok:
            log_desktop_sync(f"Network pull failed: {detail}")
            return
        try:
            imported_count = self.import_remote_attendance_records(records)
        except sqlite3.Error as exc:
            log_desktop_sync(f"Network pull database error: {exc}")
            return
        if imported_count:
            message = f"Network pull imported {imported_count} attendance record(s)"
            log_desktop_sync(message)
            try:
                self.root.after(0, self.refresh_persons)
                self.root.after(0, self.refresh_records)
                self.root.after(0, lambda: self.status_var.set(message))
            except RuntimeError:
                pass

    def import_remote_attendance_records(self, records):
        imported_count = 0
        with connect_db() as conn:
            for record in records:
                if not isinstance(record, dict):
                    continue
                name = str(record.get("name", "")).strip()
                role = str(record.get("role", "")).strip()
                event_type = str(record.get("event_type", "")).strip()
                raw_timestamp = str(record.get("timestamp", "")).strip()
                timestamp = raw_timestamp
                class_name = str(record.get("class_name", "")).strip()
                source = str(record.get("source", "system")).strip()
                if source != "desktop":
                    source = "system"
                operator_name = str(record.get("operator_name", "")).strip()
                if not operator_name:
                    operator_name = name if source == "desktop" else OPERATION_LABELS["system"]
                if not name or role not in {"children", "teachers"} or event_type not in EVENT_LABELS:
                    continue
                try:
                    timestamp = normalize_remote_attendance_timestamp(timestamp)
                except ValueError:
                    continue
                person = conn.execute(
                    "SELECT id FROM persons WHERE lower(name) = lower(?) AND role = ? ORDER BY id LIMIT 1",
                    (name, role),
                ).fetchone()
                if person:
                    person_id = person[0]
                    if role == "children" and class_name:
                        conn.execute("UPDATE persons SET class_name = ? WHERE id = ? AND COALESCE(class_name, '') = ''", (class_name, person_id))
                else:
                    cursor = conn.execute(
                        "INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at) VALUES (?, ?, ?, '', ?, ?)",
                        (name, role, class_name if role == "children" else "", f"CHILD:{name}" if role == "children" else None, now_text()),
                    )
                    person_id = cursor.lastrowid

                duplicate = conn.execute(
                    """
                    SELECT 1 FROM attendance
                    WHERE name = ? AND role = ? AND event_type = ? AND timestamp = ?
                    LIMIT 1
                    """,
                    (name, role, event_type, timestamp),
                ).fetchone()
                if duplicate:
                    continue
                if raw_timestamp != timestamp:
                    raw_duplicate = conn.execute(
                        """
                        SELECT id FROM attendance
                        WHERE name = ? AND role = ? AND event_type = ? AND timestamp = ?
                        LIMIT 1
                        """,
                        (name, role, event_type, raw_timestamp),
                    ).fetchone()
                    if raw_duplicate:
                        conn.execute(
                            "UPDATE attendance SET timestamp = ? WHERE id = ?",
                            (timestamp, raw_duplicate[0]),
                        )
                        imported_count += 1
                        continue
                conn.execute(
                    "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path, source, operator_name) VALUES (?, ?, ?, ?, ?, NULL, ?, ?)",
                    (person_id, name, role, event_type, timestamp, source, operator_name),
                )
                imported_count += 1
        return imported_count

    def selected_person_attendance_status(self):
        selection = self.person_list.selection()
        if len(selection) != 1:
            return None
        try:
            person_id = int(selection[0])
        except ValueError:
            return None
        today = datetime.now().strftime("%Y-%m-%d")
        try:
            with connect_db() as conn:
                row = conn.execute(
                    """
                    SELECT persons.role, attendance.event_type
                    FROM persons
                    LEFT JOIN attendance
                      ON attendance.person_id = persons.id
                     AND attendance.timestamp LIKE ?
                    WHERE persons.id = ?
                    ORDER BY attendance.timestamp DESC, attendance.id DESC
                    LIMIT 1
                    """,
                    (f"{today}%", person_id),
                ).fetchone()
        except sqlite3.Error:
            return None
        if not row or row[0] not in {"children", "teachers"}:
            return None
        return "in" if row[1] == "checkin" else "out"

    def set_manual_attendance_button_state(self, button, enabled):
        color = self.manual_attendance_button_color if enabled else self.manual_attendance_disabled_color
        button.configure(
            state="normal" if enabled else "disabled",
            bg=color,
            activebackground=color,
            disabledforeground="#777777",
        )

    def update_manual_attendance_buttons(self, _event=None):
        if not hasattr(self, "manual_checkin_button") or not hasattr(self, "manual_checkout_button"):
            return
        status = self.selected_person_attendance_status()
        if status == "in":
            self.set_manual_attendance_button_state(self.manual_checkin_button, False)
            self.set_manual_attendance_button_state(self.manual_checkout_button, True)
        elif status == "out":
            self.set_manual_attendance_button_state(self.manual_checkin_button, True)
            self.set_manual_attendance_button_state(self.manual_checkout_button, False)
        else:
            self.set_manual_attendance_button_state(self.manual_checkin_button, False)
            self.set_manual_attendance_button_state(self.manual_checkout_button, False)

    def selected_person_for_manual_attendance(self):
        selection = self.person_list.selection()
        if len(selection) != 1:
            messagebox.showwarning("Notice", "Please select exactly one person.")
            return None
        try:
            person_id = int(selection[0])
        except ValueError:
            messagebox.showwarning("Notice", "Please refresh the people list and try again.")
            return None
        try:
            with connect_db() as conn:
                row = conn.execute(
                    "SELECT id, name, role FROM persons WHERE id = ?",
                    (person_id,),
                ).fetchone()
        except sqlite3.Error:
            self.status_var.set("Cannot load selected person. Please try again.")
            return None
        if not row:
            messagebox.showwarning("Notice", "Selected person was already deleted.")
            self.refresh_persons()
            return None
        if row[2] not in {"children", "teachers"}:
            messagebox.showwarning("Notice", "Manual buttons are for children and teachers only.")
            return None
        return {"id": row[0], "name": row[1], "role": row[2]}

    def checkin_selected_person(self):
        person = self.selected_person_for_manual_attendance()
        if person is None:
            return
        self.record_person(person, time.time(), event_type="checkin", enforce_cooldown=False, source="desktop_manual")

    def checkout_selected_person(self):
        person = self.selected_person_for_manual_attendance()
        if person is None:
            return
        self.record_person(person, time.time(), event_type="checkout", enforce_cooldown=False, source="desktop_manual")

    def selected_child_attendance_status(self):
        return self.selected_person_attendance_status()

    def selected_child_for_manual_attendance(self):
        return self.selected_person_for_manual_attendance()

    def checkin_selected_child(self):
        self.checkin_selected_person()

    def checkout_selected_child(self):
        self.checkout_selected_person()

    def next_event_type(self, person_id):
        today = datetime.now().strftime("%Y-%m-%d")
        with connect_db() as conn:
            row = conn.execute(
                """
                SELECT event_type FROM attendance
                WHERE person_id = ? AND timestamp LIKE ?
                ORDER BY timestamp DESC, id DESC
                LIMIT 1
                """,
                (person_id, f"{today}%"),
            ).fetchone()
        if row and row[0] == "checkin":
            return "checkout"
        return "checkin"

    def is_first_event_today(self, person_id, event_type):
        today = datetime.now().strftime("%Y-%m-%d")
        with connect_db() as conn:
            row = conn.execute(
                """
                SELECT 1 FROM attendance
                WHERE person_id = ? AND event_type = ? AND timestamp LIKE ?
                LIMIT 1
                """,
                (person_id, event_type, f"{today}%"),
            ).fetchone()
        return row is None

    def reload_faces(self):
        self.known_faces = load_known_faces()
        self.status_var.set(f"Loaded {len(self.known_faces)} face samples")

    def delete_selected_person(self):
        selection = self.person_list.selection()
        if not selection:
            messagebox.showwarning("Notice", "Please select one or more people to delete.")
            return

        try:
            person_ids = [int(item_id) for item_id in selection]
        except ValueError:
            messagebox.showwarning("Notice", "Please refresh the people list and try again.")
            return

        placeholders = ",".join("?" for _ in person_ids)
        try:
            with connect_db() as conn:
                rows = conn.execute(
                    f"SELECT id, name, role, photo_path FROM persons WHERE id IN ({placeholders})",
                    person_ids,
                ).fetchall()
        except sqlite3.Error:
            self.status_var.set("Cannot load selected people. Please try again.")
            return

        if not rows:
            self.status_var.set("Selected people were already deleted.")
            self.refresh_persons()
            return

        rows_by_id = {row[0]: row for row in rows}
        people = [rows_by_id[person_id] for person_id in person_ids if person_id in rows_by_id]
        missing_count = len(person_ids) - len(people)
        preview_names = ", ".join(row[1] for row in people[:5])
        if len(people) > 5:
            preview_names += f", and {len(people) - 5} more"
        missing_text = f"\n\n{missing_count} selected person(s) were already deleted." if missing_count else ""
        confirmed = messagebox.askyesno(
            "Confirm",
            f"Delete {len(people)} selected person(s)?\n{preview_names}\n\n"
            f"This will also remove their attendance records.{missing_text}",
        )
        if not confirmed:
            return

        files_to_delete = []
        for person_id, name, role, photo_path in people:
            files_to_delete.extend(self.person_files_to_delete(person_id, name, role, photo_path))

        try:
            with connect_db() as conn:
                for person_id, _name, _role, _photo_path in people:
                    conn.execute("DELETE FROM attendance WHERE person_id = ?", (person_id,))
                    conn.execute("DELETE FROM teacher_face_samples WHERE person_id = ?", (person_id,))
                    conn.execute("DELETE FROM persons WHERE id = ?", (person_id,))
        except sqlite3.Error:
            self.status_var.set("Cannot delete selected people. Please try again.")
            return

        for path in files_to_delete:
            try:
                if path and path.exists():
                    path.unlink()
            except OSError:
                pass

        for person_id, _name, _role, _photo_path in people:
            self.last_auto_record_times.pop(person_id, None)
        self.reload_faces()
        self.refresh_persons()
        self.refresh_records()
        self.status_var.set(f"Deleted {len(people)} selected person(s)")

    def person_files_to_delete(self, person_id, name, role, photo_path):
        paths = []
        if role == "teachers" and photo_path:
            paths.append(Path(photo_path))
            try:
                with connect_db() as conn:
                    sample_paths = conn.execute(
                        "SELECT photo_path FROM teacher_face_samples WHERE person_id = ?",
                        (person_id,),
                    ).fetchall()
                paths.extend(Path(row[0]) for row in sample_paths)
                attendance_photo_paths = conn.execute(
                    "SELECT snapshot_path FROM attendance WHERE person_id = ? AND COALESCE(snapshot_path, '') <> ''",
                    (person_id,),
                ).fetchall()
                paths.extend(Path(row[0]) for row in attendance_photo_paths)
            except sqlite3.Error:
                pass
        if role == "children":
            safe_name = safe_filename(name)
            paths.append(QR_DIR / f"{safe_name}.png")
            paths.append(CARD_DIR / f"{safe_name}_card.png")
        return paths

    def on_person_sort_changed(self, _event=None):
        self.refresh_persons()
        self.status_var.set(f"People sorted by {self.person_sort_var.get()}")

    def person_sort_order_sql(self):
        sort_mode = self.person_sort_var.get()
        if sort_mode == "Name":
            return "ORDER BY name COLLATE NOCASE, role COLLATE NOCASE, id DESC"
        if sort_mode == "Class":
            return (
                "ORDER BY CASE WHEN role = 'children' THEN 0 ELSE 1 END, "
                "COALESCE(class_name, '') COLLATE NOCASE, name COLLATE NOCASE, id DESC"
            )
        return "ORDER BY id DESC"

    def refresh_persons(self):
        self.person_list.delete(*self.person_list.get_children())
        self.person_list_ids = []
        with connect_db() as conn:
            rows = conn.execute(
                f"SELECT id, name, role, class_name, created_at FROM persons {self.person_sort_order_sql()}"
            ).fetchall()
        for person_id, name, role, class_name, created_at in rows:
            self.person_list_ids.append(person_id)
            role_label = ROLE_LABELS.get(role, role)
            self.person_list.insert(
                "",
                END,
                iid=str(person_id),
                values=(name, role_label, class_name if role == "children" else "", created_at),
            )
        self.delete_person_button.configure(text=f"Delete Selected Person(s) - Total: {len(self.person_list_ids)}")
        self.update_manual_attendance_buttons()

    def refresh_records(self):
        self.record_list.delete(*self.record_list.get_children())
        self.record_list_ids = []
        with connect_db() as conn:
            rows = conn.execute(
                "SELECT id, name, role, event_type, timestamp, COALESCE(snapshot_path, ''), COALESCE(source, 'system'), COALESCE(operator_name, '') FROM attendance ORDER BY id DESC LIMIT 30"
            ).fetchall()
            checked_in_count = self.checked_in_without_checkout_count(conn)
        for record_id, name, role, event_type, timestamp, snapshot_path, source, operator_name in rows:
            self.record_list_ids.append(record_id)
            self.record_list.insert(
                "",
                END,
                iid=str(record_id),
                values=(timestamp, name, ROLE_LABELS.get(role, role), EVENT_LABELS.get(event_type, event_type), attendance_operator_name(name, source, operator_name), "Saved" if snapshot_path else ""),
            )
        self.delete_record_button.configure(text=f"Delete Selected Record - Checked In: {checked_in_count}")

    def get_db_mtime(self):
        try:
            return os.path.getmtime(DB_PATH)
        except OSError:
            return None

    def schedule_database_sync(self):
        current_mtime = self.get_db_mtime()
        if current_mtime is not None and current_mtime != self.last_db_mtime:
            self.last_db_mtime = current_mtime
            self.refresh_persons()
            self.refresh_records()
            self.status_var.set("Attendance data updated from shared database")
        self.root.after(2000, self.schedule_database_sync)

    def checked_in_without_checkout_count(self, conn):
        today = datetime.now().strftime("%Y-%m-%d")
        row = conn.execute(
            """
            SELECT COUNT(*)
            FROM (
                SELECT attendance.person_id, attendance.event_type
                FROM attendance
                JOIN persons ON persons.id = attendance.person_id
                WHERE attendance.role = 'children'
                  AND persons.role = 'children'
                  AND attendance.timestamp LIKE ?
                  AND attendance.id = (
                      SELECT latest.id
                      FROM attendance AS latest
                      WHERE latest.person_id = attendance.person_id
                        AND latest.timestamp LIKE ?
                      ORDER BY latest.timestamp DESC, latest.id DESC
                      LIMIT 1
                  )
            )
            WHERE event_type = 'checkin'
            """,
            (f"{today}%", f"{today}%"),
        ).fetchone()
        return row[0] if row else 0

    def delete_selected_record(self):
        selection = self.record_list.selection()
        if not selection:
            messagebox.showwarning("Notice", "Please select an attendance record to delete.")
            return

        try:
            record_id = int(selection[0])
        except ValueError:
            messagebox.showwarning("Notice", "Please refresh the records list and try again.")
            return

        record_values = self.record_list.item(selection[0], "values")
        record_text = " | ".join(record_values)
        confirmed = messagebox.askyesno("Confirm", f"Delete this attendance record?\n{record_text}")
        if not confirmed:
            return

        try:
            with connect_db() as conn:
                conn.execute("DELETE FROM attendance WHERE id = ?", (record_id,))
        except sqlite3.Error:
            self.status_var.set("Cannot delete selected attendance record. Please try again.")
            return

        self.refresh_records()
        self.status_var.set("Deleted selected attendance record")

    def clear_attendance_records(self):
        confirmed = messagebox.askyesno("Confirm", "Clear all check-in/check-out records?\nPeople profiles and face photos will not be deleted.")
        if not confirmed:
            return

        with connect_db() as conn:
            conn.execute("DELETE FROM attendance")

        self.last_auto_record_times.clear()
        self.refresh_records()
        self.status_var.set("Attendance records cleared")

    def attendance_export_source_rows(self, date_text=None):
        date_filter = ""
        params = []
        if date_text:
            date_filter = "WHERE attendance.timestamp LIKE ?"
            params.append(f"{date_text}%")
        with connect_db() as conn:
            return conn.execute(
                f"""
                SELECT attendance.person_id, attendance.name, attendance.role, COALESCE(persons.class_name, ''), attendance.timestamp, attendance.event_type, COALESCE(attendance.snapshot_path, ''), COALESCE(attendance.source, 'system'), COALESCE(attendance.operator_name, ''), attendance.id
                FROM attendance
                LEFT JOIN persons ON persons.id = attendance.person_id
                {date_filter}
                ORDER BY attendance.timestamp DESC, attendance.id DESC
                """,
                params,
            ).fetchall()

    def schedule_daily_closeout(self):
        self.run_daily_closeout_if_due()
        self.root.after(60 * 1000, self.schedule_daily_closeout)

    def run_daily_closeout_if_due(self):
        current = datetime.now()
        today = current.strftime("%Y-%m-%d")
        if current.strftime("%H:%M") < DAILY_CLOSEOUT_TIME:
            return
        if self.daily_closeout_completed_date == today:
            return

        try:
            checkout_count, deleted_count, attendance_path, summary_path = self.closeout_day_and_export(today)
        except (OSError, sqlite3.Error, zipfile.BadZipFile, ET.ParseError, ValueError) as exc:
            self.status_var.set(f"Daily closeout failed: {exc}")
            return

        self.daily_closeout_completed_date = today
        self.last_auto_record_times.clear()
        self.refresh_records()
        self.status_var.set(
            f"Daily closeout complete: {checkout_count} checked out, {deleted_count} records cleared; files saved in {DAILY_EXPORT_DIR}"
        )

    def closeout_day_and_export(self, date_text):
        checkout_timestamp = f"{date_text} {DAILY_CLOSEOUT_TIME}:00"
        checkout_people = []
        with connect_db() as conn:
            rows = conn.execute(
                """
                SELECT persons.id, persons.name, persons.role
                FROM persons
                JOIN attendance ON attendance.person_id = persons.id
                WHERE attendance.timestamp LIKE ?
                  AND attendance.id = (
                      SELECT latest.id
                      FROM attendance AS latest
                      WHERE latest.person_id = persons.id
                        AND latest.timestamp LIKE ?
                      ORDER BY latest.timestamp DESC, latest.id DESC
                      LIMIT 1
                  )
                  AND attendance.event_type = 'checkin'
                ORDER BY persons.name COLLATE NOCASE
                """,
                (f"{date_text}%", f"{date_text}%"),
            ).fetchall()
            for person_id, name, role in rows:
                conn.execute(
                    "INSERT INTO attendance(person_id, name, role, event_type, timestamp) VALUES (?, ?, ?, 'checkout', ?)",
                    (person_id, name, role, checkout_timestamp),
                )
                checkout_people.append(person_id)

        rows = self.attendance_export_source_rows(date_text)
        attendance_path, summary_path = self.write_daily_export_files(date_text, rows)
        with connect_db() as conn:
            deleted_count = conn.execute(
                "DELETE FROM attendance WHERE timestamp LIKE ?",
                (f"{date_text}%",),
            ).rowcount
        return len(checkout_people), deleted_count, attendance_path, summary_path

    def write_daily_export_files(self, date_text, rows):
        export_rows = [
            [name, ROLE_LABELS.get(role, role), class_name, timestamp, EVENT_LABELS.get(event_type, event_type), attendance_operator_name(name, source, operator_name), snapshot_path]
            for _person_id, name, role, class_name, timestamp, event_type, snapshot_path, source, operator_name, *_extra in rows
        ]
        summary_rows = build_presence_summary_rows(rows)
        stamp = date_text.replace("-", "")
        attendance_path = DAILY_EXPORT_DIR / f"attendance_records_{stamp}.xlsx"
        summary_path = DAILY_EXPORT_DIR / f"view_15_min_summary_{stamp}.xlsx"
        write_xlsx_workbook(
            attendance_path,
            [
                {
                    "name": "Attendance Records",
                    "headers": ["Name", "Role", "Class", "Time", "Type", "By", "Snapshot Photo"],
                    "rows": export_rows,
                }
            ],
        )
        write_xlsx_workbook(
            summary_path,
            [
                {
                    "name": "Presence Summary",
                    "headers": ["Date", "Time", "Children Present", "Class Counts"],
                    "rows": summary_rows,
                }
            ],
        )
        return attendance_path, summary_path

    def show_presence_summary(self):
        selected_date = datetime.now().date()
        selected_month = selected_date.replace(day=1)
        window = Toplevel(self.root)
        window.title("Presence Summary")
        window.geometry("840x620")
        window.minsize(700, 460)

        container = Frame(window, padx=10, pady=10)
        container.pack(fill=BOTH, expand=True)

        header = Frame(container)
        header.pack(fill="x", pady=(0, 8))
        date_var = StringVar(value=f"Selected date: {selected_date.strftime('%Y-%m-%d')}")
        month_var = StringVar(value=selected_month.strftime("%B %Y"))
        Label(header, textvariable=date_var, fg="#1b5e20").pack(side=LEFT)
        Label(header, textvariable=month_var, fg="#555555").pack(side=RIGHT)

        calendar_box = ttk.LabelFrame(container, text="Calendar", padding=8)
        calendar_box.pack(fill="x", pady=(0, 10))
        month_row = Frame(calendar_box)
        month_row.pack(fill="x", pady=(0, 8))
        prev_month_button = Button(month_row, text="<")
        prev_month_button.pack(side=LEFT, padx=(0, 8))
        month_label = Label(month_row, textvariable=month_var, anchor="center")
        month_label.pack(side=LEFT, fill="x", expand=True)
        next_month_button = Button(month_row, text=">")
        next_month_button.pack(side=RIGHT, padx=(8, 0))
        days_frame = Frame(calendar_box)
        days_frame.pack(fill="x")

        columns = ("date", "time", "present", "classes")
        tree = ttk.Treeview(container, columns=columns, show="headings", height=12)
        tree.heading("date", text="Date")
        tree.heading("time", text="Time")
        tree.heading("present", text="Children Present")
        tree.heading("classes", text="Class Counts")
        tree.column("date", width=110, anchor="center")
        tree.column("time", width=90, anchor="center")
        tree.column("present", width=120, anchor="center")
        tree.column("classes", width=460, anchor="w")
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side=LEFT, fill=BOTH, expand=True)
        scrollbar.pack(side=RIGHT, fill="y")

        def load_rows(date_text):
            rows = self.attendance_export_source_rows(date_text)
            summary_rows = build_presence_summary_rows(rows)
            tree.delete(*tree.get_children())
            for row in summary_rows:
                tree.insert("", END, values=row)
            if summary_rows:
                self.status_var.set(f"Presence Summary loaded for {date_text}")
            else:
                self.status_var.set(f"No child attendance records for {date_text}")
            return len(summary_rows)

        def select_date(date_value):
            nonlocal selected_date, selected_month
            selected_date = date_value
            selected_month = selected_date.replace(day=1)
            date_var.set(f"Selected date: {selected_date.strftime('%Y-%m-%d')}")
            month_var.set(selected_month.strftime("%B %Y"))
            render_calendar()
            load_rows(selected_date.strftime("%Y-%m-%d"))

        def render_calendar():
            nonlocal selected_month
            for child in days_frame.winfo_children():
                child.destroy()
            month_var.set(selected_month.strftime("%B %Y"))
            for col, label in enumerate(("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")):
                Label(days_frame, text=label, width=6, anchor="center").grid(row=0, column=col, padx=1, pady=1)
            month_matrix = calendar.Calendar(firstweekday=0).monthdatescalendar(selected_month.year, selected_month.month)
            today_text = datetime.now().strftime("%Y-%m-%d")
            selected_text = selected_date.strftime("%Y-%m-%d")
            for row_index, week in enumerate(month_matrix, start=1):
                for col_index, day in enumerate(week):
                    date_text = day.strftime("%Y-%m-%d")
                    is_current_month = day.month == selected_month.month
                    color = "#f0e7fb" if date_text == selected_text else "#ffffff"
                    if date_text == today_text:
                        color = "#fff6d8"
                    if not is_current_month:
                        color = "#f3f3f3"
                    button = Button(
                        days_frame,
                        text=str(day.day),
                        width=5,
                        bg=color,
                        activebackground=color,
                        state="normal" if is_current_month else "disabled",
                        command=lambda value=day: select_date(value),
                    )
                    button.grid(row=row_index, column=col_index, padx=1, pady=1)

        def change_month(delta):
            nonlocal selected_month
            month = selected_month.month + delta
            year = selected_month.year
            if month < 1:
                month = 12
                year -= 1
            elif month > 12:
                month = 1
                year += 1
            selected_month = selected_month.replace(year=year, month=month)
            render_calendar()

        prev_month_button.configure(command=lambda: change_month(-1))
        next_month_button.configure(command=lambda: change_month(1))
        render_calendar()
        load_rows(selected_date.strftime("%Y-%m-%d"))

        window.transient(self.root)
        window.grab_set()
        window.focus_force()
    def open_acceo_detail_report_dialog(self):
        default_start = monday_for_date(datetime.now().date()).strftime("%Y-%m-%d")
        window = Toplevel(self.root)
        window.title("Generate 4-Week Fiche d'assiduité")
        window.geometry("460x520")
        window.resizable(False, False)

        container = Frame(window, padx=14, pady=14)
        container.pack(fill=BOTH, expand=True)

        Label(container, text="Start date (Monday, YYYY-MM-DD)").pack(anchor="w")
        start_var = StringVar(value=default_start)
        Entry(container, textvariable=start_var).pack(fill="x", pady=(4, 10))

        selected_month = datetime.now().date().replace(day=1)
        month_var = StringVar()
        range_var = StringVar()
        calendar_box = ttk.LabelFrame(container, text="Select a Date", padding=8)
        calendar_box.pack(fill="x", pady=(0, 10))
        month_row = Frame(calendar_box)
        month_row.pack(fill="x", pady=(0, 8))
        prev_month_button = Button(month_row, text="<")
        prev_month_button.pack(side=LEFT, padx=(0, 8))
        Label(month_row, textvariable=month_var, anchor="center").pack(side=LEFT, fill="x", expand=True)
        next_month_button = Button(month_row, text=">")
        next_month_button.pack(side=RIGHT, padx=(8, 0))
        days_frame = Frame(calendar_box)
        days_frame.pack(fill="x")
        Label(container, textvariable=range_var, fg="#1b5e20").pack(anchor="w", pady=(0, 8))

        def set_start_from_date(value):
            selected_date = datetime.strptime(value, "%Y-%m-%d").date()
            monday = monday_for_date(selected_date)
            start_var.set(monday.strftime("%Y-%m-%d"))
            range_var.set(f"Selected range: {monday.strftime('%Y-%m-%d')} to {(monday + timedelta(days=27)).strftime('%Y-%m-%d')}")
            render_calendar()

        def render_calendar():
            nonlocal selected_month
            for child in days_frame.winfo_children():
                child.destroy()
            month_var.set(selected_month.strftime("%B %Y"))
            selected_dates = set()
            try:
                selected_start_date = datetime.strptime(start_var.get().strip(), "%Y-%m-%d").date()
                selected_dates = {
                    (selected_start_date + timedelta(days=offset)).strftime("%Y-%m-%d")
                    for offset in range(28)
                }
            except ValueError:
                selected_dates = set()

            for col, label in enumerate(("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")):
                Label(days_frame, text=label, width=6, anchor="center").grid(row=0, column=col, padx=1, pady=1)
            today_text = datetime.now().strftime("%Y-%m-%d")
            month_matrix = calendar.Calendar(firstweekday=0).monthdatescalendar(selected_month.year, selected_month.month)
            for row_index, week in enumerate(month_matrix, start=1):
                for col_index, day in enumerate(week):
                    date_text = day.strftime("%Y-%m-%d")
                    is_current_month = day.month == selected_month.month
                    color = "#f0e7fb" if date_text in selected_dates else "#ffffff"
                    if date_text == today_text:
                        color = "#fff6d8"
                    if not is_current_month:
                        color = "#f3f3f3"
                    button = Button(
                        days_frame,
                        text=str(day.day),
                        width=5,
                        bg=color,
                        activebackground=color,
                        state="normal" if is_current_month else "disabled",
                        command=lambda date_value=date_text: set_start_from_date(date_value),
                    )
                    button.grid(row=row_index, column=col_index, padx=1, pady=1)

        def change_month(delta):
            nonlocal selected_month
            month = selected_month.month + delta
            year = selected_month.year
            if month < 1:
                month = 12
                year -= 1
            elif month > 12:
                month = 1
                year += 1
            selected_month = selected_month.replace(year=year, month=month)
            render_calendar()

        prev_month_button.configure(command=lambda: change_month(-1))
        next_month_button.configure(command=lambda: change_month(1))
        set_start_from_date(default_start)

        Label(container, text="Format").pack(anchor="w")
        format_var = StringVar(value="Detailed 4 week")
        ttk.Combobox(
            container,
            textvariable=format_var,
            values=("Detailed 4 week", "Summary 4 week"),
            state="readonly",
        ).pack(fill="x", pady=(4, 10))
        Label(container, text="The report covers this week and the next 3 weeks.", fg="#555555").pack(anchor="w")

        buttons = Frame(container)
        buttons.pack(fill="x", pady=(16, 0))
        Button(buttons, text="Cancel", command=window.destroy).pack(side=RIGHT)
        Button(
            buttons,
            text="Generate PDF",
            command=lambda: self.generate_acceo_detail_report_from_dialog(window, start_var.get(), format_var.get()),
        ).pack(side=RIGHT, padx=(0, 8))

        window.transient(self.root)
        window.grab_set()
        window.focus_force()

    def generate_acceo_detail_report_from_dialog(self, window, start_text, format_name):
        try:
            selected_date = datetime.strptime(start_text.strip(), "%Y-%m-%d").date()
        except ValueError:
            messagebox.showwarning("Invalid Date", "Please enter the date as YYYY-MM-DD.")
            return

        start_date = monday_for_date(selected_date)
        if start_date != selected_date:
            confirmed = messagebox.askyesno(
                "Use Monday",
                f"The selected date is not a Monday.\nGenerate from Monday {start_date.strftime('%Y-%m-%d')} instead?",
            )
            if not confirmed:
                return

        if format_name == "Summary 4 week":
            default_name = f"fiche_assiduite_4week_{start_date.strftime('%Y%m%d')}_{(start_date + timedelta(days=27)).strftime('%Y%m%d')}.pdf"
        else:
            default_name = f"fiche_assiduite_detaillee_{start_date.strftime('%Y%m%d')}_{(start_date + timedelta(days=27)).strftime('%Y%m%d')}.pdf"
        path = filedialog.asksaveasfilename(
            title="Save 4-Week Fiche d'assiduité",
            initialdir=str(FORM_DIR),
            initialfile=default_name,
            defaultextension=".pdf",
            filetypes=[("PDF Files", "*.pdf")],
        )
        if not path:
            return

        try:
            if format_name == "Summary 4 week":
                generate_acceo_summary_attendance_pdf(start_date, Path(path))
            else:
                generate_acceo_detail_attendance_pdf(start_date, Path(path))
        except (OSError, sqlite3.Error, RuntimeError, ValueError) as exc:
            messagebox.showerror("Generate Failed", str(exc))
            self.status_var.set(f"Fiche d'assiduité generation failed: {exc}")
            return

        window.destroy()
        self.status_var.set(f"Generated Fiche d'assiduité: {path}")
        messagebox.showinfo("Complete", f"Generated PDF:\n{path}")

    def open_closed_dates_dialog(self):
        window = Toplevel(self.root)
        window.title("Manage Closed Dates (F)")
        window.geometry("460x520")
        window.minsize(420, 460)

        container = Frame(window, padx=14, pady=14)
        container.pack(fill=BOTH, expand=True)

        selected_month = datetime.now().date().replace(day=1)
        month_var = StringVar()
        selected_var = StringVar(value="")

        calendar_box = ttk.LabelFrame(container, text="Calendar", padding=8)
        calendar_box.pack(fill="x")

        month_row = Frame(calendar_box)
        month_row.pack(fill="x", pady=(0, 8))
        prev_month_button = Button(month_row, text="<")
        prev_month_button.pack(side=LEFT, padx=(0, 8))
        month_label = Label(month_row, textvariable=month_var, anchor="center")
        month_label.pack(side=LEFT, fill="x", expand=True)
        next_month_button = Button(month_row, text=">")
        next_month_button.pack(side=RIGHT, padx=(8, 0))

        days_frame = Frame(calendar_box)
        days_frame.pack(fill="x")

        Label(container, textvariable=selected_var, fg="#1b5e20").pack(anchor="w", pady=(8, 4))

        listbox = Listbox(container, height=10)
        listbox.pack(fill=BOTH, expand=True)

        def refresh_list():
            listbox.delete(0, END)
            for value in load_closed_dates_setting():
                listbox.insert(END, value)

        def add_date(value):
            try:
                date_text = datetime.strptime(value, "%Y-%m-%d").strftime("%Y-%m-%d")
            except ValueError:
                messagebox.showwarning("Invalid Date", "Please select a valid date.")
                return
            closed_dates = load_closed_dates_setting()
            if date_text not in closed_dates:
                closed_dates.append(date_text)
                save_closed_dates_setting(closed_dates)
            refresh_list()
            render_calendar()
            selected_var.set(f"Selected closed date: {date_text}")
            self.status_var.set(f"Closed date saved: {date_text}")

        def render_calendar():
            nonlocal selected_month
            for child in days_frame.winfo_children():
                child.destroy()

            month_var.set(selected_month.strftime("%B %Y"))
            for col, label in enumerate(("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")):
                Label(days_frame, text=label, width=6, anchor="center").grid(row=0, column=col, padx=1, pady=1)

            closed_dates = set(load_closed_dates_setting())
            month_matrix = calendar.Calendar(firstweekday=0).monthdatescalendar(selected_month.year, selected_month.month)
            today_text = datetime.now().strftime("%Y-%m-%d")
            for row_index, week in enumerate(month_matrix, start=1):
                for col_index, day in enumerate(week):
                    date_text = day.strftime("%Y-%m-%d")
                    is_current_month = day.month == selected_month.month
                    color = "#f0e7fb" if date_text in closed_dates else "#ffffff"
                    if date_text == today_text:
                        color = "#fff6d8"
                    if not is_current_month:
                        color = "#f3f3f3"
                    button = Button(
                        days_frame,
                        text=str(day.day),
                        width=5,
                        bg=color,
                        activebackground=color,
                        state="normal" if is_current_month else "disabled",
                        command=lambda value=date_text: add_date(value),
                    )
                    button.grid(row=row_index, column=col_index, padx=1, pady=1)

        def change_month(delta):
            nonlocal selected_month
            month = selected_month.month + delta
            year = selected_month.year
            if month < 1:
                month = 12
                year -= 1
            elif month > 12:
                month = 1
                year += 1
            selected_month = selected_month.replace(year=year, month=month)
            render_calendar()

        def delete_selected():
            selection = listbox.curselection()
            if not selection:
                messagebox.showwarning("Notice", "Please select a closed date to delete.")
                return
            closed_dates = load_closed_dates_setting()
            selected_values = {listbox.get(index) for index in selection}
            save_closed_dates_setting([value for value in closed_dates if value not in selected_values])
            refresh_list()
            render_calendar()
            self.status_var.set("Closed date removed")

        prev_month_button.configure(command=lambda: change_month(-1))
        next_month_button.configure(command=lambda: change_month(1))

        button_row = Frame(container)
        button_row.pack(fill="x", pady=(10, 0))
        Button(button_row, text="Delete Selected", command=delete_selected).pack(side=LEFT, fill="x", expand=True, padx=(8, 0))
        Button(button_row, text="Close", command=window.destroy).pack(side=RIGHT, padx=(8, 0))

        refresh_list()
        render_calendar()
        window.transient(self.root)
        window.grab_set()
        window.focus_force()

    def export_excel(self):
        export_date = datetime.now().strftime("%Y-%m-%d")
        default_name = f"attendance_records_{export_date.replace('-', '')}.xlsx"
        path = filedialog.asksaveasfilename(
            title="Export Excel",
            initialfile=default_name,
            defaultextension=".xlsx",
            filetypes=[("Excel Files", "*.xlsx")],
        )
        if not path:
            return

        rows = self.attendance_export_source_rows(export_date)

        export_rows = [
            [name, ROLE_LABELS.get(role, role), class_name, timestamp, EVENT_LABELS.get(event_type, event_type), attendance_operator_name(name, source, operator_name), snapshot_path]
            for _person_id, name, role, class_name, timestamp, event_type, snapshot_path, source, operator_name, *_extra in rows
        ]
        summary_rows = build_presence_summary_rows(rows)
        write_xlsx_workbook(
            path,
            [
                {
                    "name": "Attendance Records",
                    "headers": ["Name", "Role", "Class", "Time", "Type", "By", "Snapshot Photo"],
                    "rows": export_rows,
                },
                {
                    "name": "Presence Summary",
                    "headers": ["Date", "Time", "Children Present", "Class Counts"],
                    "rows": summary_rows,
                },
            ],
        )
        self.status_var.set(f"Exported Excel: {path}")
        messagebox.showinfo("Complete", "Excel export successful")
        messagebox.showinfo("Complete", "Excel export successful")


    def close(self):
        if self.cap is not None:
            self.cap.release()
        stop_webapp()
        self.root.destroy()


def main():
    init_db()
    webapp_started = start_webapp()
    root = Tk()
    app = AttendanceApp(root)
    app.status_var.set(webapp_status_message(webapp_started))
    root.mainloop()


if __name__ == "__main__":
    main()

