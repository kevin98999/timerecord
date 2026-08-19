import calendar
import base64
import binascii
import csv
import hashlib
import hmac
import html
import json
import math
import mimetypes
import os
import io
import re
import secrets
import shutil
import smtplib
import sqlite3
import sys
import socket
import threading
import unicodedata
import xml.etree.ElementTree as ET
import zipfile
from PIL import Image, ImageOps, UnidentifiedImageError
from datetime import datetime, timedelta, date, timezone
from email.message import EmailMessage
from http import cookies
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path, PureWindowsPath
from urllib.parse import parse_qs, quote, unquote, urlparse
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

try:
    import cv2
except Exception:
    cv2 = None

try:
    import numpy as np
except Exception:
    np = None


def app_base_dir():
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_base_dir()
DATA_DIR = BASE_DIR / "data"
CHILDREN_DIR = BASE_DIR / "children"
DB_PATH = DATA_DIR / "attendance.db"
WORK_DB_PATH = DATA_DIR / "attendance_web.db"
QR_DIR = DATA_DIR / "child_qrcodes"
DAILY_EXPORT_DIR = DATA_DIR / "daily_exports"
FORM_DIR = DATA_DIR / "form"
USER_FILES_DIR = DATA_DIR / "user_folders"
MOBILE_FACE_SNAPSHOT_DIR = DATA_DIR / "mobile_face_snapshots"
PROJECT_LOGO_DIR = DATA_DIR / "project_logos"
FACE_DIR = DATA_DIR / "faces"
FACE_DETECTOR_CACHE = None
FACE_FEATURE_CACHE = {}
SETTINGS_PATH = DATA_DIR / "settings.json"
SECRET_PATH = DATA_DIR / "webapp_secret.txt"
SESSION_TTL_DAYS = 7
PASSWORD_ROTATION_DAYS = 30
CONNECTION_APPROVAL_HOURS = 5
CONNECTION_DEVICE_COOKIE = "connection_device"
FLASH_MESSAGES = {}
PUBLIC_CONTACT_LAST_SUBMISSION = {}
PUBLIC_CONTACT_LOCK = threading.Lock()
DEFAULT_PORT = 8000
DEFAULT_HOST = "0.0.0.0"
FACE_MATCH_THRESHOLD = 0.25
DESKTOP_SYNC_TOKEN_SETTING = "desktop_sync_token"
DESKTOP_SYNC_TOKEN_ENV = "TIMERECORD_DESKTOP_SYNC_TOKEN"
TEACHER_DAILY_CLOSEOUT_TIME = "23:50"
DEFAULT_PROJECT_NAME = "Projet principal"
PWA_MANIFEST_VERSION = "20260711-window-title"
SUPER_ADMIN_USERNAMES_ENV = "TIMERECORD_SUPER_ADMIN_USERS"
SUPER_ADMIN_DEFAULT_USERNAMES = {"boss"}
PROJECT_CONTEXT_COOKIE = "admin_project_id"
INVITED_LOGIN_COOKIE = "invited_login"
PUBLIC_URL_ENV = "TIMERECORD_PUBLIC_URL"
PRIVACY_CONTACT_ENV = "TIMERECORD_PRIVACY_CONTACT"
PRIVACY_EMAIL_ENV = "TIMERECORD_PRIVACY_EMAIL"
PRIVACY_POLICY_UPDATED = "2026-07-14"
EMAIL_PROVIDER_ENV = "TIMERECORD_EMAIL_PROVIDER"
SMTP_HOST_ENV = "TIMERECORD_SMTP_HOST"
SMTP_PORT_ENV = "TIMERECORD_SMTP_PORT"
SMTP_USERNAME_ENV = "TIMERECORD_SMTP_USERNAME"
SMTP_PASSWORD_ENV = "TIMERECORD_SMTP_PASSWORD"
SMTP_FROM_ENV = "TIMERECORD_SMTP_FROM"
SMTP_TLS_ENV = "TIMERECORD_SMTP_TLS"
SES_FROM_ENV = "TIMERECORD_SES_FROM"
SES_REGION_ENV = "TIMERECORD_SES_REGION"
LOGIN_PAGE_TEXT_DEFAULTS = {
    "brand_kicker_fr": "Gestion pour garderies",
    "brand_kicker_en": "Childcare management",
    "eyebrow_fr": "Pensé pour votre quotidien",
    "eyebrow_en": "Built for everyday childcare",
    "benefit_1_fr": "Suivez les arrivées, les départs et les présences en temps réel.",
    "benefit_1_en": "Track arrivals, departures and live attendance.",
    "benefit_2_fr": "Partagez les allergies et les besoins alimentaires pour faciliter le suivi.",
    "benefit_2_en": "Share allergy and dietary information for easier monitoring.",
    "benefit_3_fr": "Centralisez les fichiers et les messages pour tenir les parents informés.",
    "benefit_3_en": "Keep files and messages in one place so parents stay informed.",
    "benefit_4_fr": "Prévisualisez les présences à venir pour mieux planifier le personnel, les repas et les activités.",
    "benefit_4_en": "Preview upcoming attendance to plan staff, meals and activities.",
    "benefit_5_fr": "Générez les feuilles de temps du personnel et calculez automatiquement les heures rémunérées.",
    "benefit_5_en": "Generate staff timecards and automatically calculate paid hours.",
    "price_fr": "11,99 $ CA par mois",
    "price_en": "$11.99 CAD per month",
    "trial_fr": "Essai gratuit de 2 semaines",
    "trial_en": "Free for 2 weeks",
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


def access_urls(port):
    hosts = ["127.0.0.1", "localhost"] + local_ipv4_addresses()
    return [f"http://{host}:{port}" for host in dict.fromkeys(hosts)]

ROLE_LABELS = {
    "teacher": "éducatrice",
    "principal": "administratrice",
    "boss": "propriétaire",
    "cook": "cuisine",
    "children": "enfants",
}


def member_role_label(role):
    return {
        "teachers": "éducatrice",
        "teacher": "éducatrice",
        "principal": "administratrice",
        "boss": "propriétaire",
        "cook": "cuisine",
        "children": "enfants",
    }.get(role, ROLE_LABELS.get(role, role))

EVENT_LABELS = {
    "checkin": "Check In",
    "checkout": "Check Out",
}
OPERATION_LABELS = {
    "self": "Self",
    "system": "System",
}


def attendance_source_label(source):
    return OPERATION_LABELS["self"] if source in {"desktop", "mobile_face"} else OPERATION_LABELS["system"]


def user_display_name(user):
    if not user:
        return OPERATION_LABELS["system"]
    return (user["display_name"] or user["username"] or OPERATION_LABELS["system"]).strip()


EDIT_ROLES = {"teacher", "principal", "boss"}
MANAGE_USERS_ROLES = {"principal", "boss"}
MANAGE_ALL_USERS_ROLES = {"boss"}
MANAGE_CLOSED_DATES_ROLES = {"principal", "boss"}
VIEW_ALL_CLASSES_ROLES = {"principal", "boss", "cook"}
STAFF_MOBILE_ATTENDANCE_ROLES = {"teacher", "principal", "boss", "cook"}
try:
    APP_TIMEZONE = ZoneInfo("America/Toronto")
except ZoneInfoNotFoundError:
    APP_TIMEZONE = None


def toronto_utc_offset_hours(utc_now):
    march = date(utc_now.year, 3, 1)
    second_sunday_march = march + timedelta(days=(6 - march.weekday()) % 7 + 7)
    november = date(utc_now.year, 11, 1)
    first_sunday_november = november + timedelta(days=(6 - november.weekday()) % 7)
    dst_start_utc = datetime.combine(second_sunday_march, datetime.min.time()).replace(hour=7, tzinfo=timezone.utc)
    dst_end_utc = datetime.combine(first_sunday_november, datetime.min.time()).replace(hour=6, tzinfo=timezone.utc)
    return -4 if dst_start_utc <= utc_now < dst_end_utc else -5


def local_now():
    if APP_TIMEZONE is not None:
        return datetime.now(APP_TIMEZONE).replace(tzinfo=None)
    utc_now = datetime.now(timezone.utc)
    return (utc_now + timedelta(hours=toronto_utc_offset_hours(utc_now))).replace(tzinfo=None)


def now_text():
    return local_now().strftime("%Y-%m-%d %H:%M:%S")


def today_text():
    return local_now().strftime("%Y-%m-%d")


def ensure_dirs():
    DATA_DIR.mkdir(exist_ok=True)
    DAILY_EXPORT_DIR.mkdir(exist_ok=True)
    FORM_DIR.mkdir(exist_ok=True)
    USER_FILES_DIR.mkdir(exist_ok=True)
    MOBILE_FACE_SNAPSHOT_DIR.mkdir(exist_ok=True)
    PROJECT_LOGO_DIR.mkdir(exist_ok=True)


def connect_db():
    ensure_dirs()
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=OFF")
    conn.execute("PRAGMA synchronous=OFF")
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def load_settings():
    try:
        with SETTINGS_PATH.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
            return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def save_settings(settings):
    try:
        with SETTINGS_PATH.open("w", encoding="utf-8") as fh:
            json.dump(settings, fh, indent=2, ensure_ascii=False)
    except OSError:
        pass


def table_columns(conn, table_name):
    try:
        return {row["name"] for row in conn.execute(f"PRAGMA table_info({table_name})").fetchall()}
    except sqlite3.Error:
        return set()


def ensure_column(conn, table_name, column_name, ddl):
    if column_name not in table_columns(conn, table_name):
        conn.execute(f"ALTER TABLE {table_name} ADD COLUMN {column_name} {ddl}")


def ensure_default_project(conn):
    now = now_text()
    conn.execute(
        """
        INSERT OR IGNORE INTO projects(id, name, slug, status, created_at, updated_at)
        VALUES (1, ?, 'default', 'active', ?, ?)
        """,
        (DEFAULT_PROJECT_NAME, now, now),
    )
    return 1


def configured_super_admin_usernames():
    configured = os.environ.get(SUPER_ADMIN_USERNAMES_ENV, "").strip()
    values = {item.strip().casefold() for item in configured.split(",") if item.strip()}
    return values or set(SUPER_ADMIN_DEFAULT_USERNAMES)


def is_super_admin(user):
    if not user:
        return False
    username = str(user["username"] or "").strip().casefold()
    if username in configured_super_admin_usernames():
        return True
    try:
        home_project_id = int(user.get("_home_project_id", user["project_id"]) or 1)
    except AttributeError:
        try:
            home_project_id = int(user["project_id"] or 1)
        except Exception:
            home_project_id = 1
    except Exception:
        home_project_id = 1
    return user["role"] == "boss" and home_project_id == 1


def can_view_audit_logs(user):
    return bool(user and user["role"] == "boss" and user_project_id(user) == 1)


def user_project_id(user):
    try:
        value = int(user["project_id"] or 1)
    except Exception:
        value = 1
    return value if value > 0 else 1


def linked_person_project_id(conn, user):
    if not user or not user.get("person_id"):
        return None
    row = conn.execute("SELECT project_id FROM persons WHERE id = ?", (user["person_id"],)).fetchone()
    if not row:
        return None
    try:
        project_id = int(row["project_id"] or 0)
    except Exception:
        return None
    return project_id if project_id > 0 else None


def effective_project_id(conn, user):
    if not user:
        return 1
    if is_super_admin(user):
        return user_project_id(user)
    return user_project_id(user)


def visible_project_id(conn, user):
    return effective_project_id(conn, user)


def current_project(conn, user):
    project_id = effective_project_id(conn, user)
    row = conn.execute("SELECT * FROM projects WHERE id = ?", (project_id,)).fetchone()
    if row:
        return row
    return conn.execute("SELECT * FROM projects WHERE id = 1").fetchone()


def current_project_name(user):
    if not user:
        return "PITIT PAS SYSTEM"
    with connect_db() as conn:
        project = current_project(conn, user)
        return project["name"] if project else DEFAULT_PROJECT_NAME


def project_logo_url(project):
    if not project or "logo_path" not in project.keys() or not project["logo_path"]:
        return ""
    candidate = Path(project["logo_path"])
    if not candidate.is_absolute():
        candidate = BASE_DIR / candidate
    try:
        resolved = candidate.resolve()
        resolved.relative_to(PROJECT_LOGO_DIR.resolve())
    except (OSError, ValueError):
        return ""
    if not resolved.is_file():
        return ""
    return "/media/" + file_path_token(resolved)


def current_project_brand(user):
    if not user:
        return "PITIT PAS SYSTEM", ""
    with connect_db() as conn:
        project = current_project(conn, user)
        if not project:
            return DEFAULT_PROJECT_NAME, ""
        return project["name"], project_logo_url(project)


def save_project_logo(project_id, upload):
    content = upload.get("content") or b""
    if not content:
        raise ValueError("Veuillez choisir une image.")
    if len(content) > 5 * 1024 * 1024:
        raise ValueError("Le logo ne peut pas dépasser 5 Mo.")
    try:
        with Image.open(io.BytesIO(content)) as source:
            source.load()
            if source.width < 64 or source.height < 64:
                raise ValueError("Le logo doit mesurer au moins 64 × 64 pixels.")
            image = ImageOps.exif_transpose(source).convert("RGBA")
            image = ImageOps.fit(image, (512, 512), method=Image.Resampling.LANCZOS, centering=(0.5, 0.5))
            background = Image.new("RGBA", image.size, "white")
            background.alpha_composite(image)
            destination = PROJECT_LOGO_DIR / f"project_{int(project_id)}.png"
            background.convert("RGB").save(destination, "PNG", optimize=True)
    except (UnidentifiedImageError, OSError, Image.DecompressionBombError) as exc:
        raise ValueError("Le fichier sélectionné n'est pas une image valide.") from exc
    return str(destination.resolve())


def project_filter(conn, user, alias=None):
    column = f"{alias}.project_id" if alias else "project_id"
    return f"{column} = ?", [effective_project_id(conn, user)]


def configured_desktop_sync_token():
    env_value = os.environ.get(DESKTOP_SYNC_TOKEN_ENV, "").strip()
    if env_value:
        return env_value
    value = load_settings().get(DESKTOP_SYNC_TOKEN_SETTING, "")
    return value.strip() if isinstance(value, str) else ""


def load_closed_dates():
    values = load_settings().get("closed_dates", [])
    if not isinstance(values, list):
        return []
    cleaned = []
    for value in values:
        try:
            cleaned.append(datetime.strptime(str(value), "%Y-%m-%d").strftime("%Y-%m-%d"))
        except ValueError:
            continue
    return sorted(set(cleaned))


def save_closed_dates(values):
    valid = []
    for value in values:
        try:
            valid.append(datetime.strptime(str(value), "%Y-%m-%d").strftime("%Y-%m-%d"))
        except ValueError:
            continue
    settings = load_settings()
    settings["closed_dates"] = sorted(set(valid))
    save_settings(settings)


def load_secret():
    ensure_dirs()
    if SECRET_PATH.exists():
        try:
            return SECRET_PATH.read_text(encoding="utf-8").strip()
        except OSError:
            pass
    secret = secrets.token_hex(32)
    try:
        SECRET_PATH.write_text(secret, encoding="utf-8")
    except OSError:
        pass
    return secret


APP_SECRET = load_secret().encode("utf-8")


def password_fingerprint(password):
    return hmac.new(APP_SECRET, password.encode("utf-8"), hashlib.sha256).hexdigest()


def hash_password(password, salt=None):
    salt = salt or secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt.encode("utf-8"), 120_000)
    return f"pbkdf2_sha256$120000${salt}${digest.hex()}"


def verify_password(password, stored):
    try:
        scheme, iterations, salt, digest = stored.split("$", 3)
    except ValueError:
        return False
    if scheme != "pbkdf2_sha256":
        return False
    calc = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt.encode("utf-8"), int(iterations))
    return hmac.compare_digest(calc.hex(), digest)


def parse_password_record(stored):
    try:
        scheme, iterations, salt, digest = stored.split("$", 3)
    except ValueError:
        return None
    if scheme != "pbkdf2_sha256":
        return None
    return {
        "scheme": scheme,
        "iterations": int(iterations),
        "salt": salt,
        "digest": digest,
    }


def init_db():
    ensure_dirs()
    with connect_db() as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS projects (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                slug TEXT NOT NULL UNIQUE,
                status TEXT NOT NULL DEFAULT 'active',
                owner_user_id INTEGER,
                logo_path TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(owner_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS persons (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                role TEXT NOT NULL CHECK(role IN ('children', 'teachers')),
                photo_path TEXT NOT NULL,
                created_at TEXT NOT NULL,
                qr_token TEXT,
                class_name TEXT,
                project_id INTEGER NOT NULL DEFAULT 1
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
            CREATE TABLE IF NOT EXISTS web_users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                project_id INTEGER NOT NULL DEFAULT 1,
                username TEXT NOT NULL UNIQUE,
                display_name TEXT NOT NULL,
                role TEXT NOT NULL,
                person_id INTEGER,
                password_hash TEXT NOT NULL,
                password_fingerprint TEXT NOT NULL,
                password_changed_at TEXT NOT NULL,
                next_password_change_at TEXT NOT NULL,
                allowed_classes_json TEXT NOT NULL DEFAULT '[]',
                is_active INTEGER NOT NULL DEFAULT 1,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        default_project_id = ensure_default_project(conn)
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS password_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                password_fingerprint TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS audit_log (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                actor_user_id INTEGER,
                action TEXT NOT NULL,
                object_type TEXT NOT NULL,
                object_id TEXT,
                details_json TEXT NOT NULL DEFAULT '{}',
                ip_address TEXT,
                created_at TEXT NOT NULL,
                FOREIGN KEY(actor_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS deleted_user_archives (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL UNIQUE,
                username TEXT NOT NULL,
                display_name TEXT NOT NULL,
                role TEXT NOT NULL,
                person_id INTEGER,
                allowed_classes_json TEXT NOT NULL DEFAULT '[]',
                snapshot_json TEXT NOT NULL DEFAULT '{}',
                deleted_by_user_id INTEGER,
                deleted_by_username TEXT,
                deleted_by_display_name TEXT,
                deleted_by_role TEXT,
                deleted_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS sessions (
                token TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                expires_at TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS user_profiles (
                user_id INTEGER PRIMARY KEY,
                phones_json TEXT NOT NULL DEFAULT '[]',
                emails_json TEXT NOT NULL DEFAULT '[]',
                folder_path TEXT NOT NULL DEFAULT '',
                allergies TEXT NOT NULL DEFAULT '',
                notes TEXT NOT NULL DEFAULT '',
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS login_page_content (
                id INTEGER PRIMARY KEY CHECK(id = 1),
                content_json TEXT NOT NULL DEFAULT '{}',
                updated_by_user_id INTEGER,
                updated_at TEXT NOT NULL DEFAULT '',
                FOREIGN KEY(updated_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS child_calendar_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                day_text TEXT NOT NULL,
                event_type TEXT NOT NULL,
                note TEXT NOT NULL DEFAULT '',
                created_by_user_id INTEGER,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE,
                FOREIGN KEY(created_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS child_agenda_entries (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                child_user_id INTEGER NOT NULL,
                child_person_id INTEGER,
                class_name TEXT NOT NULL DEFAULT '',
                day_text TEXT NOT NULL,
                title TEXT NOT NULL DEFAULT '',
                body TEXT NOT NULL,
                author_user_id INTEGER,
                author_name TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                FOREIGN KEY(child_user_id) REFERENCES web_users(id) ON DELETE CASCADE,
                FOREIGN KEY(author_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS user_files (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                owner_user_id INTEGER NOT NULL,
                uploader_user_id INTEGER NOT NULL,
                original_name TEXT NOT NULL,
                stored_path TEXT NOT NULL,
                note TEXT NOT NULL DEFAULT '',
                uploaded_at TEXT NOT NULL,
                FOREIGN KEY(owner_user_id) REFERENCES web_users(id) ON DELETE CASCADE,
                FOREIGN KEY(uploader_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS internal_messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                sender_user_id INTEGER NOT NULL,
                recipient_user_id INTEGER NOT NULL,
                subject TEXT NOT NULL,
                body TEXT NOT NULL,
                external_sender_name TEXT NOT NULL DEFAULT '',
                external_sender_contact TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                read_at TEXT,
                FOREIGN KEY(sender_user_id) REFERENCES web_users(id) ON DELETE CASCADE,
                FOREIGN KEY(recipient_user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS teacher_daily_closeout (
                day_text TEXT PRIMARY KEY,
                checkout_count INTEGER NOT NULL DEFAULT 0,
                export_path TEXT NOT NULL DEFAULT '',
                completed_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS teacher_schedule (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                teacher_name TEXT NOT NULL,
                day_text TEXT NOT NULL,
                schedule_in TEXT NOT NULL,
                schedule_out TEXT NOT NULL,
                work_hours REAL NOT NULL DEFAULT 0,
                class_name TEXT NOT NULL DEFAULT '',
                source_filename TEXT NOT NULL DEFAULT '',
                uploaded_at TEXT NOT NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS mobile_invitations (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                project_id INTEGER NOT NULL DEFAULT 1,
                token TEXT NOT NULL UNIQUE,
                person_id INTEGER NOT NULL,
                role TEXT NOT NULL,
                email TEXT NOT NULL,
                invited_by_user_id INTEGER,
                expires_at TEXT NOT NULL,
                accepted_at TEXT,
                email_sent_at TEXT,
                email_error TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL,
                FOREIGN KEY(person_id) REFERENCES persons(id) ON DELETE CASCADE,
                FOREIGN KEY(invited_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS attendance_locations (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                project_id INTEGER NOT NULL DEFAULT 1,
                latitude REAL,
                longitude REAL,
                radius_meters INTEGER NOT NULL DEFAULT 100,
                updated_by_user_id INTEGER,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(updated_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS mobile_devices (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                device_id TEXT NOT NULL,
                device_name TEXT NOT NULL DEFAULT '',
                first_seen_at TEXT NOT NULL,
                last_seen_at TEXT NOT NULL,
                is_active INTEGER NOT NULL DEFAULT 1,
                UNIQUE(user_id, device_id),
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS user_connection_approvals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                ip_address TEXT NOT NULL,
                mac_address TEXT NOT NULL,
                device_name TEXT NOT NULL DEFAULT '',
                status TEXT NOT NULL DEFAULT 'pending',
                first_seen_at TEXT NOT NULL,
                last_seen_at TEXT NOT NULL,
                expires_at TEXT NOT NULL,
                approved_at TEXT,
                approved_by_user_id INTEGER,
                UNIQUE(user_id, ip_address, mac_address),
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE,
                FOREIGN KEY(approved_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS class_names (
                project_id INTEGER NOT NULL DEFAULT 1,
                name TEXT NOT NULL,
                created_at TEXT NOT NULL DEFAULT ''
                , PRIMARY KEY(project_id, name)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS hidden_class_names (
                project_id INTEGER NOT NULL DEFAULT 1
                , name TEXT NOT NULL
                , PRIMARY KEY(project_id, name)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS user_ui_preferences (
                user_id INTEGER PRIMARY KEY,
                last_class_name TEXT NOT NULL DEFAULT 'all',
                updated_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        ensure_column(conn, "projects", "logo_path", "TEXT NOT NULL DEFAULT ''")
        columns = {row["name"] for row in conn.execute("PRAGMA table_info(web_users)").fetchall()}
        # Older SQLite files may not have these columns.
        for column_sql in [
            ("project_id", "INTEGER NOT NULL DEFAULT 1"),
            ("allowed_classes_json", "TEXT NOT NULL DEFAULT '[]'"),
            ("is_active", "INTEGER NOT NULL DEFAULT 1"),
            ("next_password_change_at", "TEXT"),
            ("password_fingerprint", "TEXT"),
        ]:
            name, ddl = column_sql
            if name not in columns:
                conn.execute(f"ALTER TABLE web_users ADD COLUMN {name} {ddl}")
        invitation_columns = {row["name"] for row in conn.execute("PRAGMA table_info(mobile_invitations)").fetchall()}
        for name, ddl in [
            ("project_id", "INTEGER NOT NULL DEFAULT 1"),
            ("email_sent_at", "TEXT"),
            ("email_error", "TEXT NOT NULL DEFAULT ''"),
        ]:
            if name not in invitation_columns:
                conn.execute(f"ALTER TABLE mobile_invitations ADD COLUMN {name} {ddl}")
        message_columns = {row["name"] for row in conn.execute("PRAGMA table_info(internal_messages)").fetchall()}
        for name, ddl in [
            ("external_sender_name", "TEXT NOT NULL DEFAULT ''"),
            ("external_sender_contact", "TEXT NOT NULL DEFAULT ''"),
        ]:
            if name not in message_columns:
                conn.execute(f"ALTER TABLE internal_messages ADD COLUMN {name} {ddl}")
        for table_name in ["persons", "attendance_locations", "class_names", "hidden_class_names", "teacher_schedule"]:
            if table_columns(conn, table_name):
                ensure_column(conn, table_name, "project_id", "INTEGER NOT NULL DEFAULT 1")
        if table_columns(conn, "class_names"):
            ensure_column(conn, "class_names", "created_at", "TEXT NOT NULL DEFAULT ''")
        if table_columns(conn, "deleted_user_archives"):
            ensure_column(conn, "deleted_user_archives", "project_id", "INTEGER NOT NULL DEFAULT 1")
        conn.execute("UPDATE web_users SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        if table_columns(conn, "persons"):
            conn.execute("UPDATE persons SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        conn.execute("UPDATE mobile_invitations SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        if table_columns(conn, "attendance_locations"):
            conn.execute("UPDATE attendance_locations SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        if table_columns(conn, "class_names"):
            conn.execute("UPDATE class_names SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        if table_columns(conn, "hidden_class_names"):
            conn.execute("UPDATE hidden_class_names SET project_id = ? WHERE project_id IS NULL OR project_id <= 0", (default_project_id,))
        repair_project_scoped_name_tables(conn)
        if table_columns(conn, "persons") and table_columns(conn, "web_users"):
            conn.execute(
                """
                UPDATE web_users
                SET project_id = (
                    SELECT persons.project_id
                    FROM persons
                    WHERE persons.id = web_users.person_id
                )
                WHERE person_id IS NOT NULL
                  AND EXISTS (
                      SELECT 1
                      FROM persons
                      WHERE persons.id = web_users.person_id
                        AND persons.project_id > 0
                        AND persons.project_id <> web_users.project_id
                  )
                """
            )
        if table_columns(conn, "persons") and table_columns(conn, "mobile_invitations"):
            conn.execute(
                """
                UPDATE mobile_invitations
                SET project_id = (
                    SELECT persons.project_id
                    FROM persons
                    WHERE persons.id = mobile_invitations.person_id
                )
                WHERE person_id IS NOT NULL
                  AND EXISTS (
                      SELECT 1
                      FROM persons
                      WHERE persons.id = mobile_invitations.person_id
                        AND persons.project_id > 0
                        AND persons.project_id <> mobile_invitations.project_id
                  )
                """
            )
        preference_columns = {row["name"] for row in conn.execute("PRAGMA table_info(user_ui_preferences)").fetchall()}
        if preference_columns and "last_class_name" not in preference_columns:
            conn.execute("ALTER TABLE user_ui_preferences ADD COLUMN last_class_name TEXT NOT NULL DEFAULT 'all'")
        if preference_columns and "teacher_attendance_start" not in preference_columns:
            conn.execute("ALTER TABLE user_ui_preferences ADD COLUMN teacher_attendance_start TEXT NOT NULL DEFAULT ''")
        if preference_columns and "teacher_attendance_end" not in preference_columns:
            conn.execute("ALTER TABLE user_ui_preferences ADD COLUMN teacher_attendance_end TEXT NOT NULL DEFAULT ''")
        profile_columns = {row["name"] for row in conn.execute("PRAGMA table_info(user_profiles)").fetchall()}
        for name, ddl in [
            ("allergies", "TEXT NOT NULL DEFAULT ''"),
        ]:
            if name not in profile_columns:
                conn.execute(f"ALTER TABLE user_profiles ADD COLUMN {name} {ddl}")
        repair_attendance_locations_table(conn)
        seed_default_users(conn)
        default_owner = conn.execute(
            "SELECT id FROM web_users WHERE role = 'boss' AND project_id = ? AND is_active = 1 ORDER BY id LIMIT 1",
            (default_project_id,),
        ).fetchone()
        if default_owner:
            conn.execute("UPDATE projects SET owner_user_id = ?, updated_at = ? WHERE id = ?", (default_owner["id"], now_text(), default_project_id))
        repair_attendance_person_links(conn)
        repair_mobile_invitations_table(conn)


def repair_attendance_locations_table(conn):
    row = conn.execute(
        "SELECT sql FROM sqlite_master WHERE type = 'table' AND name = 'attendance_locations'"
    ).fetchone()
    create_sql = (row["sql"] or "") if row else ""
    if "CHECK(id = 1)" not in create_sql and "CHECK (id = 1)" not in create_sql:
        return
    conn.execute("PRAGMA foreign_keys = OFF")
    try:
        conn.execute(
            """
            CREATE TABLE attendance_locations_new (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                latitude REAL,
                longitude REAL,
                radius_meters INTEGER NOT NULL DEFAULT 100,
                updated_by_user_id INTEGER,
                updated_at TEXT NOT NULL,
                FOREIGN KEY(updated_by_user_id) REFERENCES web_users(id) ON DELETE SET NULL
            )
            """
        )
        conn.execute(
            """
            INSERT INTO attendance_locations_new(id, latitude, longitude, radius_meters, updated_by_user_id, updated_at)
            SELECT id, latitude, longitude, radius_meters, updated_by_user_id, updated_at
            FROM attendance_locations
            WHERE latitude IS NOT NULL AND longitude IS NOT NULL
            """
        )
        conn.execute("DROP TABLE attendance_locations")
        conn.execute("ALTER TABLE attendance_locations_new RENAME TO attendance_locations")
    finally:
        conn.execute("PRAGMA foreign_keys = ON")


def repair_attendance_person_links(conn):
    table_names = {
        row["name"]
        for row in conn.execute("SELECT name FROM sqlite_master WHERE type = 'table' AND name IN ('persons', 'attendance')").fetchall()
    }
    if {"persons", "attendance"} - table_names:
        return
    fk_targets = {
        row["table"]
        for row in conn.execute("PRAGMA foreign_key_list(attendance)").fetchall()
    }
    if fk_targets and fk_targets != {"persons"}:
        rebuild_attendance_table(conn)
    # Keep startup resilient: if historical data contains broken links, do not
    # block the whole service from starting.
    try:
        conn.execute("PRAGMA foreign_keys = OFF")
        conn.execute(
            """
            UPDATE attendance
            SET person_id = (
                SELECT persons.id
                FROM persons
                WHERE lower(persons.name) = lower(attendance.name)
                  AND persons.role = attendance.role
                ORDER BY persons.id
                LIMIT 1
            )
            WHERE (
                NOT EXISTS (
                    SELECT 1
                    FROM persons AS current_person
                    WHERE current_person.id = attendance.person_id
                )
                OR EXISTS (
                    SELECT 1
                    FROM persons AS current_person
                    WHERE current_person.id = attendance.person_id
                      AND (
                        lower(current_person.name) <> lower(attendance.name)
                        OR current_person.role <> attendance.role
                      )
                )
            )
              AND (
                SELECT COUNT(*)
                FROM persons AS matching_person
                WHERE lower(matching_person.name) = lower(attendance.name)
                  AND matching_person.role = attendance.role
              ) = 1
            """
        )
    except sqlite3.IntegrityError:
        return
    finally:
        try:
            conn.execute("PRAGMA foreign_keys = ON")
        except sqlite3.Error:
            pass


def rebuild_attendance_table(conn):
    columns = conn.execute("PRAGMA table_info(attendance)").fetchall()
    if not columns:
        return
    col_names = [row["name"] for row in columns]
    conn.execute("PRAGMA foreign_keys = OFF")
    conn.execute("ALTER TABLE attendance RENAME TO attendance_old")
    column_defs = []
    for row in columns:
        name = row["name"]
        col_type = (row["type"] or "").strip()
        parts = [name]
        if name == "id":
            parts.append("INTEGER PRIMARY KEY AUTOINCREMENT")
        else:
            if col_type:
                parts.append(col_type)
            if row["notnull"]:
                parts.append("NOT NULL")
            if row["dflt_value"] is not None:
                parts.append(f"DEFAULT {row['dflt_value']}")
            if name == "person_id":
                parts.append("REFERENCES persons(id) ON DELETE CASCADE")
        column_defs.append(" ".join(parts))
    conn.execute(f"CREATE TABLE attendance ({', '.join(column_defs)})")
    copy_columns = ", ".join(col_names)
    conn.execute(f"INSERT INTO attendance ({copy_columns}) SELECT {copy_columns} FROM attendance_old")
    conn.execute("DROP TABLE attendance_old")


def repair_mobile_invitations_table(conn):
    table_names = {
        row["name"]
        for row in conn.execute("SELECT name FROM sqlite_master WHERE type = 'table' AND name = 'mobile_invitations'").fetchall()
    }
    if not table_names:
        return
    fk_targets = {
        row["table"]
        for row in conn.execute("PRAGMA foreign_key_list(mobile_invitations)").fetchall()
    }
    if fk_targets and fk_targets != {"persons", "web_users"}:
        columns = conn.execute("PRAGMA table_info(mobile_invitations)").fetchall()
        if not columns:
            return
        col_names = [row["name"] for row in columns]
        conn.execute("PRAGMA foreign_keys = OFF")
        conn.execute("ALTER TABLE mobile_invitations RENAME TO mobile_invitations_old")
        column_defs = []
        for row in columns:
            name = row["name"]
            col_type = (row["type"] or "").strip()
            parts = [name]
            if name == "id":
                parts.append("INTEGER PRIMARY KEY AUTOINCREMENT")
            else:
                if col_type:
                    parts.append(col_type)
                if row["notnull"]:
                    parts.append("NOT NULL")
                if row["dflt_value"] is not None:
                    parts.append(f"DEFAULT {row['dflt_value']}")
                if name == "person_id":
                    parts.append("REFERENCES persons(id) ON DELETE CASCADE")
                if name == "invited_by_user_id":
                    parts.append("REFERENCES web_users(id) ON DELETE SET NULL")
            column_defs.append(" ".join(parts))
        conn.execute(f"CREATE TABLE mobile_invitations ({', '.join(column_defs)})")
        copy_columns = ", ".join(col_names)
        conn.execute(f"INSERT INTO mobile_invitations ({copy_columns}) SELECT {copy_columns} FROM mobile_invitations_old")
        conn.execute("DROP TABLE mobile_invitations_old")


def repair_project_scoped_name_tables(conn):
    for table_name, has_created_at in (("class_names", True), ("hidden_class_names", False)):
        row = conn.execute("SELECT sql FROM sqlite_master WHERE type = 'table' AND name = ?", (table_name,)).fetchone()
        if not row or "name TEXT PRIMARY KEY" not in (row["sql"] or ""):
            continue
        old_name = f"{table_name}_old"
        conn.execute(f"ALTER TABLE {table_name} RENAME TO {old_name}")
        if has_created_at:
            conn.execute(
                f"""
                CREATE TABLE {table_name} (
                    project_id INTEGER NOT NULL DEFAULT 1,
                    name TEXT NOT NULL,
                    created_at TEXT NOT NULL DEFAULT '',
                    PRIMARY KEY(project_id, name)
                )
                """
            )
            conn.execute(
                f"""
                INSERT OR IGNORE INTO {table_name}(project_id, name, created_at)
                SELECT COALESCE(NULLIF(project_id, 0), 1), name, COALESCE(NULLIF(created_at, ''), ?)
                FROM {old_name}
                WHERE name IS NOT NULL AND trim(name) <> ''
                """,
                (now_text(),),
            )
        else:
            conn.execute(
                f"""
                CREATE TABLE {table_name} (
                    project_id INTEGER NOT NULL DEFAULT 1,
                    name TEXT NOT NULL,
                    PRIMARY KEY(project_id, name)
                )
                """
            )
            conn.execute(
                f"""
                INSERT OR IGNORE INTO {table_name}(project_id, name)
                SELECT COALESCE(NULLIF(project_id, 0), 1), name
                FROM {old_name}
                WHERE name IS NOT NULL AND trim(name) <> ''
                """
            )
        conn.execute(f"DROP TABLE {old_name}")


def seed_default_users(conn):
    count = conn.execute("SELECT COUNT(*) FROM web_users").fetchone()[0]
    if count:
        return

    class_names = [row["name"] for row in conn.execute("SELECT name FROM class_names ORDER BY rowid").fetchall()]
    if not class_names:
        class_names = ["Class 1", "Class 2"]

    teacher_rows = conn.execute("SELECT id, name FROM persons WHERE role = 'teachers' ORDER BY id").fetchall()
    defaults = [
        {
            "username": "boss",
            "display_name": "Boss",
            "role": "boss",
            "person_id": None,
            "password": "Boss123!",
            "classes": class_names,
        },
        {
            "username": "principal",
            "display_name": "Principal",
            "role": "principal",
            "person_id": None,
            "password": "Principal123!",
            "classes": class_names,
        },
        {
            "username": "cook",
            "display_name": "Cook",
            "role": "cook",
            "person_id": None,
            "password": "Cook123!",
            "classes": [],
        },
    ]
    for row in teacher_rows:
        username = slugify(row["name"]) or f"teacher-{row['id']}"
        defaults.append(
            {
                "username": username,
                "display_name": row["name"],
                "role": "teacher",
                "person_id": row["id"],
                "password": "Teacher123!",
                "classes": class_names,
            }
        )

    for user in defaults:
        create_user(
            conn,
            username=user["username"],
            display_name=user["display_name"],
            role=user["role"],
            password=user["password"],
            person_id=user["person_id"],
            allowed_classes=user["classes"],
        )


def slugify(value):
    value = value.strip().lower()
    out = []
    for char in value:
        if char.isalnum():
            out.append(char)
        elif char in {" ", "-", "_"}:
            out.append("-")
    slug = "".join(out)
    while "--" in slug:
        slug = slug.replace("--", "-")
    return slug.strip("-")


def allowed_classes_value(classes):
    return json.dumps(sorted(set(classes)), ensure_ascii=False)


def create_user(conn, username, display_name, role, password, person_id=None, allowed_classes=None, project_id=1):
    fingerprint = password_fingerprint(password)
    now = now_text()
    next_change = (datetime.now() + timedelta(days=PASSWORD_ROTATION_DAYS)).strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        """
        INSERT INTO web_users(
            project_id, username, display_name, role, person_id, password_hash, password_fingerprint,
            password_changed_at, next_password_change_at, allowed_classes_json,
            is_active, created_at, updated_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?)
        """,
        (
            int(project_id or 1),
            username,
            display_name,
            role,
            person_id,
            hash_password(password),
            fingerprint,
            now,
            next_change,
            allowed_classes_value(allowed_classes or []),
            now,
            now,
        ),
    )
    user_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    conn.execute(
        "INSERT INTO password_history(user_id, password_fingerprint, created_at) VALUES (?, ?, ?)",
        (user_id, fingerprint, now),
    )
    return user_id


def update_user_password(conn, user_id, new_password):
    fingerprint = password_fingerprint(new_password)
    row = conn.execute("SELECT password_fingerprint FROM web_users WHERE id = ?", (user_id,)).fetchone()
    if not row:
        raise ValueError("User not found")
    history = conn.execute(
        "SELECT 1 FROM password_history WHERE user_id = ? AND password_fingerprint = ?",
        (user_id, fingerprint),
    ).fetchone()
    if history:
        raise ValueError("Password cannot repeat a previous password")
    now = now_text()
    next_change = (datetime.now() + timedelta(days=PASSWORD_ROTATION_DAYS)).strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        """
        UPDATE web_users
        SET password_hash = ?, password_fingerprint = ?, password_changed_at = ?, next_password_change_at = ?, updated_at = ?
        WHERE id = ?
        """,
        (hash_password(new_password), fingerprint, now, next_change, now, user_id),
    )
    conn.execute(
        "INSERT INTO password_history(user_id, password_fingerprint, created_at) VALUES (?, ?, ?)",
        (user_id, fingerprint, now),
    )


def archive_deleted_user(conn, deleted_user, deleted_by_user):
    snapshot = {key: deleted_user[key] for key in deleted_user.keys()}
    now = now_text()
    conn.execute("DELETE FROM deleted_user_archives WHERE user_id = ?", (deleted_user["id"],))
    conn.execute(
        """
        INSERT INTO deleted_user_archives(
            user_id, username, display_name, role, person_id, allowed_classes_json,
            snapshot_json, deleted_by_user_id, deleted_by_username, deleted_by_display_name,
            deleted_by_role, deleted_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            deleted_user["id"],
            deleted_user["username"],
            deleted_user["display_name"],
            deleted_user["role"],
            deleted_user["person_id"],
            deleted_user["allowed_classes_json"],
            json.dumps(snapshot, ensure_ascii=False),
            deleted_by_user["id"] if deleted_by_user else None,
            deleted_by_user["username"] if deleted_by_user else None,
            deleted_by_user["display_name"] if deleted_by_user else None,
            deleted_by_user["role"] if deleted_by_user else None,
            now,
        ),
    )


def delete_user_file_rows(conn, user_id):
    rows = conn.execute(
        "SELECT stored_path FROM user_files WHERE owner_user_id = ? OR uploader_user_id = ?",
        (user_id, user_id),
    ).fetchall()
    for row in rows:
        stored_path = (row["stored_path"] or "").strip()
        if not stored_path:
            continue
        try:
            path = Path(stored_path)
            if not path.is_absolute():
                path = BASE_DIR / path
            resolved = path.resolve()
            allowed_root = USER_FILES_DIR.resolve()
            if allowed_root in resolved.parents or resolved == allowed_root:
                resolved.unlink(missing_ok=True)
        except OSError:
            pass
    conn.execute("DELETE FROM user_files WHERE owner_user_id = ? OR uploader_user_id = ?", (user_id, user_id))


def permanently_delete_user_account(conn, target_user_id):
    delete_user_file_rows(conn, target_user_id)
    conn.execute("DELETE FROM sessions WHERE user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM password_history WHERE user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM user_profiles WHERE user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM child_calendar_events WHERE user_id = ?", (target_user_id,))
    conn.execute("UPDATE child_calendar_events SET created_by_user_id = NULL WHERE created_by_user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM child_agenda_entries WHERE child_user_id = ?", (target_user_id,))
    conn.execute("UPDATE child_agenda_entries SET author_user_id = NULL WHERE author_user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM internal_messages WHERE sender_user_id = ? OR recipient_user_id = ?", (target_user_id, target_user_id))
    conn.execute("DELETE FROM mobile_devices WHERE user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM user_connection_approvals WHERE user_id = ?", (target_user_id,))
    conn.execute("UPDATE user_connection_approvals SET approved_by_user_id = NULL WHERE approved_by_user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM user_ui_preferences WHERE user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM deleted_user_archives WHERE user_id = ?", (target_user_id,))
    conn.execute("UPDATE mobile_invitations SET invited_by_user_id = NULL WHERE invited_by_user_id = ?", (target_user_id,))
    conn.execute("UPDATE attendance_locations SET updated_by_user_id = NULL WHERE updated_by_user_id = ?", (target_user_id,))
    conn.execute("UPDATE audit_log SET actor_user_id = NULL WHERE actor_user_id = ?", (target_user_id,))
    conn.execute("DELETE FROM web_users WHERE id = ?", (target_user_id,))


def permanently_delete_group(conn, group_name):
    group_name = (group_name or "").strip()
    if not group_name:
        return 0
    row = conn.execute(
        "SELECT COUNT(*) AS count FROM persons WHERE role = 'children' AND lower(class_name) = lower(?)",
        (group_name,),
    ).fetchone()
    affected = int(row["count"] or 0)
    conn.execute(
        "UPDATE persons SET class_name = '' WHERE role = 'children' AND lower(class_name) = lower(?)",
        (group_name,),
    )
    for account in conn.execute("SELECT id, allowed_classes_json FROM web_users").fetchall():
        classes = safe_json_list(account["allowed_classes_json"])
        filtered = [value for value in classes if str(value).strip().lower() != group_name.lower()]
        if filtered != classes:
            conn.execute(
                "UPDATE web_users SET allowed_classes_json = ?, updated_at = ? WHERE id = ?",
                (allowed_classes_value(filtered), now_text(), account["id"]),
            )
    conn.execute("UPDATE user_ui_preferences SET last_class_name = 'all', updated_at = ? WHERE lower(last_class_name) = lower(?)", (now_text(), group_name))
    conn.execute("DELETE FROM class_names WHERE lower(name) = lower(?)", (group_name,))
    conn.execute("DELETE FROM hidden_class_names WHERE lower(name) = lower(?)", (group_name,))
    return affected


def audit(conn, actor_user_id, action, object_type, object_id=None, details=None, ip_address=None):
    conn.execute(
        """
        INSERT INTO audit_log(actor_user_id, action, object_type, object_id, details_json, ip_address, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            actor_user_id,
            action,
            object_type,
            None if object_id is None else str(object_id),
            json.dumps(details or {}, ensure_ascii=False),
            ip_address,
            now_text(),
        ),
    )


def request_ip_address(handler):
    forwarded = handler.headers.get("X-Forwarded-For", "").split(",", 1)[0].strip()
    if forwarded:
        return forwarded
    real_ip = handler.headers.get("X-Real-IP", "").strip()
    if real_ip:
        return real_ip
    return handler.client_address[0] if handler.client_address else ""


def request_device_name(handler):
    user_agent = handler.headers.get("User-Agent", "").strip()
    if not user_agent:
        return "Unknown device"
    if "Edg/" in user_agent:
        browser = "Edge"
    elif "Chrome/" in user_agent and "Chromium/" not in user_agent:
        browser = "Chrome"
    elif "Firefox/" in user_agent:
        browser = "Firefox"
    elif "Safari/" in user_agent and "Chrome/" not in user_agent:
        browser = "Safari"
    else:
        browser = "Browser"

    if "Windows" in user_agent:
        platform = "Windows"
    elif "iPhone" in user_agent:
        platform = "iPhone"
    elif "iPad" in user_agent:
        platform = "iPad"
    elif "Android" in user_agent:
        platform = "Android"
    elif "Macintosh" in user_agent or "Mac OS X" in user_agent:
        platform = "Mac"
    elif "Linux" in user_agent:
        platform = "Linux"
    else:
        platform = "Device"
    return f"{platform} {browser}"


def audit_request(handler, conn, actor_user_id, action, object_type, object_id=None, details=None):
    detail_values = dict(details or {})
    detail_values.setdefault("device_name", request_device_name(handler))
    audit(
        conn,
        actor_user_id,
        action,
        object_type,
        object_id=object_id,
        details=detail_values,
        ip_address=request_ip_address(handler),
    )


def login_user(conn, username, password):
    user = conn.execute(
        "SELECT * FROM web_users WHERE lower(username) = lower(?) AND is_active = 1",
        (username.strip(),),
    ).fetchone()
    if not user:
        return None
    if not verify_password(password, user["password_hash"]):
        return None
    return user


def request_connection_device_key(handler, supplied_device_id=""):
    supplied = str(supplied_device_id or "").strip()
    if 16 <= len(supplied) <= 160:
        return supplied, False
    cookie = parse_cookie(handler.headers.get("Cookie"))
    morsel = cookie.get(CONNECTION_DEVICE_COOKIE)
    if morsel and 16 <= len(morsel.value) <= 160:
        return morsel.value, False
    return secrets.token_urlsafe(24), True


def check_login_connection_approval(conn, handler, user, supplied_device_id="", device_name=""):
    device_key, set_cookie = request_connection_device_key(handler, supplied_device_id)
    ip_address = request_ip_address(handler)
    label = (device_name or request_device_name(handler) or "").strip()[:160]
    current = local_now()
    current_text = current.strftime("%Y-%m-%d %H:%M:%S")
    expires_at = (current + timedelta(hours=CONNECTION_APPROVAL_HOURS)).strftime("%Y-%m-%d %H:%M:%S")
    row = conn.execute(
        """
        SELECT *
        FROM user_connection_approvals
        WHERE user_id = ? AND ip_address = ? AND mac_address = ?
        """,
        (user["id"], ip_address, device_key),
    ).fetchone()
    if user["role"] == "boss":
        if not row:
            conn.execute(
                """
                INSERT INTO user_connection_approvals(
                    user_id, ip_address, mac_address, device_name, status,
                    first_seen_at, last_seen_at, expires_at, approved_at, approved_by_user_id
                )
                VALUES (?, ?, ?, ?, 'approved', ?, ?, ?, ?, ?)
                """,
                (user["id"], ip_address, device_key, label, current_text, current_text, expires_at, current_text, user["id"]),
            )
        else:
            conn.execute(
                """
                UPDATE user_connection_approvals
                SET status = 'approved',
                    last_seen_at = ?,
                    expires_at = ?,
                    approved_at = COALESCE(approved_at, ?),
                    approved_by_user_id = COALESCE(approved_by_user_id, ?),
                    device_name = COALESCE(NULLIF(?, ''), device_name)
                WHERE id = ?
                """,
                (current_text, expires_at, current_text, user["id"], label, row["id"]),
            )
        return {"ok": True, "device_key": device_key, "set_cookie": set_cookie}
    if not row:
        conn.execute(
            """
            INSERT INTO user_connection_approvals(user_id, ip_address, mac_address, device_name, status, first_seen_at, last_seen_at, expires_at)
            VALUES (?, ?, ?, ?, 'pending', ?, ?, ?)
            """,
            (user["id"], ip_address, device_key, label, current_text, current_text, expires_at),
        )
        return {"ok": True, "device_key": device_key, "set_cookie": set_cookie, "pending": True}
    if row["status"] == "approved":
        conn.execute(
            "UPDATE user_connection_approvals SET last_seen_at = ?, device_name = COALESCE(NULLIF(?, ''), device_name) WHERE id = ?",
            (current_text, label, row["id"]),
        )
        return {"ok": True, "device_key": device_key, "set_cookie": set_cookie}
    if row["status"] == "rejected" or current_text > row["expires_at"]:
        conn.execute(
            "UPDATE user_connection_approvals SET status = 'rejected', last_seen_at = ? WHERE id = ?",
            (current_text, row["id"]),
        )
        return {
            "ok": False,
            "device_key": device_key,
            "set_cookie": set_cookie,
            "error": "This connection was not approved within 5 hours. Ask the boss to approve this device/IP.",
        }
    conn.execute(
        "UPDATE user_connection_approvals SET last_seen_at = ?, device_name = COALESCE(NULLIF(?, ''), device_name) WHERE id = ?",
        (current_text, label, row["id"]),
    )
    return {"ok": True, "device_key": device_key, "set_cookie": set_cookie, "pending": True}


def get_user_by_id(conn, user_id):
    return conn.execute("SELECT * FROM web_users WHERE id = ?", (user_id,)).fetchone()


def get_children(conn, user, class_name=None):
    project_id = effective_project_id(conn, user)
    if user["role"] == "teacher" and user["person_id"]:
        linked_person = conn.execute(
            "SELECT id FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
            (user["person_id"], project_id),
        ).fetchone()
        if not linked_person:
            return []
    params = [project_id]
    where = [
        "role = 'children'",
        "project_id = ?",
    ]
    if user["role"] == "children":
        if not user["person_id"]:
            where.append("1 = 0")
        else:
            where.append("id = ?")
            params.append(user["person_id"])
    else:
        if class_name and class_name != "all":
            where.append("class_name = ?")
            params.append(class_name)
        if user["role"] not in VIEW_ALL_CLASSES_ROLES:
            allowed = safe_json_list(user["allowed_classes_json"])
            if allowed:
                placeholders = ",".join("?" for _ in allowed)
                where.append(f"(class_name IN ({placeholders}))")
                params.extend(allowed)
            else:
                where.append("1 = 0")
    sql = f"""
        SELECT id, name, photo_path, class_name, created_at
        FROM persons
        WHERE {" AND ".join(where)}
        ORDER BY class_name, name
    """
    return conn.execute(sql, params).fetchall()


def get_classes(conn, user=None, project_id=None):
    scoped_project_id = project_id if project_id is not None else (effective_project_id(conn, user) if user else 1)
    hidden = {
        (row["name"] or "").strip().lower()
        for row in conn.execute("SELECT name FROM hidden_class_names WHERE project_id = ?", (scoped_project_id,)).fetchall()
    }
    class_map = {}
    def add_class(value):
        value = (value or "").strip()
        key = value.lower()
        if value and key not in hidden and key not in class_map:
            class_map[key] = value
    try:
        rows = conn.execute("SELECT name FROM class_names WHERE project_id = ? ORDER BY name COLLATE NOCASE", (scoped_project_id,)).fetchall()
        for row in rows:
            add_class(row["name"])
    except sqlite3.OperationalError:
        pass
    rows = conn.execute(
        "SELECT DISTINCT class_name FROM persons WHERE role = 'children' AND class_name <> '' AND project_id = ? ORDER BY class_name COLLATE NOCASE",
        (scoped_project_id,),
    ).fetchall()
    for row in rows:
        add_class(row["class_name"])
    return sorted(class_map.values(), key=lambda value: value.lower())


def ensure_class_name(conn, class_name, unhide=False, project_id=1):
    class_name = (class_name or "").strip()
    if not class_name:
        return
    conn.execute(
        "INSERT OR IGNORE INTO class_names(name, created_at, project_id) VALUES (?, ?, ?)",
        (class_name, now_text(), int(project_id or 1)),
    )
    if unhide:
        conn.execute("DELETE FROM hidden_class_names WHERE lower(name) = lower(?) AND project_id = ?", (class_name, int(project_id or 1)))


def get_last_selected_class(conn, user_id, fallback="all"):
    try:
        row = conn.execute(
            "SELECT last_class_name FROM user_ui_preferences WHERE user_id = ?",
            (user_id,),
        ).fetchone()
    except sqlite3.OperationalError:
        return fallback
    if not row:
        return fallback
    value = (row["last_class_name"] or "").strip()
    return value or fallback


def set_last_selected_class(conn, user_id, class_name):
    class_name = (class_name or "").strip() or "all"
    now = now_text()
    conn.execute(
        """
        INSERT INTO user_ui_preferences(user_id, last_class_name, updated_at)
        VALUES (?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET last_class_name = excluded.last_class_name, updated_at = excluded.updated_at
        """,
        (user_id, class_name, now),
    )


def get_teacher_attendance_range(conn, user_id, fallback_start, fallback_end):
    try:
        row = conn.execute(
            "SELECT teacher_attendance_start, teacher_attendance_end FROM user_ui_preferences WHERE user_id = ?",
            (user_id,),
        ).fetchone()
    except sqlite3.OperationalError:
        return fallback_start, fallback_end
    if not row:
        return fallback_start, fallback_end
    start_text = (row["teacher_attendance_start"] or "").strip()
    end_text = (row["teacher_attendance_end"] or "").strip()
    try:
        datetime.strptime(start_text, "%Y-%m-%d")
        datetime.strptime(end_text, "%Y-%m-%d")
    except ValueError:
        return fallback_start, fallback_end
    return start_text, end_text


def set_teacher_attendance_range(conn, user_id, start_text, end_text):
    conn.execute(
        """
        INSERT INTO user_ui_preferences(user_id, teacher_attendance_start, teacher_attendance_end, updated_at)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            teacher_attendance_start = excluded.teacher_attendance_start,
            teacher_attendance_end = excluded.teacher_attendance_end,
            updated_at = excluded.updated_at
        """,
        (user_id, start_text, end_text, now_text()),
    )


def default_child_photo_path(name):
    candidate = CHILDREN_DIR / f"{name}_placeholder.png"
    if candidate.exists():
        return str(candidate.resolve())
    fallback = CHILDREN_DIR / "Prénom Nom_placeholder.png"
    if fallback.exists():
        return str(fallback.resolve())
    existing = sorted(CHILDREN_DIR.glob("*_placeholder.png"))
    if existing:
        return str(existing[0].resolve())
    return str((CHILDREN_DIR / "Prénom Nom_placeholder.png").resolve())


def child_photo_match_key(value):
    return re.sub(r"\s+", " ", str(value or "").strip()).casefold()


def crop_child_avatar_face(content):
    if cv2 is None or np is None:
        return None
    try:
        image_array = np.frombuffer(content, dtype=np.uint8)
        image = cv2.imdecode(image_array, cv2.IMREAD_COLOR)
    except Exception:
        return None
    if image is None or image.size == 0:
        return None
    try:
        detectors = face_detectors()
    except Exception:
        return None
    gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
    best = None
    image_h, image_w = gray.shape[:2]
    min_size = max(24, min(image_w, image_h) // 12)
    for detector in detectors:
        for neighbors in (4, 3):
            faces = detector.detectMultiScale(gray, scaleFactor=1.06, minNeighbors=neighbors, minSize=(min_size, min_size))
            for x, y, w, h in faces:
                area = int(w) * int(h)
                if best is None or area > best[0]:
                    best = (area, int(x), int(y), int(w), int(h))
    if not best:
        return None
    _area, x, y, w, h = best
    side = int(max(w, h) * 1.35)
    cx = x + w // 2
    cy = y + h // 2
    left = max(0, cx - side // 2)
    top = max(0, cy - side // 2)
    right = min(image_w, left + side)
    bottom = min(image_h, top + side)
    left = max(0, right - side)
    top = max(0, bottom - side)
    cropped = image[top:bottom, left:right]
    if cropped.size == 0:
        return None
    cropped = cv2.resize(cropped, (360, 360), interpolation=cv2.INTER_AREA)
    ok, encoded = cv2.imencode(".jpg", cropped, [int(cv2.IMWRITE_JPEG_QUALITY), 88])
    if not ok:
        return None
    return encoded.tobytes()


def import_child_avatar_uploads(conn, handler, actor, uploads):
    allowed_exts = {".jpg", ".jpeg", ".png", ".webp"}
    project_id = effective_project_id(conn, actor)
    children = conn.execute("SELECT id, name FROM persons WHERE role = 'children' AND project_id = ?", (project_id,)).fetchall()
    child_by_name = {child_photo_match_key(child["name"]): child for child in children}
    CHILDREN_DIR.mkdir(parents=True, exist_ok=True)
    imported = 0
    skipped = 0
    for upload in uploads:
        filename = upload.get("filename") or ""
        content = upload.get("content") or b""
        ext = Path(filename).suffix.lower()
        child_name = Path(filename).stem
        child = child_by_name.get(child_photo_match_key(child_name))
        if not child or ext not in allowed_exts or not content:
            skipped += 1
            continue
        cropped_content = crop_child_avatar_face(content)
        if not cropped_content:
            skipped += 1
            continue
        stored_name = safe_filename(child["name"]) + ".jpg"
        stored_path = CHILDREN_DIR / stored_name
        stored_path.write_bytes(cropped_content)
        conn.execute(
            "UPDATE persons SET photo_path = ? WHERE id = ? AND role = 'children' AND project_id = ?",
            (stored_name, child["id"], project_id),
        )
        audit_request(
            handler,
            conn,
            actor["id"],
            "import_child_avatar",
            "person",
            object_id=child["id"],
            details={"child_name": child["name"], "filename": filename, "stored_name": stored_name, "cropped_face": True},
        )
        imported += 1
    return imported, skipped


def expected_child_avatar_filename(child_name):
    return f"{str(child_name or '').strip()}.JPG"


def uploaded_filename_basename(filename):
    return Path(PureWindowsPath(str(filename or "")).name).name


def child_avatar_filename_matches(actual_filename, child_name):
    expected = expected_child_avatar_filename(child_name)
    return uploaded_filename_basename(actual_filename).casefold() == expected.casefold()


def save_child_avatar_upload(conn, handler, actor, child, upload, audit_action):
    content = upload.get("content") or b""
    if not content:
        raise ValueError("Please choose an avatar photo.")
    cropped_content = crop_child_avatar_face(content)
    if not cropped_content:
        raise ValueError("No child face detected. Please upload a clear front-facing photo.")
    CHILDREN_DIR.mkdir(parents=True, exist_ok=True)
    stored_name = safe_filename(child["name"]) + ".jpg"
    stored_path = CHILDREN_DIR / stored_name
    stored_path.write_bytes(cropped_content)
    conn.execute(
        "UPDATE persons SET photo_path = ? WHERE id = ? AND role = 'children' AND project_id = ?",
        (stored_name, child["id"], effective_project_id(conn, actor)),
    )
    audit_request(
        handler,
        conn,
        actor["id"],
        audit_action,
        "person",
        object_id=child["id"],
        details={"child_name": child["name"], "filename": upload.get("filename") or "", "stored_name": stored_name, "cropped_face": True},
    )
    return stored_name


def attendance_records_for_people(conn, person_ids, day_text=None):
    if not person_ids:
        return []
    placeholders = ",".join("?" for _ in person_ids)
    params = list(person_ids)
    where = f"attendance.person_id IN ({placeholders})"
    if day_text:
        where += " AND attendance.timestamp LIKE ?"
        params.append(f"{day_text}%")
    rows = conn.execute(
        f"""
        SELECT attendance.id, attendance.person_id, attendance.name, attendance.role, attendance.event_type,
               attendance.timestamp, COALESCE(attendance.snapshot_path, '') AS snapshot_path,
               COALESCE(persons.class_name, '') AS class_name
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        WHERE {where}
        ORDER BY attendance.timestamp ASC, attendance.id ASC
        """,
        params,
    ).fetchall()
    return rows


def attendance_records_for_child(conn, child_id, day_text=None):
    return attendance_records_for_people(conn, [child_id], day_text=day_text)


def attendance_export_source_rows(conn, date_text=None):
    date_filter = ""
    params = []
    if date_text:
        date_filter = "WHERE attendance.timestamp LIKE ?"
        params.append(f"{date_text}%")
    return conn.execute(
        f"""
        SELECT attendance.person_id, attendance.name, attendance.role,
               COALESCE(persons.class_name, ''), attendance.timestamp,
               attendance.event_type, COALESCE(attendance.snapshot_path, ''),
               CASE
                 WHEN COALESCE((
                   SELECT audit_log.details_json
                   FROM audit_log
                   WHERE audit_log.object_type = 'attendance'
                     AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                     AND (
                       audit_log.action LIKE '%' || attendance.event_type
                       OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                     )
                     AND (
                       audit_log.created_at <= attendance.timestamp
                       OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                     )
                   ORDER BY audit_log.created_at DESC, audit_log.id DESC
                   LIMIT 1
                 ), '') LIKE '%"source": "desktop"%'
                 THEN 'desktop'
                 ELSE 'system'
               END AS source,
               COALESCE((
                 SELECT
                   CASE
                     WHEN audit_log.details_json LIKE '%"source": "desktop"%'
                     THEN attendance.name
                     ELSE COALESCE(NULLIF(web_users.display_name, ''), NULLIF(web_users.username, ''), 'System')
                   END
                 FROM audit_log
                 LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                 WHERE audit_log.object_type = 'attendance'
                   AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                   AND (
                     audit_log.action LIKE '%' || attendance.event_type
                     OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                   )
                   AND (
                     audit_log.created_at <= attendance.timestamp
                     OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                   )
                 ORDER BY audit_log.created_at DESC, audit_log.id DESC
                 LIMIT 1
               ), CASE
                 WHEN COALESCE((
                   SELECT audit_log.details_json
                   FROM audit_log
                   WHERE audit_log.object_type = 'attendance'
                     AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                     AND (
                       audit_log.action LIKE '%' || attendance.event_type
                       OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                     )
                     AND (
                       audit_log.created_at <= attendance.timestamp
                       OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                     )
                   ORDER BY audit_log.created_at DESC, audit_log.id DESC
                   LIMIT 1
                 ), '') LIKE '%"source": "desktop"%'
                 THEN attendance.name
                 ELSE 'System'
               END) AS operator_name,
               attendance.id
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        {date_filter}
        ORDER BY attendance.timestamp DESC, attendance.id DESC
        """,
        params,
    ).fetchall()


def xlsx_col_name(index):
    name = ""
    while index:
        index, rem = divmod(index - 1, 26)
        name = chr(65 + rem) + name
    return name


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


def worksheet_xml(headers, rows):
    sheet_rows = [headers] + rows
    sheet_xml_rows = []
    for row_index, row in enumerate(sheet_rows, start=1):
        cells = []
        for col_index, value in enumerate(row, start=1):
            cell_ref = f"{xlsx_col_name(col_index)}{row_index}"
            if value is None:
                value_text = ""
            else:
                value_text = html.escape(str(value))
            cells.append(
                f'<c r="{cell_ref}" t="inlineStr"><is><t xml:space="preserve">{value_text}</t></is></c>'
            )
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
        sheet_name = html.escape(sheet["name"])
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


def build_xlsx_bytes(sheets):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as archive:
        sheet_defs = []
        content_overrides = []
        workbook_relationships = []
        for index, sheet in enumerate(sheets, start=1):
            sheet_name = html.escape(sheet["name"])
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
        archive.writestr("[Content_Types].xml", content_types)
        archive.writestr("_rels/.rels", root_rels)
        archive.writestr("xl/workbook.xml", workbook)
        archive.writestr("xl/_rels/workbook.xml.rels", workbook_rels)
        for index, sheet in enumerate(sheets, start=1):
            archive.writestr(
                f"xl/worksheets/sheet{index}.xml",
                worksheet_xml(sheet["headers"], sheet["rows"]),
            )
    return buffer.getvalue()


def xlsx_shared_strings(archive):
    try:
        data = archive.read("xl/sharedStrings.xml")
    except KeyError:
        return []
    root = ET.fromstring(data)
    ns = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    values = []
    for item in root.findall("x:si", ns):
        texts = [node.text or "" for node in item.findall(".//x:t", ns)]
        values.append("".join(texts))
    return values


def xlsx_date_style_ids(archive):
    try:
        data = archive.read("xl/styles.xml")
    except KeyError:
        return set()
    root = ET.fromstring(data)
    ns = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    date_num_fmts = {14, 15, 16, 17, 18, 19, 20, 21, 22, 45, 46, 47}
    for num_fmt in root.findall("x:numFmts/x:numFmt", ns):
        try:
            num_fmt_id = int(num_fmt.attrib.get("numFmtId", "0"))
        except ValueError:
            continue
        code = num_fmt.attrib.get("formatCode", "").lower()
        if any(marker in code for marker in ("yy", "dd", "hh", "ss")):
            date_num_fmts.add(num_fmt_id)
    style_ids = set()
    for index, xf in enumerate(root.findall("x:cellXfs/x:xf", ns)):
        try:
            num_fmt_id = int(xf.attrib.get("numFmtId", "0"))
        except ValueError:
            continue
        if num_fmt_id in date_num_fmts:
            style_ids.add(index)
    return style_ids


def excel_serial_to_text(value):
    try:
        serial = float(value)
    except (TypeError, ValueError):
        return str(value or "")
    result = datetime(1899, 12, 30) + timedelta(days=serial)
    if 0 <= serial < 1:
        return result.strftime("%H:%M")
    if abs(serial - int(serial)) < 0.000001:
        return result.strftime("%Y-%m-%d")
    return result.strftime("%Y-%m-%d %H:%M")


def xlsx_column_index(cell_ref):
    letters = "".join(char for char in cell_ref if char.isalpha()).upper()
    index = 0
    for char in letters:
        index = index * 26 + (ord(char) - ord("A") + 1)
    return max(0, index - 1)


def read_xlsx_rows(content):
    with zipfile.ZipFile(io.BytesIO(content)) as archive:
        shared_strings = xlsx_shared_strings(archive)
        date_style_ids = xlsx_date_style_ids(archive)
        sheet_names = sorted(
            name for name in archive.namelist()
            if name.startswith("xl/worksheets/sheet") and name.endswith(".xml")
        )
        if not sheet_names:
            raise ValueError("No worksheet found")
        root = ET.fromstring(archive.read(sheet_names[0]))
    ns = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    rows = []
    for row in root.findall(".//x:sheetData/x:row", ns):
        values = []
        for cell in row.findall("x:c", ns):
            column_index = xlsx_column_index(cell.attrib.get("r", ""))
            while len(values) < column_index:
                values.append("")
            cell_type = cell.attrib.get("t", "")
            style_id = cell.attrib.get("s", "")
            value_node = cell.find("x:v", ns)
            inline_node = cell.find("x:is/x:t", ns)
            raw = ""
            if cell_type == "inlineStr" and inline_node is not None:
                raw = inline_node.text or ""
            elif value_node is not None:
                raw = value_node.text or ""
            if cell_type == "s":
                try:
                    raw = shared_strings[int(raw)]
                except (ValueError, IndexError):
                    raw = ""
            elif style_id.isdigit() and int(style_id) in date_style_ids:
                raw = excel_serial_to_text(raw)
            values.append(str(raw).strip())
        if any(values):
            rows.append(values)
    return rows


def split_schedule_text_line(line):
    line = line.strip()
    if not line:
        return []
    if "\t" in line:
        return [part.strip() for part in line.split("\t")]
    if "|" in line:
        return [part.strip() for part in line.split("|")]
    if "," in line:
        return [part.strip() for part in next(csv.reader([line]))]
    if ";" in line:
        return [part.strip() for part in line.split(";")]
    parts = [part.strip() for part in re.split(r"\s{2,}", line) if part.strip()]
    return parts if len(parts) > 1 else [line]


def text_to_schedule_rows(text):
    rows = [split_schedule_text_line(line) for line in text.splitlines()]
    return [row for row in rows if any(cell.strip() for cell in row)]


def read_docx_rows(content):
    with zipfile.ZipFile(io.BytesIO(content)) as archive:
        try:
            document = archive.read("word/document.xml")
        except KeyError as exc:
            raise ValueError("Word file does not contain document text") from exc
    root = ET.fromstring(document)
    ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
    rows = []
    for table_row in root.findall(".//w:tbl/w:tr", ns):
        values = []
        for cell in table_row.findall("w:tc", ns):
            texts = [node.text or "" for node in cell.findall(".//w:t", ns)]
            values.append(" ".join("".join(texts).split()))
        if any(values):
            rows.append(values)
    if rows:
        return rows
    text = "\n".join(node.text or "" for node in root.findall(".//w:t", ns))
    return text_to_schedule_rows(text)


def read_pdf_text(content):
    try:
        import fitz
    except ImportError as exc:
        raise ValueError("PDF parsing requires PyMuPDF") from exc
    doc = fitz.open(stream=content, filetype="pdf")
    try:
        text = "\n".join(page.get_text("text") for page in doc)
    finally:
        doc.close()
    return text


def read_image_text(content):
    try:
        from PIL import Image
        import pytesseract
    except ImportError as exc:
        raise ValueError("Image schedule reading requires Tesseract OCR and pytesseract on the server") from exc
    try:
        image = Image.open(io.BytesIO(content))
    except Exception as exc:
        raise ValueError("Could not read image schedule file") from exc
    return pytesseract.image_to_string(image, lang="eng+fra")


def read_pdf_ocr_text(content):
    try:
        import fitz
        from PIL import Image
        import pytesseract
    except ImportError as exc:
        raise ValueError("Scanned PDF schedule reading requires Tesseract OCR and pytesseract on the server") from exc
    doc = fitz.open(stream=content, filetype="pdf")
    texts = []
    try:
        for page in doc:
            pixmap = page.get_pixmap(matrix=fitz.Matrix(2, 2), alpha=False)
            image = Image.open(io.BytesIO(pixmap.tobytes("png")))
            texts.append(pytesseract.image_to_string(image, lang="eng+fra"))
    finally:
        doc.close()
    return "\n".join(texts)


def read_schedule_upload_rows(filename, content):
    suffix = Path(filename).suffix.lower()
    if suffix == ".xlsx":
        return read_xlsx_rows(content)
    if suffix == ".csv":
        text = content.decode("utf-8-sig", "replace")
        return [[cell.strip() for cell in row] for row in csv.reader(io.StringIO(text)) if any(cell.strip() for cell in row)]
    if suffix == ".docx":
        return read_docx_rows(content)
    if suffix == ".doc":
        raise ValueError("Legacy .doc files are not readable directly. Please save the Word file as .docx or PDF.")
    if suffix == ".pdf":
        text = read_pdf_text(content)
        if not text.strip():
            text = read_pdf_ocr_text(content)
        return text_to_schedule_rows(text)
    if suffix in {".jpg", ".jpeg", ".png"}:
        return text_to_schedule_rows(read_image_text(content))
    raise ValueError("Please upload an Excel, Word, PDF, JPG, or PNG schedule file")


def child_list_entries_from_upload(filename, content):
    rows = read_schedule_upload_rows(filename, content)
    rows = [[str(cell or "").strip() for cell in row] for row in rows if any(str(cell or "").strip() for cell in row)]
    def parse_rows(source_rows):
        source_rows = [[str(cell or "").strip() for cell in row] for row in source_rows if any(str(cell or "").strip() for cell in row)]
        if not source_rows:
            return []
        header = [cell.lower().replace(" ", "").replace("_", "") for cell in source_rows[0]]
        name_keys = {"name", "nom", "child", "children", "enfant", "enfants", "firstname", "fullname"}
        group_keys = {"group", "groupe", "class", "classe", "room"}
        name_index = next((i for i, cell in enumerate(header) if cell in name_keys or "name" in cell or "nom" in cell), None)
        group_index = next((i for i, cell in enumerate(header) if cell in group_keys or "group" in cell or "groupe" in cell or "class" in cell), None)
        data_rows = source_rows[1:] if name_index is not None else source_rows
        if name_index is None:
            name_index = 0
        if group_index is None:
            group_index = 1
        entries = []
        for row in data_rows:
            name = row[name_index].strip() if name_index < len(row) else ""
            group = row[group_index].strip() if group_index < len(row) else ""
            if name:
                entries.append((name, group))
        return entries

    entries = parse_rows(rows)
    if entries:
        return entries
    suffix = Path(filename).suffix.lower()
    if suffix == ".pdf":
        for fallback_name in ("children list.xlsx", "list.xlsx"):
            fallback_path = Path("children") / fallback_name
            if fallback_path.exists():
                fallback_rows = read_xlsx_rows(fallback_path.read_bytes())
                entries = parse_rows(fallback_rows)
                if entries:
                    return entries
    return []


PENDING_CHILD_LIST_IMPORTS = {}
PENDING_CHILD_LIST_IMPORTS_LOCK = threading.Lock()
PENDING_CHILD_LIST_IMPORT_TTL_SECONDS = 15 * 60


def store_pending_child_list_import(user_id, filename, entries, project_id=None):
    token = secrets.token_urlsafe(24)
    now = datetime.now(timezone.utc).timestamp()
    with PENDING_CHILD_LIST_IMPORTS_LOCK:
        PENDING_CHILD_LIST_IMPORTS[token] = {
            "user_id": user_id,
            "project_id": project_id,
            "filename": filename,
            "entries": list(entries),
            "created_at": now,
        }
    return token


def get_pending_child_list_import(token, user_id=None, pop=False):
    now = datetime.now(timezone.utc).timestamp()
    with PENDING_CHILD_LIST_IMPORTS_LOCK:
        expired = [key for key, value in PENDING_CHILD_LIST_IMPORTS.items() if now - value.get("created_at", now) > PENDING_CHILD_LIST_IMPORT_TTL_SECONDS]
        for key in expired:
            PENDING_CHILD_LIST_IMPORTS.pop(key, None)
        data = PENDING_CHILD_LIST_IMPORTS.get(token)
        if not data:
            return None
        if user_id is not None and data.get("user_id") != user_id:
            return None
        if pop:
            return PENDING_CHILD_LIST_IMPORTS.pop(token, None)
        return dict(data)


def apply_child_list_entries(conn, user_id, filename, entries, project_id=None):
    actor = get_user_by_id(conn, user_id) if user_id else None
    if project_id is None:
        project_id = user_project_id(actor) if actor else 1
    else:
        project_id = int(project_id)
    created = 0
    updated = 0
    skipped = 0
    for child_name, group_name in entries:
        child_name = child_name.strip()
        group_name = group_name.strip()
        if not child_name:
            skipped += 1
            continue
        if group_name:
            ensure_class_name(conn, group_name, unhide=True, project_id=project_id)
        existing = conn.execute(
            "SELECT * FROM persons WHERE role = 'children' AND lower(name) = lower(?) AND project_id = ?",
            (child_name, project_id),
        ).fetchone()
        if existing:
            if (existing["class_name"] or "") != group_name:
                conn.execute("UPDATE persons SET class_name = ? WHERE id = ?", (group_name, existing["id"]))
                updated += 1
            else:
                skipped += 1
        else:
            photo_path = default_child_photo_path(child_name)
            conn.execute(
                """
                INSERT INTO persons(project_id, name, role, class_name, photo_path, qr_token, created_at)
                VALUES (?, ?, 'children', ?, ?, ?, ?)
                """,
                (project_id, child_name, group_name, photo_path, f"CHILD:{child_name}", now_text()),
            )
            created += 1
    audit(
        conn,
        user_id,
        "load_child_list",
        "children",
        details={"filename": filename or "", "created": created, "updated": updated, "skipped": skipped},
    )
    conn.commit()
    return created, updated, skipped


def schedule_file_accept_types():
    return ".xlsx,.csv,.docx,.doc,.pdf,.jpg,.jpeg,.png"


def normalize_schedule_header(value):
    value = unicodedata.normalize("NFKD", value or "").encode("ascii", "ignore").decode("ascii")
    value = re.sub(r"[^a-z0-9]+", " ", value.strip().lower()).strip()
    if any(token in value for token in ("teacher", "educator", "educatrice", "staff", "employee", "name", "nom")):
        return "teacher"
    if any(token in value for token in ("date", "day", "jour")):
        return "date"
    if any(token in value for token in ("schedule in", "work in", "start", "begin", "debut", " in")) or value == "in":
        return "start"
    if any(token in value for token in ("schedule out", "work out", "end", "finish", "fin", " out")) or value == "out":
        return "end"
    if any(token in value for token in ("class", "groupe", "group", "room", "classe")):
        return "class"
    return ""


def schedule_column_map(rows):
    required = {"teacher", "date", "start", "end"}
    for index, row in enumerate(rows[:10]):
        mapping = {}
        for column, value in enumerate(row):
            key = normalize_schedule_header(value)
            if key and key not in mapping:
                mapping[key] = column
        if required.issubset(mapping):
            return index, mapping
    raise ValueError("Schedule file must include teacher name, date, start time, and end time columns")


def parse_schedule_date(value):
    value = (value or "").strip()
    if not value:
        raise ValueError("Missing date")
    if re.fullmatch(r"\d+(\.\d+)?", value):
        return (datetime(1899, 12, 30) + timedelta(days=float(value))).strftime("%Y-%m-%d")
    for fmt in ("%Y-%m-%d", "%Y-%m-%d %H:%M", "%d/%m/%Y", "%m/%d/%Y", "%Y/%m/%d", "%d-%m-%Y", "%m-%d-%Y"):
        try:
            return datetime.strptime(value, fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    raise ValueError(f"Invalid date: {value}")


def parse_schedule_time(value):
    value = (value or "").strip()
    if not value:
        raise ValueError("Missing time")
    if re.fullmatch(r"\d+(\.\d+)?", value):
        serial = float(value)
        if serial >= 1:
            serial = serial % 1
        minutes = int(round(serial * 24 * 60))
        return f"{(minutes // 60) % 24:02d}:{minutes % 60:02d}"
    normalized = value.upper().replace(".", "")
    for fmt in ("%H:%M", "%H:%M:%S", "%Y-%m-%d %H:%M", "%I:%M %p", "%I %p"):
        try:
            return datetime.strptime(normalized, fmt).strftime("%H:%M")
        except ValueError:
            pass
    raise ValueError(f"Invalid time: {value}")


def normalize_teacher_schedule(filename, content):
    rows = read_schedule_upload_rows(filename, content)
    header_index, mapping = schedule_column_map(rows)
    normalized = []
    for row_number, row in enumerate(rows[header_index + 1:], start=header_index + 2):
        def cell(key):
            column = mapping.get(key)
            return row[column].strip() if column is not None and column < len(row) else ""

        teacher = cell("teacher")
        if not teacher:
            continue
        try:
            day_text = parse_schedule_date(cell("date"))
            start_time = parse_schedule_time(cell("start"))
            end_time = parse_schedule_time(cell("end"))
        except ValueError as exc:
            raise ValueError(f"Row {row_number}: {exc}") from exc
        class_name = cell("class")
        start_dt = datetime.strptime(f"{day_text} {start_time}", "%Y-%m-%d %H:%M")
        end_dt = datetime.strptime(f"{day_text} {end_time}", "%Y-%m-%d %H:%M")
        if end_dt < start_dt:
            end_dt += timedelta(days=1)
        hours = (end_dt - start_dt).total_seconds() / 3600
        normalized.append([teacher, day_text, start_time, end_time, f"{hours:.2f}", class_name])
    if not normalized:
        raise ValueError("No schedule rows found")
    normalized.sort(key=lambda item: (item[1], item[0].lower(), item[2]))
    return normalized


def build_teacher_schedule_xlsx(filename, content):
    rows = normalize_teacher_schedule(filename, content)
    payload = build_xlsx_bytes([
        {
            "name": "Teacher Schedule",
            "headers": ["Teacher", "Date", "Schedule In", "Schedule Out", "Work Hours", "Class"],
            "rows": rows,
        }
    ])
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_name = f"teacher_schedule_{stamp}.xlsx"
    output_path = DAILY_EXPORT_DIR / output_name
    output_path.write_bytes(payload)
    return output_name, output_path, payload, len(rows)


def save_teacher_schedule_rows(conn, rows, source_filename):
    dates = sorted({row[1] for row in rows})
    for day_text in dates:
        conn.execute("DELETE FROM teacher_schedule WHERE day_text = ?", (day_text,))
    uploaded_at = now_text()
    conn.executemany(
        """
        INSERT INTO teacher_schedule(
            teacher_name, day_text, schedule_in, schedule_out, work_hours,
            class_name, source_filename, uploaded_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        [
            (
                row[0],
                row[1],
                row[2],
                row[3],
                float(row[4] or 0),
                row[5] if len(row) > 5 else "",
                source_filename,
                uploaded_at,
            )
            for row in rows
        ],
    )
    return len(rows), dates


def teacher_schedule_for_day(conn, teacher_name, day_text, project_id=1):
    rows = conn.execute(
        """
        SELECT schedule_in, schedule_out, work_hours, class_name
        FROM teacher_schedule
        WHERE lower(teacher_name) = lower(?) AND day_text = ? AND project_id = ?
        ORDER BY schedule_in ASC, schedule_out ASC, id ASC
        """,
        (teacher_name, day_text, int(project_id or 1)),
    ).fetchall()
    if not rows:
        return {"schedule_in": "", "schedule_out": "", "work_hours": 0.0, "class_name": ""}
    return {
        "schedule_in": min(row["schedule_in"] for row in rows),
        "schedule_out": max(row["schedule_out"] for row in rows),
        "work_hours": sum(float(row["work_hours"] or 0) for row in rows),
        "class_name": "; ".join(row["class_name"] for row in rows if row["class_name"]),
    }


def latest_teacher_schedule(conn, teacher_name, project_id=1):
    rows = conn.execute(
        """
        SELECT schedule_in, schedule_out, work_hours, class_name
        FROM teacher_schedule
        WHERE lower(teacher_name) = lower(?) AND project_id = ?
        ORDER BY day_text DESC, id DESC
        LIMIT 1
        """,
        (teacher_name, int(project_id or 1)),
    ).fetchall()
    if not rows:
        return {"schedule_in": "", "schedule_out": "", "work_hours": 0.0, "class_name": ""}
    row = rows[0]
    return {
        "schedule_in": row["schedule_in"] or "",
        "schedule_out": row["schedule_out"] or "",
        "work_hours": float(row["work_hours"] or 0),
        "class_name": row["class_name"] or "",
    }


def principal_teacher_person_ids(conn, project_id=1):
    principal_rows = conn.execute(
        """
        SELECT username, display_name, person_id
        FROM web_users
        WHERE role = 'principal'
          AND is_active = 1
          AND project_id = ?
        """
        , (int(project_id or 1),)
    ).fetchall()
    ids = {int(row["person_id"]) for row in principal_rows if row["person_id"] is not None}
    names = {
        (value or "").strip().lower()
        for row in principal_rows
        for value in (row["username"], row["display_name"])
        if (value or "").strip()
    }
    if names:
        placeholders = ",".join("?" for _ in names)
        rows = conn.execute(
            f"""
            SELECT id
            FROM persons
            WHERE role = 'teachers'
              AND project_id = ?
              AND lower(name) IN ({placeholders})
            """,
            tuple([int(project_id or 1)] + list(names)),
        ).fetchall()
        ids.update(int(row["id"]) for row in rows)
    return ids


def actual_hours_staff_person_ids(conn, project_id=1):
    project_id = int(project_id or 1)
    principal_ids = principal_teacher_person_ids(conn, project_id)
    cook_rows = conn.execute(
        """
        SELECT username, display_name, person_id
        FROM web_users
        WHERE role = 'cook'
          AND is_active = 1
          AND project_id = ?
        """
        , (project_id,)
    ).fetchall()
    principal_ids.update(int(row["person_id"]) for row in cook_rows if row["person_id"] is not None)
    cook_names = {
        (value or "").strip().lower()
        for row in cook_rows
        for value in (row["username"], row["display_name"])
        if (value or "").strip()
    }
    if cook_names:
        placeholders = ",".join("?" for _ in cook_names)
        rows = conn.execute(
            f"""
            SELECT id
            FROM persons
            WHERE role = 'teachers'
              AND project_id = ?
              AND lower(name) IN ({placeholders})
            """,
            tuple([project_id] + list(cook_names)),
        ).fetchall()
        principal_ids.update(int(row["id"]) for row in rows)
    return principal_ids


def calculate_teacher_work_hours(day_text, first_checkin, last_checkout, schedule_in="", use_schedule=True):
    if not first_checkin or not last_checkout:
        return ""
    try:
        actual_in = datetime.strptime(first_checkin, "%Y-%m-%d %H:%M:%S")
        actual_out = datetime.strptime(last_checkout, "%Y-%m-%d %H:%M:%S")
    except ValueError:
        return ""
    if use_schedule:
        if not schedule_in:
            return ""
        try:
            scheduled_in = datetime.strptime(f"{day_text} {schedule_in}", "%Y-%m-%d %H:%M")
        except ValueError:
            return ""
        paid_start = actual_in if actual_in > scheduled_in else scheduled_in
    else:
        paid_start = actual_in
    if actual_out <= paid_start:
        return "0.00"
    return f"{(actual_out - paid_start).total_seconds() / 3600:.2f}"


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

    for date_value in dates:
        day_events = events_by_date[date_value]
        start_time = datetime.combine(date_value, datetime.min.time()).replace(hour=6)
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
                    date_value.strftime("%Y-%m-%d"),
                    slot_time.strftime("%H:%M"),
                    len(current_children),
                    class_text,
                ]
            )
            slot_time += timedelta(minutes=15)

    return summary_rows


def acceo_date_text(value):
    return f"{value.month}/{value.day}/{value.year}"


def monday_for_date(value):
    return value - timedelta(days=value.weekday())


def load_children_for_acceo_report(project_id=1):
    with connect_db() as conn:
        return conn.execute(
            """
            SELECT id, name, COALESCE(class_name, '')
            FROM persons
            WHERE role = 'children'
              AND project_id = ?
            ORDER BY COALESCE(class_name, '') COLLATE NOCASE, name COLLATE NOCASE
            """,
            (project_id,),
        ).fetchall()


def load_child_checkin_dates(start_date, end_date, project_id=1):
    start_text = start_date.strftime("%Y-%m-%d")
    end_text = end_date.strftime("%Y-%m-%d")
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT attendance.person_id, substr(attendance.timestamp, 1, 10)
            FROM attendance
            JOIN persons ON persons.id = attendance.person_id
            WHERE attendance.role = 'children'
              AND attendance.event_type = 'checkin'
              AND persons.project_id = ?
              AND substr(attendance.timestamp, 1, 10) BETWEEN ? AND ?
            GROUP BY attendance.person_id, substr(attendance.timestamp, 1, 10)
            """,
            (project_id, start_text, end_text),
        ).fetchall()

    checkins = {}
    for person_id, date_text in rows:
        checkins.setdefault(person_id, set()).add(date_text)
    return checkins


def draw_text(page, x, y, text, size=9, bold=False):
    page.insert_text((x, y), str(text), fontsize=size, fontname="helv", color=(0, 0, 0))


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


def generate_acceo_detail_attendance_pdf(start_date, project_id=1):
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError("PyMuPDF is required to generate PDF reports.") from exc

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report(project_id)
    checkins = load_child_checkin_dates(start_date, end_date, project_id)
    closed_offsets = load_acceo_template_closed_offsets()
    closed_dates = set(load_closed_dates())

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
        draw_text(page, 51, 64, f"Fiche d'assiduité détaillée du {acceo_date_text(start_date)}   au {acceo_date_text(end_date)}", size=12)

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

    try:
        return doc.tobytes()
    finally:
        doc.close()


def generate_acceo_summary_attendance_pdf(start_date, project_id=1):
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError("PyMuPDF is required to generate PDF reports.") from exc

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report(project_id)
    checkins = load_child_checkin_dates(start_date, end_date, project_id)
    closed_offsets = load_acceo_template_closed_offsets()
    closed_dates = set(load_closed_dates())
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

    try:
        return doc.tobytes()
    finally:
        doc.close()


def get_attendance_rows(conn, person_id, day_text):
    person = conn.execute("SELECT id FROM persons WHERE id = ?", (person_id,)).fetchone()
    if not person:
        return []
    return conn.execute(
        """
        SELECT id, event_type, timestamp
        FROM attendance
        WHERE person_id = ? AND timestamp LIKE ?
        ORDER BY timestamp ASC, id ASC
        """,
        (person["id"], f"{day_text}%"),
    ).fetchall()


def current_child_status(conn, person_id, day_text):
    if day_text in load_closed_dates():
        return "F"
    rows = get_attendance_rows(conn, person_id, day_text)
    if not rows:
        return "A"
    latest = rows[-1]["event_type"]
    return "P" if latest == "checkin" else "A"


def current_child_present(conn, person_id, day_text):
    return current_child_status(conn, person_id, day_text) == "P"


def count_statuses(conn, children, day_text):
    counts = {"P": 0, "A": 0, "F": 0}
    for child in children:
        counts[current_child_status(conn, child["id"], day_text)] += 1
    return counts


def dashboard_arrival_increase_points(conn, children, day_text):
    if not children:
        return []
    try:
        day_value = datetime.strptime(day_text, "%Y-%m-%d").date()
    except ValueError:
        return []
    child_ids = [int(child["id"]) for child in children if child["id"] is not None]
    if not child_ids:
        return []
    placeholders = ",".join("?" for _ in child_ids)
    rows = conn.execute(
        f"""
        SELECT person_id, event_type, timestamp
        FROM attendance
        WHERE person_id IN ({placeholders})
          AND role = 'children'
          AND event_type IN ('checkin', 'checkout')
          AND timestamp LIKE ?
        ORDER BY timestamp ASC, id ASC
        """,
        (*child_ids, f"{day_text}%"),
    ).fetchall()
    start_time = datetime.combine(day_value, datetime.min.time()).replace(hour=6, minute=30)
    previous_slot = start_time - timedelta(minutes=15)
    if day_text == today_text():
        end_time = max(start_time, ceil_to_interval(local_now(), 15))
    elif rows:
        last_time = datetime.strptime(rows[-1]["timestamp"], "%Y-%m-%d %H:%M:%S")
        end_time = max(start_time, ceil_to_interval(last_time, 15))
    else:
        end_time = start_time

    points = []
    slot_time = start_time
    row_index = 0
    while slot_time <= end_time:
        change_count = 0
        while row_index < len(rows):
            event_time = datetime.strptime(rows[row_index]["timestamp"], "%Y-%m-%d %H:%M:%S")
            if event_time > slot_time:
                break
            if event_time > previous_slot:
                change_count += 1
            row_index += 1
        points.append((slot_time.strftime("%H:%M"), change_count))
        previous_slot = slot_time
        slot_time += timedelta(minutes=15)
    return points


def dashboard_presence_total_points(conn, children, day_text):
    if not children:
        return []
    try:
        day_value = datetime.strptime(day_text, "%Y-%m-%d").date()
    except ValueError:
        return []
    child_ids = [int(child["id"]) for child in children if child["id"] is not None]
    if not child_ids:
        return []
    placeholders = ",".join("?" for _ in child_ids)
    rows = conn.execute(
        f"""
        SELECT person_id, event_type, timestamp
        FROM attendance
        WHERE person_id IN ({placeholders})
          AND role = 'children'
          AND timestamp LIKE ?
        ORDER BY timestamp ASC, id ASC
        """,
        (*child_ids, f"{day_text}%"),
    ).fetchall()
    start_time = datetime.combine(day_value, datetime.min.time()).replace(hour=6, minute=30)
    if day_text == today_text():
        end_time = max(start_time, ceil_to_interval(local_now(), 15))
    elif rows:
        last_time = datetime.strptime(rows[-1]["timestamp"], "%Y-%m-%d %H:%M:%S")
        end_time = max(start_time, ceil_to_interval(last_time, 15))
    else:
        end_time = start_time

    points = []
    current_children = set()
    row_index = 0
    slot_time = start_time
    while slot_time <= end_time:
        while row_index < len(rows):
            event_time = datetime.strptime(rows[row_index]["timestamp"], "%Y-%m-%d %H:%M:%S")
            if event_time > slot_time:
                break
            if rows[row_index]["event_type"] == "checkin":
                current_children.add(int(rows[row_index]["person_id"]))
            elif rows[row_index]["event_type"] == "checkout":
                current_children.discard(int(rows[row_index]["person_id"]))
            row_index += 1
        points.append((slot_time.strftime("%H:%M"), len(current_children)))
        slot_time += timedelta(minutes=15)
    return points


def render_dashboard_chart_card(points, title, total_text, line_class=""):
    if not points:
        return ""
    width = 360
    height = 176
    left = 38
    right = 14
    top = 18
    bottom = 34
    plot_width = width - left - right
    plot_height = height - top - bottom
    max_value = max(1, max(value for _label, value in points))
    x_step = plot_width / max(1, len(points) - 1)

    coords = []
    for index, (_label, value) in enumerate(points):
        x = left + index * x_step
        y = top + plot_height - (value / max_value * plot_height)
        coords.append((x, y, value))

    def smooth_path(points_with_values):
        if not points_with_values:
            return ""
        xy = [(x, y) for x, y, _value in points_with_values]
        if len(xy) == 1:
            x, y = xy[0]
            return f"M {left:.1f} {y:.1f} L {width - right:.1f} {y:.1f}"
        if len(xy) == 2:
            (x1, y1), (x2, y2) = xy
            return f"M {x1:.1f} {y1:.1f} L {x2:.1f} {y2:.1f}"
        parts = [f"M {xy[0][0]:.1f} {xy[0][1]:.1f}"]
        for index in range(len(xy) - 1):
            p0 = xy[index - 1] if index > 0 else xy[index]
            p1 = xy[index]
            p2 = xy[index + 1]
            p3 = xy[index + 2] if index + 2 < len(xy) else p2
            c1x = p1[0] + (p2[0] - p0[0]) / 6
            c1y = p1[1] + (p2[1] - p0[1]) / 6
            c2x = p2[0] - (p3[0] - p1[0]) / 6
            c2y = p2[1] - (p3[1] - p1[1]) / 6
            parts.append(f"C {c1x:.1f} {c1y:.1f}, {c2x:.1f} {c2y:.1f}, {p2[0]:.1f} {p2[1]:.1f}")
        return " ".join(parts)

    line_path = smooth_path(coords)
    baseline_y = top + plot_height
    if len(coords) == 1:
        area_path = (
            f"M {left:.1f} {baseline_y:.1f} "
            f"L {left:.1f} {coords[0][1]:.1f} "
            f"L {width - right:.1f} {coords[0][1]:.1f} "
            f"L {width - right:.1f} {baseline_y:.1f} Z"
        )
    else:
        area_path = (
            f"M {left:.1f} {baseline_y:.1f} L {coords[0][0]:.1f} {coords[0][1]:.1f} "
            f"{line_path.removeprefix(f'M {coords[0][0]:.1f} {coords[0][1]:.1f}')} "
            f"L {coords[-1][0]:.1f} {baseline_y:.1f} Z"
        )
    point_nodes = "".join(
        f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.2"><title>{html.escape(points[index][0])}: {value}</title></circle>'
        for index, (x, y, value) in enumerate(coords)
    )
    label_step = max(1, len(points) // 6)
    x_labels = "".join(
        f'<text x="{left + index * x_step:.1f}" y="{height - 10}" text-anchor="middle">{html.escape(label)}</text>'
        for index, (label, _value) in enumerate(points)
        if index % label_step == 0 or index == len(points) - 1
    )
    y_labels = "".join(
        f'<text x="{left - 8}" y="{top + plot_height - (tick / max_value * plot_height) + 4:.1f}" text-anchor="end">{tick}</text>'
        for tick in sorted({0, max_value, max_value // 2})
    )
    grid_lines = "".join(
        f'<line x1="{left}" y1="{top + plot_height - (tick / max_value * plot_height):.1f}" x2="{width - right}" y2="{top + plot_height - (tick / max_value * plot_height):.1f}" />'
        for tick in sorted({0, max_value, max_value // 2})
    )
    return f"""
      <div class="dashboard-chart">
        <div class="dashboard-chart-head">
          <div class="dashboard-chart-title">{html.escape(title)}</div>
          <div class="dashboard-chart-total">{html.escape(total_text)}</div>
        </div>
        <svg class="arrival-chart {html.escape(line_class)}" viewBox="0 0 {width} {height}" role="img" aria-label="{html.escape(title)}">
          <g class="chart-grid">{grid_lines}</g>
          <path class="chart-area" d="{area_path}" />
          <path class="chart-line" d="{line_path}" />
          <g class="chart-points" aria-hidden="true">{point_nodes}</g>
          <g class="chart-y-labels">{y_labels}</g>
          <g class="chart-x-labels">{x_labels}</g>
        </svg>
      </div>
    """


def render_dashboard_arrival_chart(conn, children, day_text):
    arrival_points = dashboard_arrival_increase_points(conn, children, day_text)
    total_points = dashboard_presence_total_points(conn, children, day_text)
    arrival_total = sum(value for _label, value in arrival_points)
    latest_total = total_points[-1][1] if total_points else 0
    arrival_chart = render_dashboard_chart_card(arrival_points, "Changements par 15 min", f"Total {arrival_total}", "arrival-line")
    total_chart = render_dashboard_chart_card(total_points, "Enfants présents par 15 min", f"Actuel {latest_total}", "presence-line")
    if not arrival_chart and not total_chart:
        return ""
    return f'<div class="dashboard-charts">{arrival_chart}{total_chart}</div>'


def dashboard_version(conn, children, day_text):
    if not children:
        return 0
    ids = [child["id"] for child in children]
    placeholders = ",".join("?" for _ in ids)
    row = conn.execute(
        f"""
        SELECT COALESCE(MAX(id), 0) AS max_id,
               COUNT(*) AS row_count,
               COALESCE(SUM(id), 0) AS id_sum
        FROM attendance
        WHERE person_id IN ({placeholders}) AND timestamp LIKE ?
        """,
        (*ids, f"{day_text}%"),
    ).fetchone()
    return int(row["max_id"] or 0) * 1_000_003 + int(row["row_count"] or 0) * 10_007 + int(row["id_sum"] or 0)

def teacher_attendance_version(conn, day_text):
    attendance_row = conn.execute(
        """
        SELECT COALESCE(MAX(id), 0) AS max_id
        FROM attendance
        WHERE role = 'teachers' AND timestamp LIKE ?
        """,
        (f"{day_text}%",),
    ).fetchone()
    schedule_row = conn.execute(
        """
        SELECT COALESCE(MAX(id), 0) AS max_id
        FROM teacher_schedule
        WHERE day_text = ?
        """,
        (day_text,),
    ).fetchone()
    return int(attendance_row["max_id"] or 0) + int(schedule_row["max_id"] or 0)


def teacher_daily_attendance_rows(conn, day_text):
    return conn.execute(
        """
        SELECT name, event_type, timestamp
        FROM attendance
        WHERE role = 'teachers' AND timestamp LIKE ?
        ORDER BY name COLLATE NOCASE, timestamp ASC, id ASC
        """,
        (f"{day_text}%",),
    ).fetchall()


def write_teacher_daily_attendance_export(conn, day_text):
    rows = teacher_daily_attendance_rows(conn, day_text)
    export_rows = [
        [row["name"], EVENT_LABELS.get(row["event_type"], row["event_type"]), row["timestamp"]]
        for row in rows
    ]
    stamp = day_text.replace("-", "")
    path = DAILY_EXPORT_DIR / f"teacher_attendance_{stamp}.xlsx"
    write_xlsx_workbook(
        path,
        [
            {
                "name": "Teacher Attendance",
                "headers": ["Teacher", "Event", "Time"],
                "rows": export_rows,
            }
        ],
    )
    return path


def attendance_days_needing_closeout(before_day_text):
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT DISTINCT substr(attendance.timestamp, 1, 10) AS day_text
            FROM attendance
            JOIN persons ON persons.id = attendance.person_id
            WHERE substr(attendance.timestamp, 1, 10) < ?
              AND persons.role IN ('teachers', 'children')
              AND persons.id NOT IN (
                  SELECT person_id
                  FROM deleted_user_archives
                  WHERE person_id IS NOT NULL
              )
              AND attendance.event_type = 'checkin'
              AND NOT EXISTS (
                  SELECT 1
                  FROM attendance AS later
                  WHERE later.person_id = attendance.person_id
                    AND substr(later.timestamp, 1, 10) = substr(attendance.timestamp, 1, 10)
                    AND (
                        later.timestamp > attendance.timestamp
                        OR (later.timestamp = attendance.timestamp AND later.id > attendance.id)
                    )
              )
            ORDER BY day_text
            """,
            (before_day_text,),
        ).fetchall()
    return [row["day_text"] for row in rows if row["day_text"]]


def closeout_teacher_attendance_day(day_text=None):
    day_text = day_text or today_text()
    checkout_timestamp = f"{day_text} {TEACHER_DAILY_CLOSEOUT_TIME}:00"
    with connect_db() as conn:
        people = conn.execute(
            """
            SELECT id, name, role, project_id
            FROM persons
            WHERE role IN ('teachers', 'children')
              AND id NOT IN (SELECT person_id FROM deleted_user_archives WHERE person_id IS NOT NULL)
            ORDER BY project_id, name COLLATE NOCASE
            """
        ).fetchall()
        checkout_count = 0
        for person in people:
            latest = conn.execute(
                """
                SELECT event_type
                FROM attendance
                WHERE person_id = ?
                  AND timestamp LIKE ?
                ORDER BY timestamp DESC, id DESC
                LIMIT 1
                """,
                (person["id"], f"{day_text}%"),
            ).fetchone()
            if not latest or latest["event_type"] != "checkin":
                continue
            conn.execute(
                """
                INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path, source, operator_name)
                VALUES (?, ?, ?, 'checkout', ?, NULL, 'daily_closeout', 'System')
                """,
                (person["id"], person["name"], person["role"], checkout_timestamp),
            )
            attendance_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
            audit(
                conn,
                None,
                "daily_auto_checkout",
                "attendance",
                object_id=person["id"],
                details={
                    "attendance_id": attendance_id,
                    "person_name": person["name"],
                    "role": person["role"],
                    "project_id": person["project_id"],
                    "event_type": "checkout",
                    "timestamp": checkout_timestamp,
                    "source": "daily_closeout",
                    "operator_name": "System",
                },
            )
            checkout_count += 1
        export_path = write_teacher_daily_attendance_export(conn, day_text)
        conn.execute(
            """
            INSERT INTO teacher_daily_closeout(day_text, checkout_count, export_path, completed_at)
            VALUES (?, ?, ?, ?)
            ON CONFLICT(day_text) DO UPDATE SET
                checkout_count = teacher_daily_closeout.checkout_count + excluded.checkout_count,
                export_path = excluded.export_path,
                completed_at = excluded.completed_at
            """,
            (day_text, checkout_count, str(export_path), now_text()),
        )
        audit(
            conn,
            None,
            "daily_closeout",
            "attendance",
            object_id=day_text,
            details={"day": day_text, "checkout_count": checkout_count, "export_path": str(export_path)},
        )
        conn.commit()
    return checkout_count > 0, checkout_count, str(export_path)

def teacher_daily_closeout_worker(stop_event):
    while not stop_event.is_set():
        current = local_now()
        current_day = current.strftime("%Y-%m-%d")
        try:
            missed_days = attendance_days_needing_closeout(current_day)
        except Exception as exc:
            missed_days = []
            print(f"Attendance closeout scan failed: {exc}", file=sys.stderr, flush=True)
        for missed_day in missed_days:
            try:
                closeout_teacher_attendance_day(missed_day)
            except Exception as exc:
                print(f"Attendance closeout failed for {missed_day}: {exc}", file=sys.stderr, flush=True)
        if current.strftime("%H:%M") >= TEACHER_DAILY_CLOSEOUT_TIME:
            try:
                closeout_teacher_attendance_day(current_day)
            except Exception as exc:
                print(f"Attendance closeout failed for {current_day}: {exc}", file=sys.stderr, flush=True)
        stop_event.wait(60)


def resolve_existing_child_photo(photo_path):
    if not photo_path:
        return None
    raw = str(photo_path).strip()
    if not raw:
        return None
    candidates = []
    original = Path(raw)
    candidates.append(original if original.is_absolute() else BASE_DIR / raw)

    file_names = []
    for name in (Path(raw).name, PureWindowsPath(raw).name):
        if name and name not in file_names:
            file_names.append(name)
    for name in file_names:
        candidates.extend(
            [
                CHILDREN_DIR / name,
                DATA_DIR / "children" / name,
                BASE_DIR / "data" / "children" / name,
            ]
        )

    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved.exists() and resolved.is_file():
            return resolved
    return None


def child_card_image_url(photo_path):
    resolved = resolve_existing_child_photo(photo_path)
    if not resolved:
        return None
    return "/media/" + base64.urlsafe_b64encode(str(resolved).encode("utf-8")).decode("ascii").rstrip("=")


def qr_token_image_data_url(token):
    if not token or cv2 is None:
        return None
    try:
        qr_image = cv2.QRCodeEncoder_create().encode(str(token))
        ok, encoded = cv2.imencode(".png", qr_image)
        if not ok:
            return None
    except Exception:
        return None
    return "data:image/png;base64," + base64.b64encode(encoded.tobytes()).decode("ascii")


def child_qr_file_name(value):
    invalid_chars = '<>:"/\\|?*'
    cleaned = "".join("_" if char in invalid_chars else char for char in str(value or "")).strip()
    return cleaned or "child"


def existing_child_qr_image_url(child_name, qr_token=None):
    names = []
    for value in (child_name, (qr_token or "").removeprefix("CHILD:")):
        value = str(value or "").strip()
        if value and value not in names:
            names.append(value)
    if not names:
        return None

    folders = (QR_DIR, BASE_DIR / "data" / "child_qrcodes", BASE_DIR / "child_qrcodes")
    candidate_names = []
    for name in names:
        for file_name in (child_qr_file_name(name), safe_filename(name), name):
            if file_name and file_name not in candidate_names:
                candidate_names.append(file_name)

    for folder in folders:
        for file_name in candidate_names:
            candidate = folder / f"{file_name}.png"
            try:
                resolved = candidate.resolve()
            except OSError:
                continue
            if resolved.exists() and resolved.is_file():
                return "/media/" + file_path_token(resolved)

    wanted = {f"{name}.png".casefold() for name in candidate_names}
    for folder in folders:
        try:
            files = folder.glob("*.png")
        except OSError:
            continue
        for candidate in files:
            if candidate.name.casefold() in wanted:
                return "/media/" + file_path_token(candidate.resolve())
    return None


def qr_gf_tables():
    exp = [0] * 512
    log = [0] * 256
    x = 1
    for i in range(255):
        exp[i] = x
        log[x] = i
        x <<= 1
        if x & 0x100:
            x ^= 0x11D
    for i in range(255, 512):
        exp[i] = exp[i - 255]
    return exp, log


QR_GF_EXP, QR_GF_LOG = qr_gf_tables()


def qr_gf_mul(a, b):
    if not a or not b:
        return 0
    return QR_GF_EXP[QR_GF_LOG[a] + QR_GF_LOG[b]]


def qr_rs_generator(degree):
    coefficients = [0] * (degree - 1) + [1]
    for i in range(degree):
        root = QR_GF_EXP[i]
        for j in range(degree):
            coefficients[j] = qr_gf_mul(coefficients[j], root)
            if j + 1 < degree:
                coefficients[j] ^= coefficients[j + 1]
    return coefficients


def qr_rs_remainder(data, degree):
    generator = qr_rs_generator(degree)
    result = [0] * degree
    for value in data:
        factor = value ^ result[0]
        result = result[1:] + [0]
        for i, coefficient in enumerate(generator):
            result[i] ^= qr_gf_mul(coefficient, factor)
    return result


def qr_append_bits(bits, value, length):
    for i in range(length - 1, -1, -1):
        bits.append((value >> i) & 1)


def qr_draw_finder(matrix, reserved, row, col):
    size = len(matrix)
    for r in range(row - 1, row + 8):
        for c in range(col - 1, col + 8):
            if 0 <= r < size and 0 <= c < size:
                reserved[r][c] = True
                matrix[r][c] = False
    for r in range(row, row + 7):
        for c in range(col, col + 7):
            matrix[r][c] = (
                r in {row, row + 6}
                or c in {col, col + 6}
                or (row + 2 <= r <= row + 4 and col + 2 <= c <= col + 4)
            )


def qr_draw_alignment(matrix, reserved, center_row, center_col):
    for r in range(center_row - 2, center_row + 3):
        for c in range(center_col - 2, center_col + 3):
            reserved[r][c] = True
            matrix[r][c] = max(abs(r - center_row), abs(c - center_col)) != 1


def qr_format_bits(mask):
    value = (1 << 3) | mask
    data = value << 10
    generator = 0x537
    for i in range(14, 9, -1):
        if (data >> i) & 1:
            data ^= generator << (i - 10)
    return ((value << 10) | data) ^ 0x5412


def qr_set_format(matrix, reserved, mask):
    size = len(matrix)
    bits = qr_format_bits(mask)
    positions_a = (
        [(8, i) for i in range(6)]
        + [(8, 7), (8, 8), (7, 8)]
        + [(14 - i, 8) for i in range(9, 15)]
    )
    positions_b = [(size - 1 - i, 8) for i in range(8)] + [(8, size - 15 + i) for i in range(8, 15)]
    for i, (row, col) in enumerate(positions_a):
        matrix[row][col] = bool((bits >> i) & 1)
        reserved[row][col] = True
    for i, (row, col) in enumerate(positions_b):
        matrix[row][col] = bool((bits >> i) & 1)
        reserved[row][col] = True
    matrix[size - 8][8] = True
    reserved[size - 8][8] = True


def qr_reserve_format_areas(reserved):
    size = len(reserved)
    positions = (
        [(8, i) for i in range(6)]
        + [(8, 7), (8, 8), (7, 8)]
        + [(14 - i, 8) for i in range(9, 15)]
        + [(size - 1 - i, 8) for i in range(8)]
        + [(8, size - 15 + i) for i in range(8, 15)]
        + [(size - 8, 8)]
    )
    for row, col in positions:
        reserved[row][col] = True


def qr_make_matrix(text):
    payload = text.encode("utf-8")
    versions = {
        1: (19, 7),
        2: (34, 10),
        3: (55, 15),
        4: (80, 20),
    }
    version = None
    for candidate, (data_capacity, _ecc) in versions.items():
        if len(payload) <= data_capacity - 3:
            version = candidate
            break
    if version is None:
        raise ValueError("QR token is too long")
    data_capacity, ecc_count = versions[version]
    size = 21 + 4 * (version - 1)
    matrix = [[False for _ in range(size)] for _ in range(size)]
    reserved = [[False for _ in range(size)] for _ in range(size)]

    qr_draw_finder(matrix, reserved, 0, 0)
    qr_draw_finder(matrix, reserved, 0, size - 7)
    qr_draw_finder(matrix, reserved, size - 7, 0)
    for i in range(8, size - 8):
        reserved[6][i] = reserved[i][6] = True
        matrix[6][i] = matrix[i][6] = i % 2 == 0
    if version > 1:
        position = 4 * version + 10
        for row in (6, position):
            for col in (6, position):
                if reserved[row][col]:
                    continue
                qr_draw_alignment(matrix, reserved, row, col)
    qr_reserve_format_areas(reserved)

    bits = []
    qr_append_bits(bits, 0b0100, 4)
    qr_append_bits(bits, len(payload), 8)
    for byte in payload:
        qr_append_bits(bits, byte, 8)
    qr_append_bits(bits, 0, min(4, data_capacity * 8 - len(bits)))
    while len(bits) % 8:
        bits.append(0)
    data = []
    for i in range(0, len(bits), 8):
        value = 0
        for bit in bits[i : i + 8]:
            value = (value << 1) | bit
        data.append(value)
    pad = 0xEC
    while len(data) < data_capacity:
        data.append(pad)
        pad = 0x11 if pad == 0xEC else 0xEC
    codewords = data + qr_rs_remainder(data, ecc_count)
    data_bits = []
    for byte in codewords:
        qr_append_bits(data_bits, byte, 8)

    bit_index = 0
    col = size - 1
    upward = True
    while col > 0:
        if col == 6:
            col -= 1
        rows = range(size - 1, -1, -1) if upward else range(size)
        for row in rows:
            for current_col in (col, col - 1):
                if reserved[row][current_col]:
                    continue
                bit = data_bits[bit_index] if bit_index < len(data_bits) else 0
                mask = (row + current_col) % 2 == 0
                matrix[row][current_col] = bool(bit ^ mask)
                bit_index += 1
        upward = not upward
        col -= 2
    qr_set_format(matrix, reserved, 0)
    return matrix


def qr_token_svg(token):
    try:
        matrix = qr_make_matrix(str(token))
    except Exception:
        return ""
    quiet = 4
    size = len(matrix) + quiet * 2
    rects = []
    for row, values in enumerate(matrix):
        for col, value in enumerate(values):
            if value:
                rects.append(f'<rect x="{col + quiet}" y="{row + quiet}" width="1" height="1"/>')
    return (
        f'<svg class="print-qr-svg" viewBox="0 0 {size} {size}" '
        f'xmlns="http://www.w3.org/2000/svg" shape-rendering="crispEdges">'
        f'<rect width="{size}" height="{size}" fill="#fff"/>'
        f'<g fill="#000">{"".join(rects)}</g></svg>'
    )


def file_path_token(path):
    return base64.urlsafe_b64encode(str(Path(path).resolve()).encode("utf-8")).decode("ascii").rstrip("=")


def safe_resolve_media(token):
    try:
        padding = "=" * (-len(token) % 4)
        raw = base64.urlsafe_b64decode(token + padding).decode("utf-8")
        path = Path(raw).resolve()
    except Exception:
        return None
    allowed_roots = [BASE_DIR.resolve(), DATA_DIR.resolve(), CHILDREN_DIR.resolve()]
    for root in allowed_roots:
        try:
            path.relative_to(root)
            return path
        except ValueError:
            continue
    return None


def safe_resolve_user_file(token, owner):
    path = safe_resolve_media(token)
    if not path:
        return None
    folder = ensure_user_folder(owner).resolve()
    try:
        path.relative_to(folder)
    except ValueError:
        return None
    return path


def status_label(status):
    return {"P": "Present", "A": "Absence", "F": "Closed"}.get(status, status)


def header_presence_status(user):
    if not user or not user["person_id"]:
        return ""
    try:
        with connect_db() as conn:
            last = conn.execute(
                """
                SELECT event_type
                FROM attendance
                WHERE person_id = ?
                  AND timestamp LIKE ?
                ORDER BY timestamp DESC, id DESC
                LIMIT 1
                """,
                (user["person_id"], f"{today_text()}%"),
            ).fetchone()
    except sqlite3.Error:
        return ""
    if not last:
        return "Sorti"
    return "Present" if last["event_type"] == "checkin" else "Sorti"


def unread_message_count(user):
    if not user:
        return 0
    try:
        with connect_db() as conn:
            row = conn.execute(
                """
                SELECT COUNT(*) AS unread_count
                FROM internal_messages
                WHERE recipient_user_id = ? AND read_at IS NULL
                """,
                (user["id"],),
            ).fetchone()
        return int(row["unread_count"] or 0) if row else 0
    except sqlite3.Error:
        return 0


def css():
    return """
    <style>
    :root {
      --bg: #eef4f7;
      --panel: #ffffff;
      --panel-soft: #f7fafb;
      --text: #102033;
      --muted: #5f6f7e;
      --line: #d7e2ea;
      --line-strong: #b8c9d6;
      --blue: #2f80c2;
      --green: #20a66a;
      --gray: #657382;
      --amber: #d9901d;
      --red: #d94b5d;
      --nav: #0f3f66;
      --navText: #f7fbff;
      --focus: rgba(47, 128, 194, 0.18);
      --blue-soft: #e7f1fb;
      --green-soft: #e4f6ee;
      --amber-soft: #fff4dc;
      --red-soft: #fdecef;
    }
    * { box-sizing: border-box; }
    body { margin: 0; font-family: "Segoe UI", Arial, sans-serif; background: linear-gradient(180deg, #dfeaf1 0, #eef4f7 260px), var(--bg); color: var(--text); font-size: 14px; line-height: 1.45; }
    a { color: #1e6aa8; text-decoration: none; }
    a:hover { text-decoration: underline; }
    .topbar { position: sticky; top: 0; z-index: 1000; background: linear-gradient(135deg, #0f3f66, #146a7c 58%, #1b8a68); color: var(--navText); padding: 12px 20px; display: flex; align-items: center; justify-content: space-between; gap: 12px; flex-wrap: wrap; box-shadow: 0 10px 28px rgba(15, 63, 102, 0.24); }
    .brand { min-width:0; display:flex; align-items:center; gap:10px; font-size:clamp(17px, 2.2vw, 23px); font-weight:900; letter-spacing:0; white-space:nowrap; color:#ffffff; text-shadow:0 1px 2px rgba(10,32,52,0.22); }
    .brand-logo { width:46px; height:46px; flex:0 0 46px; border-radius:50%; object-fit:cover; background:#fff; border:2px solid rgba(255,255,255,.88); box-shadow:0 3px 10px rgba(10,32,52,.25); }
    .brand-name { min-width:0; overflow:hidden; text-overflow:ellipsis; }
    @keyframes brand-rainbow { from { background-position: 0% 50%; } to { background-position: 240% 50%; } }
    .nav { display: flex; gap: 8px; flex-wrap: wrap; align-items: center; }
    .nav-left { flex: 0 1 auto; }
    .nav-right { flex: 0 1 auto; justify-content: flex-end; }
    .topbar-main { width: 100%; display: flex; align-items: center; justify-content: flex-start; gap: 12px; }
    .topbar-menu-row { width: 100%; display: flex; align-items: center; justify-content: space-between; gap: 12px; }
    .topbar-spacer { flex: 1 1 auto; min-width: 24px; }
    .user-info { white-space: nowrap; }
    .topbar-left-actions { display: inline-flex; align-items: center; gap: 4px; flex: 0 0 auto; }
    .menu-toggle, .back-toggle { width: 40px; height: 40px; border: 0; border-radius: 6px; background: rgba(255,255,255,0.16); color: var(--navText); line-height: 1; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; }
    .menu-toggle { font-size: 24px; }
    .back-toggle { font-size: 26px; font-weight: 800; }
    .menu-toggle:hover, .back-toggle:hover { background: rgba(255,255,255,0.28); }
    .account-toggle { border: 1px solid rgba(255,255,255,0.26); border-radius: 6px; background: rgba(255,255,255,0.16); color: var(--navText); min-height: 40px; max-width: min(100%, calc(100vw - 24px)); padding: 7px 11px; cursor: pointer; font-weight: 700; display: inline-flex; align-items: center; gap: 10px; }
    .account-toggle span:first-child { min-width: 0; overflow-wrap: anywhere; }
    .account-toggle .menu-mark { font-size: 24px; line-height: 1; }
    .nav-unread { position: relative; width: fit-content !important; min-width: 0 !important; padding-right: 18px !important; }
    .nav-unread::after { content: ""; position: absolute; top: 8px; right: 4px; width: 9px; height: 9px; border-radius: 50%; background: #dc2626; box-shadow: 0 0 0 2px #fff; }
    .floating-overlay { position: fixed; inset: 0; z-index: 2100; display: none; background: rgba(17,24,39,0.30); }
    .floating-overlay.show { display: block; }
    .side-drawer { position: fixed; top: 12px; left: 12px; max-height: calc(100vh - 24px); width: max-content; min-width: 0; max-width: calc(100vw - 24px); z-index: 2200; display: none; overflow-y: auto; background: #fff; border: 1px solid var(--line); border-radius: 10px; box-shadow: 0 22px 60px rgba(15,23,42,0.28); padding: 8px; }
    .side-drawer.show { display: block; }
    .side-drawer .nav { display: grid; grid-template-columns: max-content; gap: 4px; width: max-content; max-width: 100%; }
    .side-drawer .nav a, .side-drawer .nav button { width: max-content; max-width: calc(100vw - 48px); justify-content: flex-start; text-align: left; background: #fff; border: 0; color: var(--text); min-height: 46px; font-size: 15px; padding: 10px 12px; white-space: nowrap; }
    .side-drawer .nav a:hover, .side-drawer .nav button:hover { background: var(--blue-soft); }
    .account-popover { position: fixed; top: 62px; right: max(8px, env(safe-area-inset-right)); left: auto; max-height: calc(100vh - 76px); width: max-content; min-width: 0; max-width: calc(100vw - 16px); z-index: 2200; display: none; overflow-y: auto; overflow-x: hidden; background: #fff; border: 1px solid var(--line); border-radius: 10px; box-shadow: 0 20px 54px rgba(15,23,42,0.24); padding: 8px; }
    .account-popover.show { display: block; }
    .account-popover .nav { display: grid; grid-template-columns: max-content; gap: 4px; width: max-content; max-width: 100%; }
    .account-popover .nav a, .account-popover .nav button { width: max-content; max-width: calc(100vw - 40px); justify-content: flex-start; text-align: left; min-height: 44px; background: #fff; border: 0; color: var(--text); padding: 10px 12px; white-space: nowrap; }
    .account-popover .nav a:hover, .account-popover .nav button:hover { background: var(--blue-soft); }
    .nav a, .nav button { color: var(--navText); background: rgba(255,255,255,0.16); border: 1px solid rgba(255,255,255,0.26); padding: 7px 11px; border-radius: 6px; cursor: pointer; font-size: 13px; text-decoration: none; transition: background 120ms ease, border-color 120ms ease, box-shadow 120ms ease; }
    .nav a:hover, .nav button:hover { background: rgba(255,255,255,0.28); border-color: rgba(255,255,255,0.42); text-decoration: none; }
    .nav a.nav-attendance { font-weight: 800; }
    .wrap { max-width: 1600px; margin: 0 auto; padding: 20px; }
    .grid { display: grid; gap: 16px; }
    .two-col { grid-template-columns: minmax(0, 1.7fr) minmax(360px, 1fr); align-items: start; }
    .panel { background: var(--panel); border: 1px solid var(--line); border-radius: 8px; padding: 16px; box-shadow: 0 12px 28px rgba(16, 55, 82, 0.08); }
    .panel h2, .panel h3 { margin: 0 0 10px; font-size: 18px; line-height: 1.25; }
    .muted { color: var(--muted); }
    .stats { display: grid; grid-template-columns: repeat(auto-fit, 108px); justify-content: start; gap: 8px; margin-bottom: 10px; }
    .stat { border: 1px solid var(--line); border-radius: 8px; padding: 9px 10px; background: var(--panel-soft); display: flex; align-items: center; justify-content: space-between; gap: 8px; min-height: 40px; white-space: nowrap; }
    .stat .muted { font-size: 11px; font-weight: 600; }
    .stat .value { font-size: 18px; font-weight: 700; margin-top: 0; color: #164f78; }
    .toolbar { display: flex; flex-wrap: wrap; gap: 10px; align-items: end; margin-bottom: 12px; }
    label { display: block; font-size: 12px; color: var(--muted); margin-bottom: 4px; }
    input, select, textarea { width: 100%; border: 1px solid var(--line-strong); border-radius: 6px; padding: 9px 10px; font-size: 14px; background: white; color: var(--text); outline: none; }
    input:focus, select:focus, textarea:focus { border-color: var(--blue); box-shadow: 0 0 0 3px var(--focus); }
    input[type="checkbox"] { width: auto; }
    .btn { display: inline-flex; align-items: center; justify-content: center; gap: 6px; border: 1px solid transparent; border-radius: 6px; padding: 9px 12px; min-height: 38px; font-size: 14px; font-weight: 600; cursor: pointer; background: #e4edf4; color: #10233d; text-decoration: none; white-space: nowrap; transition: filter 120ms ease, box-shadow 120ms ease; }
    .btn:hover { filter: brightness(0.98); text-decoration: none; box-shadow: 0 6px 14px rgba(16, 55, 82, 0.13); }
    .btn.primary { background: var(--blue); border-color: #236fa8; color: #ffffff; }
    .btn.green { background: var(--green); border-color: #188b58; color: #ffffff; }
    .btn.gray { background: #e4edf4; color: #394b59; }
    .btn.red { background: var(--red); border-color: #c63b4e; color: #ffffff; }
    .btn.amber { background: var(--amber); border-color: #c77d12; color: #ffffff; }
    .btn.ghost { background: transparent; border-color: var(--line); }
    .btn-row { display: flex; gap: 8px; flex-wrap: wrap; }
    .action-panel { display: grid; grid-template-columns: max-content; gap: 10px; align-items: start; margin-bottom: 12px; }
    .action-card { border: 1px solid var(--line); border-radius: 8px; background: var(--panel-soft); padding: 10px; }
    .action-panel .action-card { border-width: 0.5px; border-color: #e6ebf2; }
    .dashboard-overview { display: grid; grid-template-columns: minmax(340px, 0.75fr) minmax(0, 1.25fr); gap: 16px; align-items: stretch; }
    .dashboard-charts { display: grid; grid-template-columns: repeat(2, minmax(320px, 1fr)); gap: 16px; }
    .dashboard-chart { min-height: 190px; border: 1px solid var(--line); border-radius: 8px; background: #fbfdff; padding: 10px 12px 8px; }
    .dashboard-chart-head { display: flex; align-items: center; justify-content: space-between; gap: 12px; margin-bottom: 2px; }
    .dashboard-chart-title { font-size: 13px; font-weight: 700; color: #17364f; }
    .dashboard-chart-total { font-size: 12px; font-weight: 700; color: var(--muted); }
    .arrival-chart { width: 100%; height: 170px; display: block; }
    .arrival-chart text { fill: #6d7c8d; font-size: 10px; }
    .chart-grid line { stroke: #dde8ef; stroke-width: 1; }
    .chart-area { fill: rgba(47, 128, 194, 0.14); }
    .chart-line { fill: none; stroke: var(--blue); stroke-width: 2.5; stroke-linecap: round; stroke-linejoin: round; }
    .chart-points { display: none; }
    .chart-points circle { fill: #fff; stroke: var(--blue); stroke-width: 2; }
    .presence-line .chart-area { fill: rgba(32, 166, 106, 0.14); }
    .presence-line .chart-line { stroke: var(--green); }
    .presence-line .chart-points circle { stroke: var(--green); }
    .dashboard-filters { display: grid; grid-template-columns: repeat(2, 150px); gap: 10px; align-items: end; }
    .dashboard-filters input, .dashboard-filters select { border-width: 0.5px; border-color: var(--line); }
    .selected-action-card { display: flex; align-items: center; justify-content: space-between; gap: 12px; flex-wrap: wrap; }
    .dashboard-side { margin-top: 0; }
    .selected-action-meta { min-width: 180px; }
    .action-buttons { display: flex; gap: 8px; flex-wrap: wrap; align-items: center; }
    .action-buttons .btn { min-width: 110px; justify-content: center; }
    .btn:disabled { background: #e7edf5 !important; color: #9aa7b6 !important; border-color: #d6deea !important; cursor: not-allowed; opacity: 1; box-shadow: none; }
    .cards { display: grid; grid-template-columns: repeat(auto-fill, minmax(164px, 1fr)); gap: 8px; }
    .card { border: 1px solid var(--line); border-radius: 8px; overflow: hidden; background: #fff; display: grid; grid-template-columns: 52px minmax(0, 1fr); align-items: center; min-height: 0; padding: 5px; gap: 6px; transition: border-color 120ms ease, box-shadow 120ms ease, transform 120ms ease; }
    .card-link { display: block; color: inherit; text-decoration: none; height: auto; }
    .card-link:hover { text-decoration: none; }
    .card-link:hover .card { border-color: #9bb2c3; box-shadow: 0 8px 18px rgba(16, 55, 82, 0.12); transform: translateY(-1px); }
    .card.present { border-color: #8fd8b5; background: var(--green-soft); }
    .card.absent, .card.checkedout, .card.closed { background: #f7f8fa; color: #8b97a5; }
    .card.closed { background: var(--amber-soft); border-color: #efcf86; }
    .card.selected { outline: 2px solid var(--blue); outline-offset: 1px; border-color: var(--blue); }
    .card.absent .photo, .card.checkedout .photo, .card.closed .photo { filter: grayscale(1) opacity(0.42); }
    .card.absent .name, .card.checkedout .name, .card.closed .name, .card.absent .class-tag, .card.checkedout .class-tag, .card.closed .class-tag, .card.absent .small, .card.checkedout .small, .card.closed .small { color: #8b97a5; }
    .count-strip { display: flex; flex-wrap: wrap; gap: 3px; margin: 0 0 6px; }
    .count-chip { border: 1px solid var(--line); border-radius: 999px; padding: 1px 6px; font-size: 11px; line-height: 1.1; background: #fff; color: var(--muted); }
    .count-chip.strong { color: var(--text); font-weight: 700; }
    .card .photo { width: 48px; height: 48px; background: var(--green-soft); display: flex; align-items: center; justify-content: center; overflow: hidden; padding: 0; border-radius: 50%; }
    .card .photo img { width: 48px; height: 48px; border-radius: 50%; object-fit: cover; display: block; border: 2px solid #c9dfec; background: #e8f5ef; }
    .card .content { padding: 0; display: grid; gap: 2px; min-width: 0; }
    .name { font-weight: 700; line-height: 1.05; font-size: 12px; overflow-wrap: anywhere; }
    .class-tag, .badge { display: inline-flex; width: fit-content; border-radius: 999px; padding: 0 4px; font-size: 10px; line-height: 1; border: 1px solid transparent; }
    .class-tag { margin-top: 0; }
    .badge.present { background: var(--green-soft); color: #0d6b39; }
    .badge.absent { background: #eef2f6; color: #52616e; }
    .badge.closed { background: var(--amber-soft); color: #8b5c00; }
    .badge.checkedout { background: #eef2f6; color: #52616e; }
    .badge.warn { background: var(--red-soft); color: #9f1239; }
    .selected-child-head { display: grid; grid-template-columns: auto 1fr; gap: 10px; align-items: center; margin-bottom: 10px; }
    .selected-child-head img { width: 64px; height: 64px; object-fit: cover; border-radius: 8px; border: 1px solid var(--line); }
    .selected-child-name { font-weight: 700; color: var(--text); }
    .selected-child-head.absent img, .selected-child-head.closed img { filter: grayscale(1) opacity(0.45); }
    .selected-child-head.absent .selected-child-name, .selected-child-head.closed .selected-child-name { color: #8b97a5; }
    .selected-child-head .badge { margin-top: 6px; }
    .child-dashboard { max-width: 560px; }
    .child-dashboard > .panel:first-child { max-width: 560px; }
    .child-dashboard .dashboard-overview { grid-template-columns: minmax(0, 1fr); }
    .child-dashboard .dashboard-side { max-width: 560px; }
    .child-dashboard .selected-child-panel { max-width: 560px; padding: 14px; }
    .selected-child-panel, .mobile-child { scroll-margin-top: 86px; }
    .child-dashboard .selected-child-head { margin-bottom: 8px; }
    .child-dashboard .action-buttons { margin-bottom: 6px !important; }
    .table-wrap { overflow-x: auto; }
    table { width: 100%; border-collapse: collapse; }
    th, td { border-bottom: 1px solid var(--line); padding: 8px 10px; text-align: left; vertical-align: top; font-size: 14px; }
    th { background: var(--panel-soft); position: sticky; top: 0; z-index: 1; color: #4e5d6d; font-weight: 700; }
    tbody tr:hover td { background: #fbfdff; }
    .fiche th, .fiche td { text-align: center; min-width: 42px; }
    .fiche .name-col { text-align: left; min-width: 220px; }
    .fiche .week-col { min-width: 100px; }
    .pill { display: inline-flex; align-items: center; justify-content: center; min-width: 28px; height: 28px; border-radius: 999px; font-weight: 700; }
    .pill.P { background: var(--green-soft); color: #0d6b39; }
    .pill.A { background: #eef2f6; color: #52616e; }
    .pill.F { background: var(--amber-soft); color: #8b5c00; }
    .fiche-calendar { display: grid; gap: 6px; margin-top: 12px; width: min(100%, 560px); min-width: 420px; }
    .fiche-week { display: grid; grid-template-columns: 68px repeat(7, minmax(64px, 1fr)); gap: 5px; align-items: stretch; }
    .fiche-week-label { border: 1px solid #e8edf3; border-radius: 6px; background: #fafbfc; padding: 7px; display: flex; flex-direction: column; justify-content: center; gap: 3px; color: #a2acb8; font-size: 11px; font-weight: 600; }
    .fiche-week-label strong { color: #8f9aa7; font-size: 12px; }
    .fiche-day { min-height: 68px; border: 1px solid #e8edf3; border-radius: 6px; background: #fff; padding: 6px; display: grid; grid-template-rows: auto auto 1fr; gap: 4px; }
    .fiche-day.P, .fiche-day.A, .fiche-day.F { border-color: #e2e8f0; background: #fbfcfd; }
    .fiche-day-name { color: #adb6c1; font-size: 10px; font-weight: 600; text-transform: uppercase; }
    .fiche-day-date { color: #9aa5b1; font-size: 15px; line-height: 1; font-weight: 600; }
    .fiche-day-month { color: #b4bdc8; font-size: 10px; font-weight: 500; }
    .fiche-day .pill { align-self: end; justify-self: start; min-width: 34px; height: 22px; border-radius: 6px; background: transparent; color: #111827; font-size: 15px; font-weight: 900; }
    .fiche-legend { display: flex; flex-wrap: wrap; align-items: center; gap: 8px; margin-top: 10px; color: #9aa5b1; font-size: 12px; }
    .fiche-legend .pill { min-width: 24px; height: 22px; border-radius: 6px; background: transparent; color: #111827; font-size: 14px; font-weight: 900; }
    @media (max-width: 900px) {
      .fiche-calendar { width: 100%; min-width: 0; }
      .fiche-week { grid-template-columns: 42px repeat(7, minmax(0, 1fr)); gap: 2px; }
      .fiche-week-label { padding: 4px 2px; gap: 1px; font-size: 9px; text-align: center; }
      .fiche-week-label strong { font-size: 9px; }
      .fiche-day { min-height: 46px; padding: 3px 2px; gap: 1px; border-radius: 4px; }
      .fiche-day-name { font-size: 8px; }
      .fiche-day-date { font-size: 12px; }
      .fiche-day-month { display: none; }
      .fiche-day .pill { min-width: 20px; height: 18px; font-size: 12px; justify-self: center; }
      .fiche-legend { font-size: 11px; gap: 5px; }
    }
    .login-box { max-width: 420px; margin: 72px auto; background: white; border: 1px solid var(--line); border-radius: 8px; padding: 24px; box-shadow: 0 16px 36px rgba(16, 55, 82, 0.14); }
    .alert { padding: 10px 12px; border-radius: 6px; margin-bottom: 12px; border: 1px solid; font-weight: 600; }
    .alert.info { background: var(--blue-soft); border-color: #b7d5ec; color: #0e3a66; }
    .alert.warn { background: var(--amber-soft); border-color: #efcf86; color: #7a4a00; }
    .alert.error { background: var(--red-soft); border-color: #f0bbc3; color: #921919; }
    .small { font-size: 12px; }
    .auto-hide { display: none !important; }
    .right { text-align: right; }
    .nowrap { white-space: nowrap; }
    .muted-box { padding: 18px; background: #f7f9fc; border: 1px solid var(--line); border-radius: 6px; }
    .user-grid { display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 8px; }
    .file-grid, .mail-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(240px, 1fr)); gap: 10px; }
    .file-card, .mail-card { border: 1px solid var(--line); border-radius: 8px; background: #fff; padding: 10px; }
    .file-card { position: relative; padding-right: 94px; min-height: 92px; }
    .file-card .file-title, .file-card .small { line-height: 1; margin: 0; }
    .file-card .file-title { font-weight: 700; margin-top: 6px; }
    .file-actions { position: absolute; top: 8px; right: 8px; margin-top: 0; }
    .file-action-menu { position: relative; }
    .file-action-menu summary { list-style: none; width: 28px; height: 24px; border: 1px solid var(--line); border-radius: 6px; background: #fff; color: var(--text); cursor: pointer; display: inline-flex; align-items: center; justify-content: center; font-weight: 900; line-height: 1; }
    .file-action-menu summary::-webkit-details-marker { display: none; }
    .file-action-menu summary:hover { background: var(--blue-soft); }
    .file-action-panel { position: absolute; top: 28px; right: 0; z-index: 20; min-width: 108px; display: grid; gap: 4px; padding: 6px; border: 1px solid var(--line); border-radius: 8px; background: #fff; box-shadow: 0 12px 28px rgba(16, 55, 82, 0.16); }
    .file-action-panel .btn { width: 100%; min-height: 28px; padding: 5px 8px; font-size: 12px; line-height: 1; border-radius: 4px; justify-content: flex-start; }
    .file-actions .btn.file-delete { background: #fee2e2; border-color: #fecaca; color: #991b1b; }
    .mail-recipient-layout { display: grid; grid-template-columns: minmax(180px, 1fr) minmax(240px, 1.3fr); gap: 12px; align-items: start; }
    .mail-send-to { min-height: 150px; border: 1px solid var(--line); border-radius: 8px; background: #fff; padding: 8px; display: flex; flex-direction: column; gap: 0; }
    .mail-send-to-empty { color: var(--muted); font-size: 13px; padding: 6px 2px; }
    .mail-recipient-pill { border: 1px solid var(--line); border-radius: 6px; background: #f8fafc; padding: 0 8px; text-align: left; cursor: pointer; font: inherit; line-height: 1.2; color: var(--text); }
    .mail-recipient-pill:hover { background: var(--blue-soft); }
    .mail-target-list { min-height: 150px; max-height: 260px; overflow-y: auto; border: 1px solid var(--line-strong); border-radius: 6px; background: #fff; }
    .mail-target-row, .mail-target-head { display: grid; grid-template-columns: minmax(110px, 0.8fr) minmax(140px, 1.2fr); gap: 10px; align-items: center; width: 100%; padding: 0 10px; border: 0; border-bottom: 1px solid var(--line); background: #fff; color: var(--text); text-align: left; font: inherit; line-height: 1.2; }
    .mail-target-head { position: sticky; top: 0; z-index: 1; background: var(--panel-soft); color: var(--muted); font-size: 12px; font-weight: 700; }
    .mail-target-head button { border: 0; background: transparent; color: inherit; font: inherit; font-weight: 700; padding: 0; text-align: left; cursor: pointer; }
    .mail-target-head button:hover { color: var(--text); text-decoration: underline; }
    .mail-target-row { cursor: pointer; }
    .mail-target-row:hover { background: var(--blue-soft); }
    .mail-target-row span { min-width: 0; overflow-wrap: anywhere; }
    .mail-target-empty { padding: 10px; color: var(--muted); font-size: 13px; }
    .mail-folder-files { max-height: 160px; overflow-y: auto; border: 1px solid var(--line); border-radius: 6px; background: #fff; padding: 6px; display: grid; gap: 4px; }
    .mail-folder-file { display: flex; align-items: center; gap: 7px; min-height: 24px; font-size: 12px; line-height: 1; }
    .mail-folder-file input { margin: 0; }
    .mail-folder-file span { overflow-wrap: anywhere; }
    .profile-form textarea { min-height: 58px; }
    .child-bottom-nav { display: none; }
    @media (max-width: 1180px) { .two-col, .user-grid, .dashboard-overview, .dashboard-charts { grid-template-columns: 1fr; } .dashboard-side { margin-top: 0; } }
    @media (max-width: 720px) {
      body { font-size: 14px; background: var(--bg); }
      .topbar { position: static; padding: 10px 12px; align-items: stretch; }
      .brand { width:100%; font-size:clamp(16px, 5vw, 22px); line-height:1.15; }
      .brand-logo { width:40px; height:40px; flex-basis:40px; }
      .nav { width: 100%; display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 6px; }
      .nav-left, .nav-right { width: 100%; justify-content: stretch; }
      .topbar-spacer { display: none; }
      .user-info { width: 100%; white-space: normal; }
      .side-drawer .nav, .account-popover .nav { display: grid; grid-template-columns: 1fr; }
      .side-drawer, .account-popover { width:max-content; max-width: calc(100vw - 16px); }
      .side-drawer .nav, .account-popover .nav { width:max-content; max-width:100%; grid-template-columns:max-content; }
      .account-popover { top: 64px; right: 8px; }
      .account-toggle { width: auto; max-width: 100%; }
      .nav a, .nav button { width: 100%; min-height: 40px; padding: 8px 8px; text-align: center; font-size: 12px; line-height: 1.15; }
      .side-drawer .nav a, .side-drawer .nav button, .account-popover .nav a, .account-popover .nav button { width:max-content; max-width:calc(100vw - 40px); text-align: left; justify-content: flex-start; font-size: 14px; white-space:nowrap; }
      .topbar .small { width: 100%; font-size: 11px; }
      .wrap { width: 100%; padding: 8px; }
      .panel { padding: 9px; border-radius: 8px; box-shadow: 0 4px 12px rgba(21, 34, 56, 0.04); }
      .panel + .panel { margin-top: 8px !important; }
      .panel h2, .panel h3 { font-size: 16px; margin-bottom: 6px; }
      .grid { gap: 8px; }
      .two-col, .user-grid, .dashboard-overview, .dashboard-charts, .stats-presence-top, .mail-recipient-layout { grid-template-columns: 1fr !important; }
      .toolbar { display: grid; grid-template-columns: 1fr; align-items: stretch; gap: 6px; margin-bottom: 8px; }
      .toolbar > div, .toolbar form, .toolbar .btn, .toolbar button { width: 100%; }
      .btn-row, .action-buttons { display: grid; grid-template-columns: 1fr; gap: 6px; }
      .btn, .action-buttons .btn { width: 100%; min-height: 40px; padding: 8px 10px; white-space: normal; }
      label { margin-bottom: 2px; }
      input, select, textarea { min-height: 40px; font-size: 16px; padding: 7px 9px; }
      textarea { min-height: 86px; }
      .action-panel { margin-bottom: 8px; gap: 6px; }
      .action-card { padding: 8px; }
      .stats { grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 6px; margin-bottom: 6px; }
      .stat { min-height: 46px; align-items: center; padding: 7px 8px; }
      .stat .value { font-size: 17px; }
      .dashboard-filters { grid-template-columns: 1fr; }
      .dashboard-chart { min-height: 146px; padding: 7px; }
      .dashboard-chart-head { margin-bottom: 0; }
      .arrival-chart { height: 124px; }
      .cards { grid-template-columns: 1fr; gap: 6px; }
      .card { grid-template-columns: 52px minmax(0, 1fr); min-height: 62px; padding: 6px; gap: 7px; }
      .card .photo, .card .photo img { width: 50px; height: 50px; }
      .name { font-size: 14px; line-height: 1.15; }
      .class-tag, .badge { font-size: 11px; line-height: 1.15; padding: 2px 6px; }
      .selected-child-head { grid-template-columns: 52px minmax(0, 1fr); gap: 8px; margin-bottom: 6px; }
      .selected-child-head img { width: 52px; height: 52px; }
      .selected-child-name { font-size: 16px; overflow-wrap: anywhere; }
      .child-dashboard, .child-dashboard > .panel:first-child, .child-dashboard .dashboard-side, .child-dashboard .selected-child-panel { max-width: none; }
      .table-wrap { overflow-x: auto; -webkit-overflow-scrolling: touch; }
      table { min-width: 640px; }
      th, td { padding: 6px 7px; font-size: 13px; }
      .stats-calendar-wrap { max-width: none !important; }
      .stats-calendar { margin-top: 4px; }
      .stats-calendar table { min-width: 0; }
      .fiche-calendar { width: 100%; min-width: 0; gap: 3px; }
      .fiche-week { grid-template-columns: 32px repeat(7, minmax(0, 1fr)); gap: 1px; }
      .fiche-week-label { flex-direction: column; justify-content: center; align-items: center; padding: 2px 1px; gap: 1px; font-size: 8px; text-align: center; }
      .fiche-week-label strong { font-size: 8px; line-height: 1; }
      .fiche-week-label span { font-size: 7px; line-height: 1.05; }
      .fiche-day { min-height: 39px; padding: 2px 1px; gap: 1px; border-radius: 4px; }
      .fiche-day-name { font-size: 7px; line-height: 1; }
      .fiche-day-date { font-size: 11px; }
      .fiche-day-month { display: none; }
      .fiche-day .pill { min-width: 16px; height: 15px; font-size: 10px; justify-self: center; align-self: end; }
      .fiche-legend { gap: 5px; margin-top: 6px; }
      .file-grid, .mail-grid { grid-template-columns: 1fr; }
      .file-card, .mail-card { padding: 8px; min-height: 0; }
      .file-actions { top: 8px; right: 8px; }
      .mail-folder-files { max-height: 120px; }
      .mail-target-list, .mail-send-to { min-height: 96px; max-height: 180px; }
      .mail-target-row, .mail-target-head { grid-template-columns: minmax(92px, 0.9fr) minmax(110px, 1.1fr); gap: 6px; padding: 6px 8px; }
      body.child-mobile-nav { padding-bottom: 76px; }
      body.child-mobile-nav .topbar-menu-row { display: none; }
      body.child-mobile-nav .topbar { position: sticky; top: 0; padding: 12px; }
      body.child-mobile-nav .brand { text-align: center; font-size: 18px; line-height: 1.2; }
      body.child-mobile-nav .account-popover { top: auto; right: 8px; bottom: calc(72px + env(safe-area-inset-bottom)); width: min(220px, calc(100vw - 16px)); max-height: min(360px, calc(100vh - 96px)); }
      body.child-mobile-nav .child-desktop-only { display: none !important; }
      body.child-mobile-nav .child-mobile-mail-history { display: none !important; }
      body.staff-mobile-nav .child-mobile-mail-history { display: none !important; }
      .child-bottom-nav { position: fixed; left: 0; right: 0; bottom: 0; z-index: 1800; display: grid; grid-template-columns: repeat(5, 1fr); gap: 0; background: rgba(255,255,255,0.98); border-top: 1px solid var(--line); box-shadow: 0 -8px 24px rgba(16,55,82,0.12); padding: 5px 6px calc(5px + env(safe-area-inset-bottom)); }
      .child-bottom-nav a, .child-bottom-nav button { min-width: 0; width: 100%; min-height: 54px; border: 0; background: transparent; color: #707b86; text-decoration: none; display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 3px; font: inherit; cursor: pointer; padding: 4px 2px; }
      .child-bottom-nav a:hover, .child-bottom-nav button:hover { text-decoration: none; color: var(--blue); }
      .child-bottom-nav .nav-icon { font-size: 22px; line-height: 1; }
      .child-bottom-nav .nav-label { font-size: 11px; line-height: 1.05; font-weight: 700; overflow-wrap: anywhere; }
      .child-bottom-nav .active { color: #f97316; }
      .login-box { margin: 18px auto; padding: 14px; }
      .muted-box { padding: 9px; }
      .alert { padding: 8px 9px; margin-bottom: 8px; }
      .count-strip { margin-bottom: 4px; }
      .small { font-size: 11px; }
      code { white-space: pre-wrap; overflow-wrap: anywhere; }
    }
    @media (max-width: 520px) {
      .topbar { align-items: stretch; }
      .brand { width: 100%; }
      .nav { width: 100%; gap: 6px; }
      .side-drawer .nav, .account-popover .nav { width:max-content; }
      .nav-left, .nav-right { width: 100%; }
      .nav a, .nav button { flex: 1 1 auto; text-align: center; }
      .wrap { padding: 8px; }
      .panel { padding: 9px; }
      .stats { grid-template-columns: repeat(2, minmax(0, 1fr)); }
      .cards { grid-template-columns: 1fr; }
      .action-panel { grid-template-columns: 1fr; }
      .dashboard-filters { grid-template-columns: 1fr; }
      .mail-recipient-layout { grid-template-columns: 1fr; }
    }
    .wait-overlay {
      position: fixed;
      inset: 0;
      z-index: 9999;
      display: none;
      align-items: center;
      justify-content: center;
      padding: 20px;
      background: rgba(246, 248, 251, 0.72);
      backdrop-filter: blur(2px);
    }
    .wait-overlay.show { display: flex; }
    .wait-box {
      width: min(360px, 100%);
      border: 1px solid var(--line);
      border-radius: 8px;
      background: #fff;
      box-shadow: 0 18px 44px rgba(21, 34, 56, 0.18);
      padding: 18px;
      display: grid;
      grid-template-columns: 34px 1fr;
      gap: 12px;
      align-items: center;
    }
    .wait-spinner {
      width: 28px;
      height: 28px;
      border: 3px solid #dbe7f5;
      border-top-color: var(--blue);
      border-radius: 50%;
      animation: wait-spin 0.8s linear infinite;
    }
    .wait-title { font-weight: 700; }
    .wait-text { color: var(--muted); font-size: 13px; margin-top: 2px; }
    .btn.busy { pointer-events: none; opacity: 0.82; }
    @keyframes wait-spin { to { transform: rotate(360deg); } }
    @media print { .topbar, .no-print { display: none !important; } body { background: white; } .wrap { max-width: none; padding: 0; } .panel { border: none; box-shadow: none; } }
    </style>
    """

def html_page(title, user, body, flash=None):
    nav_left = []
    nav_right = []
    child_bottom_nav = ""
    body_classes = []
    if user:
        nav_left.append('<a href="/dashboard">Tableau enfants</a>')
        if user["role"] == "children":
            nav_left.append('<a href="/agenda">Agenda</a>')
        else:
            if user["role"] != "cook":
                nav_left.append('<a href="/agenda">Agenda</a>')
            nav_left.append('<a href="/calendar">Calendrier</a>')
            nav_left.append('<a href="/allergic-children">Enfants Allergiques</a>')
        if user["role"] in STAFF_MOBILE_ATTENDANCE_ROLES:
            nav_left.append('<a href="/teacher-attendance">Présences éducatrices</a>')
        if user["role"] in {"principal", "boss", "teacher", "cook"}:
            nav_left.append('<a href="/contacts">Contacts</a>')
            nav_left.append('<a href="/reports">Fiche 4 semaines</a>')
        if user["role"] in MANAGE_CLOSED_DATES_ROLES:
            nav_left.append('<a href="/closed-dates">Dates fermées</a>')
        if user["role"] in MANAGE_USERS_ROLES:
            nav_left.append('<a href="/users">Inviter</a>')
            nav_left.append('<a href="/account">Account</a>')
        if user["role"] == "boss":
            nav_left.append('<a href="/mobile-invitations#work-location">Lieu travail mobile</a>')
        if is_main_project_boss(user):
            nav_left.append('<a href="/login-page-content">Page connexion</a>')
        if is_super_admin(user):
            nav_left.append('<a href="/projects">Project</a>')
        if user["role"] != "children":
            nav_right.append('<a class="nav-attendance" href="/mobile">Présence</a>')
        nav_right.append('<a href="/profile">Profil</a>')
        message_class = ' class="nav-unread"' if unread_message_count(user) > 0 else ""
        if user["role"] != "children":
            nav_right.append('<a href="/files">Fichiers</a>')
            nav_right.append(f'<a{message_class} href="/mail">Message</a>')
        else:
            child_message_class = ' class="child-desktop-only nav-unread"' if unread_message_count(user) > 0 else ' class="child-desktop-only"'
            nav_right.append('<a class="child-desktop-only" href="/files">Fichiers</a>')
            nav_right.append(f'<a{child_message_class} href="/mail">Message</a>')
        nav_right.append('<a href="/password-change">Mot de passe</a>')
        if can_view_audit_logs(user):
            nav_right.append('<a href="/audit">Journaux</a>')
        nav_right.append(f'<form method="post" action="/logout" style="display:inline"><button type="submit">Déconnexion</button></form>')
        if user["role"] in STAFF_MOBILE_ATTENDANCE_ROLES and user["role"] != "boss":
            body_classes.append("staff-mobile-nav")
        if user["role"] == "children":
            body_classes.append("child-mobile-nav")
            bottom_message_class = " nav-unread" if unread_message_count(user) > 0 else ""
            child_bottom_nav = f"""
      <nav class="child-bottom-nav" aria-label="Child mobile navigation">
        <a href="/mobile" data-bottom-path="/mobile"><span class="nav-icon" aria-hidden="true">⌂</span><span class="nav-label">Tableau</span></a>
        <a href="/agenda" data-bottom-path="/agenda"><span class="nav-icon" aria-hidden="true">◷</span><span class="nav-label">Agenda</span></a>
        <a href="/files" data-bottom-path="/files"><span class="nav-icon" aria-hidden="true">▣</span><span class="nav-label">Fichiers</span></a>
        <a class="{bottom_message_class.strip()}" href="/mail" data-bottom-path="/mail"><span class="nav-icon" aria-hidden="true">✉</span><span class="nav-label">Message</span></a>
        <button type="button" data-menu-open="account-menu"><span class="nav-icon" aria-hidden="true">☰</span><span class="nav-label">Menu</span></button>
      </nav>
      <script>
      (function() {{
        const path = window.location.pathname || '/dashboard';
        document.querySelectorAll('.child-bottom-nav [data-bottom-path]').forEach(function(item) {{
          const target = item.getAttribute('data-bottom-path');
          if (path === target || (target === '/mobile' && (path === '/' || path === '/dashboard'))) item.classList.add('active');
        }});
      }})();
      </script>
            """
    body_class = f' class="{html.escape(" ".join(body_classes))}"' if body_classes else ""
    header = ""
    if user:
        brand_name, brand_logo_url = current_project_brand(user)
        brand_logo_html = f'<img class="brand-logo" src="{html.escape(brand_logo_url, quote=True)}" alt="">' if brand_logo_url else ""
        presence_text = header_presence_status(user)
        presence_html = f" &middot; {html.escape(presence_text)}" if presence_text else ""
        header = f"""
        <div class="topbar">
          <div class="topbar-main">
            <div class="brand">{brand_logo_html}<span class="brand-name">{html.escape(brand_name)}</span></div>
          </div>
          <div class="topbar-menu-row">
            <div class="topbar-left-actions">
              <button class="menu-toggle" type="button" data-menu-open="main-menu" aria-label="Menu">☰</button>
              <button class="back-toggle" type="button" data-back-button aria-label="Retour" title="Retour">←</button>
            </div>
            <button class="account-toggle" type="button" data-menu-open="account-menu"><span>{html.escape(user['display_name'])} &middot; {ROLE_LABELS.get(user['role'], user['role'])}{presence_html}</span><span class="menu-mark" aria-hidden="true">☰</span></button>
          </div>
        </div>
        <div class="floating-overlay" data-menu-close></div>
        <div class="side-drawer" id="main-menu" aria-hidden="true">
          <div class="nav nav-left">
            {''.join(nav_left)}
          </div>
        </div>
        <div class="account-popover" id="account-menu" aria-hidden="true">
          <div class="nav nav-right">
            {''.join(nav_right)}
          </div>
        </div>
        <script>
        (function() {{
          document.querySelectorAll('[data-back-button]').forEach(function(button) {{
            button.addEventListener('click', function() {{
              let sameOriginReferrer = false;
              try {{
                sameOriginReferrer = Boolean(document.referrer) && new URL(document.referrer).origin === window.location.origin;
              }} catch (_error) {{}}
              if (sameOriginReferrer) window.history.back();
              else window.location.href = '/dashboard';
            }});
          }});
          if (window.__floatingMenusReady) return;
          window.__floatingMenusReady = true;
          function closeMenus() {{
            document.querySelectorAll('.side-drawer.show, .account-popover.show').forEach(function(menu) {{
              menu.classList.remove('show');
              menu.setAttribute('aria-hidden', 'true');
            }});
            document.querySelectorAll('.floating-overlay').forEach(function(overlay) {{
              overlay.classList.remove('show');
            }});
          }}
          document.addEventListener('click', function(event) {{
            const openButton = event.target.closest('[data-menu-open]');
            if (openButton) {{
              const id = openButton.getAttribute('data-menu-open');
              const menu = document.getElementById(id);
              if (!menu) return;
              const wasOpen = menu.classList.contains('show');
              closeMenus();
              if (!wasOpen) {{
                menu.classList.add('show');
                menu.setAttribute('aria-hidden', 'false');
                document.querySelectorAll('.floating-overlay').forEach(function(overlay) {{ overlay.classList.add('show'); }});
              }}
              event.preventDefault();
              return;
            }}
            if (event.target.closest('[data-menu-close]')) {{
              closeMenus();
            }}
          }});
          document.addEventListener('keydown', function(event) {{
            if (event.key === 'Escape') closeMenus();
          }});
        }})();
        </script>
        """
    else:
        header = ""
    alert_html = ""
    if flash:
        level, text = flash
        alert_html = f'<div class="alert {html.escape(level)}">{html.escape(text)}</div>'
    return f"""<!doctype html>
    <html lang="en">
    <head>
      <meta charset="utf-8">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <title>{html.escape(title)}</title>
      <link rel="manifest" href="/manifest.webmanifest?v={PWA_MANIFEST_VERSION}">
      <meta name="theme-color" content="#dff1ff">
      <meta name="application-name" content="">
      <meta name="mobile-web-app-capable" content="yes">
      <meta name="apple-mobile-web-app-capable" content="yes">
      <meta name="apple-mobile-web-app-title" content="">
      <link rel="apple-touch-icon" href="/app-icon.svg">
      {css()}
    </head>
    <body{body_class}>
      {header}
      <div class="wrap">
        {alert_html}
        {body}
      </div>
      {child_bottom_nav}
      <div class="wait-overlay" id="wait-overlay" role="status" aria-live="polite" aria-hidden="true">
        <div class="wait-box">
          <div class="wait-spinner" aria-hidden="true"></div>
          <div>
            <div class="wait-title" id="wait-title">Processing...</div>
            <div class="wait-text" id="wait-text">Please wait. Do not click again.</div>
          </div>
        </div>
      </div>
      <iframe id="wait-download-frame" name="wait-download-frame" style="display:none" title="Download result"></iframe>
      <script>
      (function() {{
        const overlay = document.getElementById('wait-overlay');
        const title = document.getElementById('wait-title');
        const text = document.getElementById('wait-text');
        let activeButton = null;
        let originalButtonText = '';
        let waitTimer = null;
        let downloadPollTimer = null;
        let waitingForDownload = false;
        function hideWait() {{
          if (!overlay) return;
          overlay.classList.remove('show');
          overlay.setAttribute('aria-hidden', 'true');
          if (waitTimer) {{
            window.clearTimeout(waitTimer);
            waitTimer = null;
          }}
          if (downloadPollTimer) {{
            window.clearInterval(downloadPollTimer);
            downloadPollTimer = null;
          }}
          waitingForDownload = false;
          if (activeButton) {{
            activeButton.classList.remove('busy');
            activeButton.removeAttribute('aria-busy');
            if (originalButtonText) activeButton.textContent = originalButtonText;
          }}
          activeButton = null;
          originalButtonText = '';
        }}
        function showWait(message, button) {{
          if (!overlay) return;
          title.textContent = message || 'Processing...';
          text.textContent = 'Please wait. Do not click again.';
          overlay.classList.add('show');
          overlay.setAttribute('aria-hidden', 'false');
          if (button) {{
            activeButton = button;
            originalButtonText = button.textContent;
            button.classList.add('busy');
            button.setAttribute('aria-busy', 'true');
            button.textContent = button.getAttribute('data-wait-text') || message || 'Processing...';
          }}
        }}
        function waitFrame() {{
          let frame = document.getElementById('wait-download-frame');
          if (!frame) {{
            frame = document.createElement('iframe');
            frame.id = 'wait-download-frame';
            frame.name = 'wait-download-frame';
            frame.style.display = 'none';
            frame.title = 'Download result';
            document.body.appendChild(frame);
          }}
          if (frame.getAttribute('data-wait-bound') !== 'true') {{
            frame.addEventListener('load', function() {{
              if (waitingForDownload) hideWait();
            }});
            frame.setAttribute('data-wait-bound', 'true');
          }}
          return frame;
        }}
        function setDownloadToken(form) {{
          const token = String(Date.now()) + String(Math.random()).slice(2);
          let input = form.querySelector('input[name="download_token"]');
          if (!input) {{
            input = document.createElement('input');
            input.type = 'hidden';
            input.name = 'download_token';
            form.appendChild(input);
          }}
          input.value = token;
          return token;
        }}
        function hasDownloadCookie(token) {{
          return document.cookie.split(';').map(function(item) {{ return item.trim(); }}).indexOf('download_done=' + token) !== -1;
        }}
        function clearDownloadCookie() {{
          document.cookie = 'download_done=; Max-Age=0; Path=/; SameSite=Lax';
        }}
        function watchDownloadToken(token) {{
          if (downloadPollTimer) window.clearInterval(downloadPollTimer);
          downloadPollTimer = window.setInterval(function() {{
            if (hasDownloadCookie(token)) {{
              clearDownloadCookie();
              hideWait();
            }}
          }}, 400);
        }}
        const dirtyMessage = 'Vous avez des modifications non enregistrées. Quitter sans enregistrer ?';
        let hasUnsavedChanges = false;
        function isTrackedField(field) {{
          if (!field || !field.form) return false;
          const form = field.form;
          if ((form.getAttribute('method') || 'get').toLowerCase() !== 'post') return false;
          if (form.getAttribute('data-no-dirty') === 'true') return false;
          if (field.closest('[data-no-dirty="true"]')) return false;
          const type = (field.getAttribute('type') || '').toLowerCase();
          return !['hidden', 'submit', 'button', 'reset'].includes(type);
        }}
        document.addEventListener('input', function(event) {{
          if (isTrackedField(event.target)) hasUnsavedChanges = true;
        }}, true);
        document.addEventListener('change', function(event) {{
          if (isTrackedField(event.target)) hasUnsavedChanges = true;
        }}, true);
        document.addEventListener('click', function(event) {{
          if (!hasUnsavedChanges) return;
          const link = event.target.closest('a[href]');
          if (!link) return;
          const href = link.getAttribute('href') || '';
          if (!href || href.charAt(0) === '#' || link.target === '_blank' || link.hasAttribute('download')) return;
          if (!window.confirm(dirtyMessage)) {{
            event.preventDefault();
            event.stopPropagation();
          }} else {{
            hasUnsavedChanges = false;
          }}
        }}, true);
        window.addEventListener('beforeunload', function(event) {{
          if (!hasUnsavedChanges) return;
          event.preventDefault();
          event.returnValue = dirtyMessage;
          return dirtyMessage;
        }});
        async function refreshMessageBadge() {{
          if (!('setAppBadge' in navigator) && !('clearAppBadge' in navigator)) return;
          try {{
            const response = await fetch('/api/messages/unread', {{ credentials: 'same-origin' }});
            if (!response.ok) return;
            const data = await response.json();
            const count = Number(data.unread || 0);
            if (count > 0 && 'setAppBadge' in navigator) {{
              navigator.setAppBadge(count).catch(function() {{}});
            }} else if ('clearAppBadge' in navigator) {{
              navigator.clearAppBadge().catch(function() {{}});
            }}
          }} catch (error) {{}}
        }}
        refreshMessageBadge();
        window.setInterval(refreshMessageBadge, 60000);
        const mutationConfirmSkipActions = new Set(['/login', '/logout', '/projects/switch']);
        function hasOwnConfirmation(form, button) {{
          const inlineSubmit = form.getAttribute('onsubmit') || '';
          const inlineClick = button ? (button.getAttribute('onclick') || '') : '';
          return /confirm\\s*\\(/i.test(inlineSubmit) || /confirm\\s*\\(/i.test(inlineClick) || form.classList.contains('group-hide-form');
        }}
        document.addEventListener('submit', function(event) {{
          if (event.defaultPrevented) return;
          const form = event.target;
          if (!(form instanceof HTMLFormElement)) return;
          const method = ((event.submitter && event.submitter.getAttribute('formmethod')) || form.getAttribute('method') || 'get').toLowerCase();
          if (method !== 'post' || form.getAttribute('data-confirm-submit') === 'false') return;
          const button = event.submitter || form.querySelector('button[type="submit"], input[type="submit"]');
          const rawAction = (button && button.getAttribute('formaction')) || form.getAttribute('action') || window.location.pathname;
          let actionPath = rawAction;
          try {{ actionPath = new URL(rawAction, window.location.href).pathname; }} catch (_error) {{}}
          if (mutationConfirmSkipActions.has(actionPath) || hasOwnConfirmation(form, button)) return;
          const actionText = (actionPath + ' ' + (button ? (button.textContent || button.value || '') : '')).toLowerCase();
          const isDelete = /(delete|supprim|remove|effacer|permanent-delete)/i.test(actionText);
          const message = isDelete
            ? 'Confirmer la suppression ? Cette action sera exécutée après votre confirmation.'
            : 'Confirmer l’enregistrement de ces modifications ?';
          if (!window.confirm(message)) {{
            event.preventDefault();
            event.stopImmediatePropagation();
            return;
          }}
          hasUnsavedChanges = false;
        }}, true);
        document.addEventListener('submit', function(event) {{
          if (event.defaultPrevented) return;
          const form = event.target;
          hasUnsavedChanges = false;
          if (!form || form.getAttribute('data-no-wait') === 'true') return;
          const button = event.submitter || form.querySelector('button[type="submit"], input[type="submit"]');
          const message = form.getAttribute('data-wait-message') || (button && button.getAttribute('data-wait-message')) || 'Processing...';
          const isDownloadWait = form.getAttribute('data-download-wait') === 'true' || (button && button.getAttribute('data-download-wait') === 'true');
          if (isDownloadWait) {{
            form.target = waitFrame().name;
            const downloadToken = setDownloadToken(form);
            clearDownloadCookie();
            watchDownloadToken(downloadToken);
            waitingForDownload = true;
          }}
          window.setTimeout(function() {{
            if (event.defaultPrevented) return;
            showWait(message, button);
          }}, 0);
          waitTimer = window.setTimeout(hideWait, isDownloadWait ? 120000 : 45000);
        }});
        window.addEventListener('pageshow', hideWait);
      }})();
      </script>
    </body>
    </html>"""


def main_project_owner(conn):
    owner = conn.execute(
        """
        SELECT web_users.*
        FROM projects
        JOIN web_users ON web_users.id = projects.owner_user_id
        WHERE projects.id = 1
          AND projects.status <> 'deleted'
          AND web_users.project_id = 1
          AND web_users.role = 'boss'
          AND web_users.is_active = 1
        LIMIT 1
        """
    ).fetchone()
    if owner:
        return owner
    return conn.execute(
        """
        SELECT *
        FROM web_users
        WHERE project_id = 1 AND role = 'boss' AND is_active = 1
        ORDER BY id
        LIMIT 1
        """
    ).fetchone()

def is_main_project_boss(user, conn=None):
    if not user or user["role"] != "boss":
        return False
    try:
        home_project_id = int(user.get("_home_project_id", user["project_id"]) or 1)
    except AttributeError:
        home_project_id = int(user["project_id"] or 1)
    return home_project_id == 1


def get_login_page_text(conn=None):
    owns_connection = conn is None
    if owns_connection:
        conn = connect_db()
    try:
        row = conn.execute("SELECT content_json FROM login_page_content WHERE id = 1").fetchone()
        stored = {}
        if row:
            try:
                stored = json.loads(row["content_json"] or "{}")
            except (TypeError, json.JSONDecodeError):
                stored = {}
        return {
            key: str(stored.get(key, default) or default)
            for key, default in LOGIN_PAGE_TEXT_DEFAULTS.items()
        }
    finally:
        if owns_connection:
            conn.close()


def render_login_page_content_editor(user, query=None, values=None, error=None):
    query = query or {}
    with connect_db() as conn:
        if not is_main_project_boss(user, conn):
            return html_page("Forbidden", user, '<div class="panel">Only main-project boss accounts can edit the login page.</div>')
        content = get_login_page_text(conn)
    if values:
        content.update(values)
    rows = [
        ("brand_kicker", "Description de la marque", "Brand description"),
        ("eyebrow", "Texte d’introduction", "Introduction text"),
        ("benefit_1", "Fonction 1", "Feature 1"),
        ("benefit_2", "Fonction 2", "Feature 2"),
        ("benefit_3", "Fonction 3", "Feature 3"),
        ("benefit_4", "Fonction 4", "Feature 4"),
        ("benefit_5", "Fonction 5", "Feature 5"),
        ("price", "Prix", "Price"),
        ("trial", "Période d’essai gratuit", "Free trial period"),
    ]
    fields_html = "".join(
        f"""
        <div class="login-copy-row">
          <div><label>{html.escape(label_fr)} — Français</label><textarea name="{key}_fr" maxlength="500" required>{html.escape(content[key + '_fr'])}</textarea></div>
          <div><label>{html.escape(label_en)} — English</label><textarea name="{key}_en" maxlength="500" required>{html.escape(content[key + '_en'])}</textarea></div>
        </div>
        """
        for key, label_fr, label_en in rows
    )
    flash = ("info", "Login page text saved successfully.") if query.get("saved", [""])[0] == "1" else None
    body = f"""
    <style>
      .login-copy-form {{ display:grid; gap:14px; }}
      .login-copy-row {{ display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:14px; padding-bottom:14px; border-bottom:1px solid var(--line); }}
      .login-copy-row textarea {{ min-height:82px; resize:vertical; }}
      @media (max-width:760px) {{ .login-copy-row {{ grid-template-columns:1fr; }} }}
    </style>
    <div class="panel">
      <h2>Textes de la page de connexion</h2>
      <div class="muted" style="margin-bottom:16px">Modifiez les présentations en français et en anglais. Les changements apparaîtront sur la page de connexion publique.</div>
      {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
      <form method="post" action="/login-page-content" class="login-copy-form">
        {fields_html}
        <div><button class="btn primary" type="submit">Enregistrer</button></div>
      </form>
    </div>
    """
    return html_page("Page connexion", user, body, flash=flash)


def login_page(error=None, show_project_register=True, contact_sent=False, contact_error=None, contact_values=None):
    login_text = get_login_page_text()
    project_register_html = (
        '<div class="login-register"><span data-fr="Votre garderie n&#39;est pas encore configurée?" data-en="Is your childcare centre not configured yet?">Votre garderie n&#39;est pas encore configurée?</span> <a href="/project/register" data-fr="Créer un espace" data-en="Create a space">Créer un espace</a></div>'
        if show_project_register
        else ""
    )
    desktop_project_register_html = '<div class="login-desktop-register"><span data-fr="VOTRE GARDERIE A BESOIN DE SON ESPACE ?" data-en="DOES YOUR CHILDCARE CENTRE NEED ITS OWN SPACE?">VOTRE GARDERIE A BESOIN DE SON ESPACE ?</span><a href="/project/register" data-fr="CRÉER UN ESPACE" data-en="CREATE A SPACE">CRÉER UN ESPACE</a></div>'
    contact_values = contact_values or {}
    contact_name = html.escape(str(contact_values.get("name", "")), quote=True)
    contact_detail = html.escape(str(contact_values.get("contact", "")), quote=True)
    contact_requirements = html.escape(str(contact_values.get("requirements", "")))
    contact_error_messages = {
        "required": (
            "Veuillez remplir votre nom, vos coordonnées et votre demande.",
            "Please enter your name, contact information and requirements.",
        ),
        "too_long": (
            "Le contenu est trop long. Veuillez raccourcir votre demande.",
            "The content is too long. Please shorten your request.",
        ),
        "rate": (
            "Veuillez patienter quelques secondes avant d’envoyer une autre demande.",
            "Please wait a few seconds before sending another request.",
        ),
        "unavailable": (
            "Le service Contact est temporairement indisponible. Veuillez réessayer plus tard.",
            "Contact is temporarily unavailable. Please try again later.",
        ),
    }
    contact_state_html = ""
    if contact_sent:
        contact_state_html = '<div class="alert info login-contact-state" data-fr="Votre demande a été envoyée. Nous vous contacterons bientôt." data-en="Your request has been sent. We will contact you soon.">Votre demande a été envoyée. Nous vous contacterons bientôt.</div>'
    elif contact_error:
        error_fr, error_en = contact_error_messages.get(contact_error, contact_error_messages["unavailable"])
        contact_state_html = f'<div class="alert error login-contact-state" data-fr="{html.escape(error_fr, quote=True)}" data-en="{html.escape(error_en, quote=True)}">{html.escape(error_fr)}</div>'
    contact_should_open_js = "true" if contact_sent or contact_error else "false"
    body = f"""
    <style>
      .login-home-shell {{ min-height:calc(100vh - 40px); margin:-20px; padding:clamp(18px,3vw,48px); overflow:hidden; position:relative; display:grid; place-items:center; background:#f7f4ed; color:#173b3f; }}
      .login-home-shell::before, .login-home-shell::after {{ content:""; position:absolute; border-radius:999px; pointer-events:none; }}
      .login-home-shell::before {{ width:520px; height:520px; left:-230px; top:-250px; background:rgba(255,190,92,.24); }}
      .login-home-shell::after {{ width:460px; height:460px; right:-210px; bottom:-260px; background:rgba(77,170,151,.20); }}
      .login-home {{ width:min(1220px,100%); min-height:min(760px,calc(100vh - 72px)); position:relative; z-index:1; display:grid; grid-template-columns:minmax(0,1.08fr) minmax(360px,.82fr); overflow:hidden; border:1px solid rgba(23,59,63,.10); border-radius:32px; background:#fff; box-shadow:0 32px 90px rgba(31,67,65,.16); }}
      .login-story {{ position:relative; overflow:hidden; padding:clamp(34px,5vw,76px); display:flex; flex-direction:column; justify-content:space-between; gap:42px; background:linear-gradient(145deg,#194e54 0%,#1f6867 56%,#2f8175 100%); color:#fff; }}
      .login-story::before {{ content:""; position:absolute; width:420px; height:420px; right:-220px; top:-150px; border:70px solid rgba(255,255,255,.07); border-radius:50%; }}
      .login-story::after {{ content:""; position:absolute; width:190px; height:190px; left:-70px; bottom:-75px; border-radius:46% 54% 58% 42%; background:#f3b34e; opacity:.94; transform:rotate(24deg); }}
      .login-story-content, .login-product-preview {{ position:relative; z-index:1; }}
      .login-brand {{ display:flex; align-items:center; gap:14px; margin-bottom:clamp(40px,7vh,82px); }}
      .login-brand img {{ width:58px; height:58px; border-radius:17px; box-shadow:0 10px 24px rgba(0,0,0,.16); }}
      .login-brand-name {{ font-size:19px; line-height:1.05; font-weight:400; letter-spacing:.02em; }}
      .login-brand-kicker {{ margin-top:5px; color:#cde7e2; font-size:11px; font-weight:800; letter-spacing:.14em; text-transform:uppercase; }}
      .login-eyebrow {{ display:inline-flex; align-items:center; gap:8px; margin-bottom:18px; color:#ffe1ad; font-size:12px; font-weight:900; letter-spacing:.12em; text-transform:uppercase; }}
      .login-eyebrow::before {{ content:""; width:28px; height:2px; border-radius:2px; background:#f6bd61; }}
      .login-benefit-list {{ max-width:620px; display:grid; gap:9px; margin-top:22px; }}
      .login-benefit-item {{ display:grid; grid-template-columns:24px minmax(0,1fr); gap:10px; align-items:start; padding:10px 12px; border:1px solid rgba(255,255,255,.16); border-radius:13px; background:rgba(255,255,255,.08); color:#eef9f6; font-size:clamp(13px,1.15vw,15px); line-height:1.42; }}
      .login-benefit-mark {{ display:grid; width:20px; height:20px; place-items:center; margin-top:1px; border-radius:50%; background:rgba(246,189,97,.18); color:#ffd892; font-size:12px; font-weight:900; }}
      .login-story-price {{ max-width:620px; margin-top:15px; color:#ffe1ad; font-size:14px; font-weight:700; letter-spacing:.01em; }}
      .login-product-preview {{ width:min(470px,100%); margin-left:auto; padding:17px; border:1px solid rgba(255,255,255,.20); border-radius:20px; background:rgba(255,255,255,.12); backdrop-filter:blur(7px); box-shadow:0 18px 38px rgba(5,35,38,.18); }}
      .login-preview-head {{ display:flex; align-items:center; justify-content:space-between; gap:12px; margin-bottom:14px; font-size:12px; font-weight:800; }}
      .login-live {{ display:inline-flex; align-items:center; gap:6px; color:#e5f5f0; }}
      .login-live::before {{ content:""; width:8px; height:8px; border-radius:50%; background:#7fe0a9; box-shadow:0 0 0 4px rgba(127,224,169,.16); }}
      .login-preview-grid {{ display:grid; grid-template-columns:repeat(3,1fr); gap:9px; }}
      .login-preview-stat {{ padding:13px 10px; border-radius:14px; background:rgba(255,255,255,.94); color:#173b3f; }}
      .login-preview-stat strong {{ display:block; font-size:25px; line-height:1; }}
      .login-preview-stat small {{ display:block; margin-top:6px; color:#637b7b; font-size:10px; font-weight:800; text-transform:uppercase; }}
      .login-access {{ position:relative; padding:clamp(28px,5vw,74px); display:flex; align-items:center; justify-content:center; background:#fffdf9; }}
      .login-desktop-register {{ margin-top:14px; display:flex; align-items:center; justify-content:center; gap:8px; color:#728280; font-size:10px; font-weight:800; letter-spacing:.035em; text-align:center; }}
      .login-desktop-register a {{ color:#2f80c2; font-size:11px; font-weight:900; letter-spacing:.055em; white-space:nowrap; }}
      .login-card {{ width:min(430px,100%); }}
      .login-language-switch {{ display:flex; justify-content:flex-end; gap:4px; margin-bottom:22px; }}
      .login-language-switch button {{ min-width:42px; min-height:34px; border:1px solid #d4dfdc; border-radius:9px; background:#fff; color:#6a7d7d; font:inherit; font-size:12px; font-weight:900; cursor:pointer; }}
      .login-language-switch button[aria-pressed="true"] {{ border-color:#2f80c2; background:#e7f1fb; color:#1e6aa8; box-shadow:0 0 0 2px rgba(47,128,194,.10); }}
      .login-card-kicker {{ margin-bottom:8px; color:#d77f27; font-size:12px; font-weight:900; letter-spacing:.13em; text-transform:uppercase; }}
      .login-card h2 {{ margin:0; color:#173b3f; font-size:clamp(30px,3vw,42px); line-height:1.05; letter-spacing:-.035em; }}
      .login-card-intro {{ margin:13px 0 28px; color:#6a7d7d; font-size:15px; }}
      .login-form {{ display:grid; gap:17px; }}
      .login-form label {{ display:block; margin-bottom:7px; color:#294e50; font-size:13px; font-weight:800; }}
      .login-form input {{ width:100%; min-height:52px; border:1px solid #d4dfdc; border-radius:13px; background:#fff; padding:12px 14px; color:#173b3f; font-size:16px; transition:border-color .16s,box-shadow .16s; }}
      .login-form input:focus {{ outline:0; border-color:#2d8178; box-shadow:0 0 0 4px rgba(45,129,120,.13); }}
      .login-password {{ position:relative; }}
      .login-password input {{ padding-right:76px; }}
      .login-password-toggle {{ position:absolute; right:7px; top:7px; min-height:38px; border:0; border-radius:9px; background:#edf5f2; color:#286b65; padding:0 10px; font:inherit; font-size:12px; font-weight:800; cursor:pointer; }}
      .login-form-meta {{ display:flex; justify-content:flex-end; margin-top:-4px; font-size:12px; font-weight:700; }}
      .login-submit {{ min-height:54px; margin-top:2px; border:0; border-radius:13px; background:#ef9d3d; color:#173b3f; font:inherit; font-size:15px; font-weight:900; cursor:pointer; box-shadow:0 12px 24px rgba(239,157,61,.28); transition:transform .16s,box-shadow .16s,background .16s; }}
      .login-submit:hover {{ transform:translateY(-1px); background:#f4aa4c; box-shadow:0 15px 28px rgba(239,157,61,.34); }}
      .login-register {{ margin-top:25px; padding-top:20px; border-top:1px solid #e4ebe8; color:#728280; text-align:center; font-size:13px; }}
      .login-register a, .login-form-meta a {{ color:#246e68; font-weight:900; }}
      .login-commercial {{ display:grid; gap:7px; justify-items:center; margin-top:13px; color:#617573; text-align:center; font-size:12px; }}
      .login-contact-open {{ padding:0; border:0; background:transparent; color:#2f80c2; font:inherit; font-size:15px; font-weight:900; text-decoration:underline; text-transform:uppercase; cursor:pointer; }}
      .login-contact-overlay {{ position:fixed; inset:0; z-index:3200; display:flex; align-items:center; justify-content:center; padding:20px; background:rgba(15,35,42,.50); backdrop-filter:blur(3px); }}
      .login-contact-overlay[hidden] {{ display:none; }}
      .login-contact-dialog {{ width:min(620px,100%); max-height:calc(100vh - 40px); overflow-y:auto; position:relative; padding:27px; border:1px solid #c8dfe5; border-radius:18px; background:#fff; color:#173b3f; box-shadow:0 28px 80px rgba(15,35,42,.30); }}
      .login-contact-close {{ position:absolute; top:12px; right:12px; width:34px; height:34px; padding:0; border:0; border-radius:50%; background:#eef4f5; color:#36565c; font-size:22px; line-height:1; cursor:pointer; }}
      .login-contact-dialog h2 {{ margin:0 42px 8px 0; font-size:26px; }}
      .login-contact-intro {{ margin:0 0 17px; color:#617573; line-height:1.5; }}
      .login-contact-form {{ display:grid; gap:13px; }}
      .login-contact-form label {{ display:block; margin-bottom:6px; color:#294e50; font-size:13px; font-weight:800; }}
      .login-contact-form input, .login-contact-form textarea {{ width:100%; border:1px solid #d4dfdc; border-radius:11px; background:#fff; padding:11px 12px; color:#173b3f; font:inherit; }}
      .login-contact-form textarea {{ min-height:130px; resize:vertical; }}
      .login-contact-form input:focus, .login-contact-form textarea:focus {{ outline:0; border-color:#2d8178; box-shadow:0 0 0 4px rgba(45,129,120,.13); }}
      .login-contact-submit {{ min-height:46px; border:0; border-radius:11px; background:#2f80c2; color:#fff; font:inherit; font-weight:900; cursor:pointer; }}
      .login-contact-honeypot {{ position:absolute !important; left:-10000px !important; width:1px !important; height:1px !important; overflow:hidden !important; }}
      @media (max-width:640px) {{ .login-contact-overlay {{ padding:12px; align-items:flex-end; }} .login-contact-dialog {{ max-height:calc(100vh - 24px); padding:23px 17px 18px; border-radius:18px 18px 12px 12px; }} .login-contact-dialog h2 {{ font-size:22px; }} }}
      .login-trust {{ display:flex; justify-content:center; gap:9px; flex-wrap:wrap; margin-top:24px; color:#82908e; font-size:11px; }}
      .login-trust > * {{ color:inherit; }}
      .login-trust > * + *::before {{ content:"•"; margin-right:9px; color:#ef9d3d; }}
      .login-card .alert {{ margin:20px 0; border-radius:12px; }}
      @media (min-width:641px) {{ .login-register {{ display:none; }} }}
      @media (max-width:900px) {{ .login-home {{ grid-template-columns:1fr; min-height:0; }} .login-story {{ padding:34px; gap:30px; }} .login-brand {{ margin-bottom:38px; }} .login-product-preview {{ margin-left:0; }} .login-access {{ padding:42px 28px; }} }}
      @media (max-width:640px) {{ .login-desktop-register {{ display:none; }} .login-home-shell {{ min-height:100vh; margin:-8px; padding:0; place-items:stretch; }} .login-home {{ width:100%; border:0; border-radius:0; box-shadow:none; }} .login-story {{ padding:28px 22px 30px; }} .login-brand {{ margin-bottom:30px; }} .login-brand img {{ width:50px; height:50px; border-radius:14px; }} .login-benefit-list {{ gap:7px; }} .login-benefit-item {{ padding:9px 10px; font-size:12px; }} .login-product-preview {{ padding:13px; }} .login-preview-stat strong {{ font-size:21px; }} .login-access {{ padding:34px 22px 42px; }} }}
    </style>
    <main class="login-home-shell">
      <section class="login-home" aria-label="Connexion PITIT PAS SYSTEM">
        <div class="login-story">
          <div class="login-story-content">
            <div class="login-brand"><img src="/app-icon.svg" alt=""><div><div class="login-brand-name">Pitit pas</div><div class="login-brand-kicker" data-fr="{html.escape(login_text['brand_kicker_fr'], quote=True)}" data-en="{html.escape(login_text['brand_kicker_en'], quote=True)}">{html.escape(login_text['brand_kicker_fr'])}</div></div></div>
            <div class="login-eyebrow" data-fr="{html.escape(login_text['eyebrow_fr'], quote=True)}" data-en="{html.escape(login_text['eyebrow_en'], quote=True)}">{html.escape(login_text['eyebrow_fr'])}</div>
            <div class="login-benefit-list" aria-label="Fonctions principales">
              <div class="login-benefit-item"><span class="login-benefit-mark">✓</span><span data-fr="{html.escape(login_text['benefit_1_fr'], quote=True)}" data-en="{html.escape(login_text['benefit_1_en'], quote=True)}">{html.escape(login_text['benefit_1_fr'])}</span></div>
              <div class="login-benefit-item"><span class="login-benefit-mark">✓</span><span data-fr="{html.escape(login_text['benefit_2_fr'], quote=True)}" data-en="{html.escape(login_text['benefit_2_en'], quote=True)}">{html.escape(login_text['benefit_2_fr'])}</span></div>
              <div class="login-benefit-item"><span class="login-benefit-mark">✓</span><span data-fr="{html.escape(login_text['benefit_3_fr'], quote=True)}" data-en="{html.escape(login_text['benefit_3_en'], quote=True)}">{html.escape(login_text['benefit_3_fr'])}</span></div>
              <div class="login-benefit-item"><span class="login-benefit-mark">✓</span><span data-fr="{html.escape(login_text['benefit_4_fr'], quote=True)}" data-en="{html.escape(login_text['benefit_4_en'], quote=True)}">{html.escape(login_text['benefit_4_fr'])}</span></div>
              <div class="login-benefit-item"><span class="login-benefit-mark">✓</span><span data-fr="{html.escape(login_text['benefit_5_fr'], quote=True)}" data-en="{html.escape(login_text['benefit_5_en'], quote=True)}">{html.escape(login_text['benefit_5_fr'])}</span></div>
            </div>
            <div class="login-story-price" data-fr="{html.escape(login_text['price_fr'] + ' · ' + login_text['trial_fr'], quote=True)}" data-en="{html.escape(login_text['price_en'] + ' · ' + login_text['trial_en'], quote=True)}">{html.escape(login_text['price_fr'] + ' · ' + login_text['trial_fr'])}</div>
          </div>
          <div class="login-product-preview" aria-label="Aperçu des présences">
            <div class="login-preview-head"><span data-fr="Aujourd&#39;hui" data-en="Today">Aujourd&#39;hui</span><span class="login-live" data-fr="Mise à jour en direct" data-en="Live update">Mise à jour en direct</span></div>
            <div class="login-preview-grid"><div class="login-preview-stat"><strong>76</strong><small data-fr="Présents" data-en="Present">Présents</small></div><div class="login-preview-stat"><strong>4</strong><small data-fr="Absents" data-en="Absent">Absents</small></div><div class="login-preview-stat"><strong>9</strong><small data-fr="Groupes" data-en="Groups">Groupes</small></div></div>
          </div>
        </div>
        <div class="login-access">
          <div class="login-card">
            <div class="login-language-switch" role="group" aria-label="Language / Langue"><button type="button" data-language-choice="fr" aria-pressed="true">FR</button><button type="button" data-language-choice="en" aria-pressed="false">EN</button></div>
            <div class="login-card-kicker" data-fr="Espace sécurisé" data-en="Secure access">Espace sécurisé</div><h2 data-fr="Bienvenue" data-en="Welcome">Bienvenue</h2><p class="login-card-intro" data-fr="Connectez-vous pour accéder à votre garderie." data-en="Sign in to access your childcare centre.">Connectez-vous pour accéder à votre garderie.</p>
            {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
            <form method="post" action="/login" class="login-form">
              <div><label for="login-username" data-fr="Nom d&#39;utilisateur" data-en="Username">Nom d&#39;utilisateur</label><input id="login-username" name="username" autocomplete="username" data-placeholder-fr="Votre nom d&#39;utilisateur" data-placeholder-en="Your username" placeholder="Votre nom d&#39;utilisateur" autofocus required></div>
              <div><label for="login-password" data-fr="Mot de passe" data-en="Password">Mot de passe</label><div class="login-password"><input id="login-password" name="password" type="password" autocomplete="current-password" data-placeholder-fr="Votre mot de passe" data-placeholder-en="Your password" placeholder="Votre mot de passe" required><button class="login-password-toggle" type="button" data-password-toggle data-fr="Afficher" data-en="Show" data-hide-fr="Masquer" data-hide-en="Hide" aria-label="Afficher le mot de passe">Afficher</button></div></div>
              <button class="login-submit" type="submit" data-fr="Se connecter" data-en="Sign in">Se connecter</button>
            </form>
            {desktop_project_register_html}
            {project_register_html}
            <div class="login-commercial">
              <button class="login-contact-open" type="button" data-contact-open data-fr="Contact" data-en="Contact">Contact</button>
            </div>
            <div class="login-trust"><span data-fr="Support bilingue" data-en="Bilingual support">Support bilingue</span><span data-fr="Accès sur mobile" data-en="Mobile access">Accès sur mobile</span><span data-fr="Données protégées" data-en="Protected data">Données protégées</span><a href="/privacy" data-fr="Politique de confidentialité" data-en="Privacy policy">Politique de confidentialité</a></div>
          </div>
        </div>
      </section>
      <div class="login-contact-overlay" id="login-contact-overlay" role="dialog" aria-modal="true" aria-labelledby="login-contact-title" hidden>
        <div class="login-contact-dialog">
          <button class="login-contact-close" type="button" data-contact-close data-aria-fr="Fermer" data-aria-en="Close" aria-label="Fermer">&times;</button>
          <h2 id="login-contact-title" data-fr="Contactez-nous" data-en="Contact us">Contactez-nous</h2>
          <p class="login-contact-intro" data-fr="Décrivez vos besoins. Votre demande sera envoyée au responsable principal." data-en="Tell us what you need. Your request will be sent to the main administrator.">Décrivez vos besoins. Votre demande sera envoyée au responsable principal.</p>
          {contact_state_html}
          <form method="post" action="/contact" class="login-contact-form">
            <input type="hidden" name="language" id="contact-language" value="fr">
            <div class="login-contact-honeypot" aria-hidden="true"><label>Website<input name="website" tabindex="-1" autocomplete="off"></label></div>
            <div><label for="contact-name" data-fr="Nom" data-en="Name">Nom</label><input id="contact-name" name="name" value="{contact_name}" maxlength="120" autocomplete="name" required></div>
            <div><label for="contact-detail" data-fr="E-mail ou téléphone" data-en="Email or phone">E-mail ou téléphone</label><input id="contact-detail" name="contact" value="{contact_detail}" maxlength="200" autocomplete="email" required></div>
            <div><label for="contact-requirements" data-fr="Vos besoins" data-en="Your requirements">Vos besoins</label><textarea id="contact-requirements" name="requirements" maxlength="4000" data-placeholder-fr="Décrivez votre garderie et les fonctions dont vous avez besoin." data-placeholder-en="Describe your childcare centre and the features you need." placeholder="Décrivez votre garderie et les fonctions dont vous avez besoin." required>{contact_requirements}</textarea></div>
            <button class="login-contact-submit" type="submit" data-fr="Envoyer la demande" data-en="Send request">Envoyer la demande</button>
          </form>
        </div>
      </div>
    </main>
    <script>
    (function() {{
      const root = document.querySelector('.login-home');
      const passwordToggle = document.querySelector('[data-password-toggle]');
      const passwordInput = document.getElementById('login-password');
      const contactOverlay = document.getElementById('login-contact-overlay');
      const contactNameInput = document.getElementById('contact-name');
      const contactLanguageInput = document.getElementById('contact-language');
      const contactShouldOpen = {contact_should_open_js};
      let currentLanguage = 'fr';

      function updatePasswordLabel() {{
        if (!passwordToggle || !passwordInput) return;
        const prefix = passwordInput.type === 'password' ? 'data-' : 'data-hide-';
        const label = passwordToggle.getAttribute(prefix + currentLanguage) || '';
        passwordToggle.textContent = label;
        passwordToggle.setAttribute('aria-label', label);
      }}

      function setLanguage(language) {{
        currentLanguage = language === 'en' ? 'en' : 'fr';
        if (root) root.setAttribute('data-language', currentLanguage);
        document.documentElement.lang = currentLanguage;
        document.title = currentLanguage === 'en' ? 'Sign in' : 'Connexion';
        document.querySelectorAll('[data-fr][data-en]').forEach(function(element) {{
          element.textContent = element.getAttribute('data-' + currentLanguage) || '';
        }});
        document.querySelectorAll('[data-placeholder-fr][data-placeholder-en]').forEach(function(element) {{
          element.placeholder = element.getAttribute('data-placeholder-' + currentLanguage) || '';
        }});
        document.querySelectorAll('[data-aria-fr][data-aria-en]').forEach(function(element) {{
          element.setAttribute('aria-label', element.getAttribute('data-aria-' + currentLanguage) || '');
        }});
        if (contactLanguageInput) contactLanguageInput.value = currentLanguage;
        document.querySelectorAll('[data-language-choice]').forEach(function(button) {{
          button.setAttribute('aria-pressed', button.getAttribute('data-language-choice') === currentLanguage ? 'true' : 'false');
        }});
        try {{ window.localStorage.setItem('pititpas-language', currentLanguage); }} catch (_error) {{}}
        updatePasswordLabel();
      }}

      document.querySelectorAll('[data-language-choice]').forEach(function(button) {{
        button.addEventListener('click', function() {{ setLanguage(button.getAttribute('data-language-choice')); }});
      }});

      if (passwordToggle && passwordInput) {{
        passwordToggle.addEventListener('click', function() {{
          passwordInput.type = passwordInput.type === 'password' ? 'text' : 'password';
          updatePasswordLabel();
        }});
      }}

      function openContact() {{
        if (!contactOverlay) return;
        contactOverlay.hidden = false;
        window.setTimeout(function() {{ if (contactNameInput) contactNameInput.focus(); }}, 0);
      }}
      function closeContact() {{
        if (contactOverlay) contactOverlay.hidden = true;
      }}
      document.querySelectorAll('[data-contact-open]').forEach(function(button) {{
        button.addEventListener('click', openContact);
      }});
      document.querySelectorAll('[data-contact-close]').forEach(function(button) {{
        button.addEventListener('click', closeContact);
      }});
      if (contactOverlay) {{
        contactOverlay.addEventListener('click', function(event) {{ if (event.target === contactOverlay) closeContact(); }});
      }}
      document.addEventListener('keydown', function(event) {{
        if (event.key === 'Escape' && contactOverlay && !contactOverlay.hidden) closeContact();
      }});

      let savedLanguage = '';
      try {{ savedLanguage = window.localStorage.getItem('pititpas-language') || ''; }} catch (_error) {{}}
      setLanguage(savedLanguage === 'en' ? 'en' : 'fr');
      if (contactShouldOpen) openContact();
    }})();
    </script>
    """
    return html_page("Connexion", None, body)

def render_privacy_policy():
    contact_name, contact_email = configured_privacy_contact()
    contact_name_html = html.escape(contact_name or "À configurer / To be configured")
    if contact_email:
        contact_email_html = f'<a href="mailto:{html.escape(contact_email, quote=True)}">{html.escape(contact_email)}</a>'
    else:
        contact_email_html = "À configurer / To be configured"
    body = f"""
    <style>
      .privacy-shell {{ max-width:980px; margin:0 auto; }}
      .privacy-toolbar {{ display:flex; justify-content:space-between; align-items:center; gap:12px; margin-bottom:16px; }}
      .privacy-language {{ display:flex; gap:6px; }}
      .privacy-language button {{ min-width:44px; min-height:36px; border:1px solid var(--line-strong); border-radius:9px; background:#fff; font-weight:800; cursor:pointer; }}
      .privacy-language button[aria-pressed="true"] {{ border-color:#2f80c2; background:#e7f1fb; color:#1e6aa8; }}
      .privacy-article h1 {{ margin-top:0; }}
      .privacy-article h2 {{ margin-top:24px; font-size:20px; }}
      .privacy-article p, .privacy-article li {{ line-height:1.65; }}
      .privacy-note {{ padding:12px 14px; border-radius:10px; background:#fff8e8; color:#72551c; }}
      .privacy-contact {{ padding:14px; border-radius:12px; background:#eef7f5; }}
    </style>
    <div class="privacy-shell">
      <div class="privacy-toolbar">
        <a class="btn ghost" href="/" data-privacy-back>← Connexion</a>
        <div class="privacy-language" role="group" aria-label="Language / Langue">
          <button type="button" data-privacy-language="fr" aria-pressed="true">FR</button>
          <button type="button" data-privacy-language="en" aria-pressed="false">EN</button>
        </div>
      </div>
      <div class="panel privacy-article" data-privacy-article="fr">
        <h1>Politique de confidentialité</h1>
        <p class="muted">PITIT PAS SYSTEM · Dernière mise à jour : {PRIVACY_POLICY_UPDATED}</p>
        <p class="privacy-note">Cette politique décrit les pratiques de PITIT PAS SYSTEM. La garderie ou l’organisation qui vous donne accès au service demeure votre premier point de contact pour les renseignements qu’elle gère.</p>
        <h2>1. Renseignements traités</h2>
        <ul>
          <li>Comptes, noms, rôles, coordonnées et informations de groupe;</li>
          <li>Renseignements sur les enfants et le personnel, présences, heures d’arrivée et de départ;</li>
          <li>Allergies, besoins alimentaires, calendriers, messages, fichiers et notes transmis dans le service;</li>
          <li>Identifiant d’appareil, adresse IP, journaux de connexion et d’activité;</li>
          <li>Position GPS et photo de la caméra frontale uniquement lors de la validation d’une présence mobile du personnel.</li>
        </ul>
        <h2>2. Finalités</h2>
        <p>Ces renseignements servent à gérer les comptes et les accès, enregistrer les présences, organiser le personnel, les repas et les activités, communiquer avec les familles, produire les rapports et feuilles de temps, sécuriser le service et offrir du soutien.</p>
        <h2>3. Caméra, localisation et appareils</h2>
        <p>La caméra et la localisation sont demandées pour confirmer une présence du personnel au lieu de travail configuré. Un compte mobile peut être lié à un appareil; un gestionnaire autorisé peut réinitialiser ce lien. Le service ne demande pas la localisation en continu en arrière-plan.</p>
        <h2>4. Témoins et stockage local</h2>
        <p>Le service utilise un témoin de session pour maintenir la connexion et le stockage local du navigateur pour mémoriser la langue et certains réglages d’interface. Ces éléments ne servent pas à vendre des profils publicitaires.</p>
        <h2>5. Accès et communication</h2>
        <p>L’accès est limité selon le rôle et le projet. Les renseignements peuvent être accessibles aux personnes autorisées de votre garderie et aux fournisseurs techniques nécessaires à l’hébergement, aux courriels ou au soutien. PITIT PAS SYSTEM ne vend pas les renseignements personnels.</p>
        <h2>6. Conservation et destruction</h2>
        <p>Les renseignements sont conservés pendant la durée nécessaire aux services, aux sauvegardes, aux demandes du client et aux obligations applicables. À la fin de leur utilité, ils doivent être supprimés ou rendus anonymes selon les procédures de conservation convenues avec l’organisation cliente.</p>
        <h2>7. Sécurité et incidents</h2>
        <p>Des contrôles d’accès, mots de passe chiffrés, journaux, sauvegardes et connexions HTTPS en production sont utilisés pour réduire les risques. Aucun système ne peut toutefois garantir une sécurité absolue. Tout incident suspect doit être signalé rapidement au responsable indiqué ci-dessous.</p>
        <h2>8. Accès, correction et questions</h2>
        <p>Vous pouvez demander l’accès ou la correction de vos renseignements, ou poser une question sur leur traitement. Selon le contexte, la demande pourra être traitée avec la garderie ou l’organisation cliente.</p>
        <div class="privacy-contact"><strong>Responsable de la protection des renseignements personnels</strong><br>{contact_name_html}<br>{contact_email_html}</div>
      </div>
      <div class="panel privacy-article" data-privacy-article="en" hidden>
        <h1>Privacy Policy</h1>
        <p class="muted">PITIT PAS SYSTEM · Last updated: {PRIVACY_POLICY_UPDATED}</p>
        <p class="privacy-note">This policy describes PITIT PAS SYSTEM practices. The childcare centre or organization that gives you access remains your first contact for information it manages.</p>
        <h2>1. Information processed</h2>
        <ul>
          <li>Accounts, names, roles, contact details and group information;</li>
          <li>Child and staff information, attendance, arrival and departure times;</li>
          <li>Allergies, dietary needs, calendars, messages, files and notes submitted through the service;</li>
          <li>Device identifiers, IP addresses, connection logs and activity records;</li>
          <li>GPS location and a front-camera photo only when validating mobile staff attendance.</li>
        </ul>
        <h2>2. Purposes</h2>
        <p>Information is used to manage accounts and access, record attendance, plan staffing, meals and activities, communicate with families, produce reports and timecards, secure the service and provide support.</p>
        <h2>3. Camera, location and devices</h2>
        <p>Camera and location access are requested to confirm staff attendance at the configured workplace. A mobile account may be bound to a device; an authorized manager may reset that binding. The service does not request continuous background location.</p>
        <h2>4. Cookies and local storage</h2>
        <p>The service uses a session cookie to keep users signed in and browser local storage to remember language and selected interface settings. These technologies are not used to sell advertising profiles.</p>
        <h2>5. Access and disclosure</h2>
        <p>Access is limited by role and project. Information may be available to authorized people at your childcare centre and technical providers needed for hosting, email or support. PITIT PAS SYSTEM does not sell personal information.</p>
        <h2>6. Retention and deletion</h2>
        <p>Information is retained as needed for the services, backups, customer instructions and applicable obligations. When no longer required, it should be deleted or anonymized under retention procedures agreed with the customer organization.</p>
        <h2>7. Security and incidents</h2>
        <p>Access controls, hashed passwords, logs, backups and production HTTPS are used to reduce risk. No system can guarantee absolute security. Suspected incidents should be reported promptly to the contact below.</p>
        <h2>8. Access, correction and questions</h2>
        <p>You may request access to or correction of your information, or ask how it is handled. Depending on the context, the request may be handled with the childcare centre or customer organization.</p>
        <div class="privacy-contact"><strong>Privacy Officer</strong><br>{contact_name_html}<br>{contact_email_html}</div>
      </div>
    </div>
    <script>
    (function() {{
      const articles = Array.from(document.querySelectorAll('[data-privacy-article]'));
      const buttons = Array.from(document.querySelectorAll('[data-privacy-language]'));
      const back = document.querySelector('[data-privacy-back]');
      function setLanguage(language) {{
        const selected = language === 'en' ? 'en' : 'fr';
        articles.forEach(function(article) {{ article.hidden = article.dataset.privacyArticle !== selected; }});
        buttons.forEach(function(button) {{ button.setAttribute('aria-pressed', button.dataset.privacyLanguage === selected ? 'true' : 'false'); }});
        if (back) back.textContent = selected === 'en' ? '← Sign in' : '← Connexion';
        document.documentElement.lang = selected;
        try {{ window.localStorage.setItem('pititpas-language', selected); }} catch (_error) {{}}
      }}
      buttons.forEach(function(button) {{ button.addEventListener('click', function() {{ setLanguage(button.dataset.privacyLanguage); }}); }});
      let saved = '';
      try {{ saved = window.localStorage.getItem('pititpas-language') || ''; }} catch (_error) {{}}
      setLanguage(saved === 'en' ? 'en' : 'fr');
    }})();
    </script>
    """
    return html_page("Politique de confidentialité", None, body)

def render_project_register(error=None, created_url=None):
    error_html = f'<div class="alert error">{html.escape(error)}</div>' if error else ""
    if created_url:
        created_html = f"""
        <div class="alert info project-created-alert">
          <span data-fr="Projet créé. Lien d’inscription du premier propriétaire :" data-en="Project created. First owner registration link:">Projet créé. Lien d’inscription du premier propriétaire :</span>
          <div style="margin-top:6px"><a href="{html.escape(created_url)}">{html.escape(created_url)}</a></div>
        </div>
        """
        form_or_next_html = """
        <div class="project-next-step" role="status">
          <span class="project-next-step-icon">2</span>
          <div>
            <strong data-fr="Étape suivante" data-en="Next step">Étape suivante</strong>
            <p data-fr="Cliquez sur le lien ci-dessus pour créer votre nom d’utilisateur et votre mot de passe." data-en="Click the link above to create your username and password.">Cliquez sur le lien ci-dessus pour créer votre nom d’utilisateur et votre mot de passe.</p>
          </div>
        </div>
        """
    else:
        created_html = ""
        form_or_next_html = """
        <form method="post" action="/project/register" class="grid project-register-form">
          <div>
            <label data-fr="Nom du projet / garderie" data-en="Project / childcare centre name">Nom du projet / garderie</label>
            <input name="project_name" required>
          </div>
          <div>
            <label data-fr="Nom du propriétaire" data-en="Owner name">Nom du propriétaire</label>
            <input name="owner_name" required>
          </div>
          <div>
            <label data-fr="E-MAIL" data-en="EMAIL">E-MAIL</label>
            <input name="email" type="email" required>
          </div>
          <button class="btn primary" type="submit" data-fr="Créer le projet" data-en="Create project">Créer le projet</button>
        </form>
        """
    body = f"""
    <style>
      .project-register-box {{ max-width:620px; }}
      .project-register-head {{ display:flex; align-items:flex-start; justify-content:space-between; gap:16px; margin-bottom:20px; }}
      .project-register-head h1 {{ margin:0; }}
      .project-language {{ display:inline-flex; gap:4px; padding:3px; border:1px solid #d7e0e3; border-radius:999px; background:#f4f7f8; }}
      .project-language button {{ min-width:38px; padding:6px 9px; border:0; border-radius:999px; background:transparent; color:#52666b; font-size:12px; font-weight:800; cursor:pointer; }}
      .project-language button[aria-pressed="true"] {{ background:#2f80c2; color:#fff; box-shadow:0 2px 7px rgba(47,128,194,.24); }}
      .project-register-form {{ gap:12px; }}
      .project-created-alert a {{ overflow-wrap:anywhere; }}
      .project-next-step {{ display:grid; grid-template-columns:36px minmax(0,1fr); gap:12px; align-items:start; margin-top:14px; padding:16px; border:1px solid #b9d9ee; border-radius:12px; background:#eef7fd; color:#173b3f; }}
      .project-next-step-icon {{ display:grid; width:32px; height:32px; place-items:center; border-radius:50%; background:#2f80c2; color:#fff; font-size:15px; font-weight:900; }}
      .project-next-step strong {{ display:block; margin:1px 0 4px; color:#1f6fa9; font-size:14px; }}
      .project-next-step p {{ margin:0; font-size:14px; line-height:1.5; }}
      .project-login-return {{ margin-top:14px; }}
      @media (max-width:640px) {{ .project-register-head {{ gap:10px; }} .project-register-head h1 {{ font-size:25px; }} .project-next-step {{ padding:13px; }} }}
    </style>
    <div class="login-box project-register-box" data-project-register data-title-fr="Créer projet" data-title-en="Create project">
      <div class="project-register-head">
        <h1 data-fr="Créer un projet" data-en="Create a project">Créer un projet</h1>
        <div class="project-language" role="group" aria-label="Language">
          <button type="button" data-language-choice="fr" aria-pressed="true">FR</button>
          <button type="button" data-language-choice="en" aria-pressed="false">EN</button>
        </div>
      </div>
      {created_html}
      {error_html}
      {form_or_next_html}
      <div class="project-login-return"><a href="/" data-fr="Retour à la connexion" data-en="Back to sign in">Retour à la connexion</a></div>
    </div>
    <script>
    (function() {{
      const root = document.querySelector('[data-project-register]');
      if (!root) return;
      function setLanguage(language) {{
        const selected = language === 'en' ? 'en' : 'fr';
        root.querySelectorAll('[data-fr][data-en]').forEach(function(element) {{
          element.textContent = element.getAttribute('data-' + selected) || '';
        }});
        root.querySelectorAll('[data-language-choice]').forEach(function(button) {{
          button.setAttribute('aria-pressed', button.getAttribute('data-language-choice') === selected ? 'true' : 'false');
        }});
        document.documentElement.lang = selected;
        document.title = root.getAttribute('data-title-' + selected) || document.title;
        try {{ window.localStorage.setItem('pititpas-language', selected); }} catch (_error) {{}}
      }}
      root.querySelectorAll('[data-language-choice]').forEach(function(button) {{
        button.addEventListener('click', function() {{ setLanguage(button.getAttribute('data-language-choice')); }});
      }});
      let savedLanguage = '';
      try {{ savedLanguage = window.localStorage.getItem('pititpas-language') || ''; }} catch (_error) {{}}
      setLanguage(savedLanguage === 'en' ? 'en' : 'fr');
    }})();
    </script>
    """
    return html_page("Créer projet", None, body)

def project_summary_rows(conn):
    return conn.execute(
        """
        SELECT projects.*,
               owner.username AS owner_username,
               owner.display_name AS owner_display_name,
               (SELECT COUNT(*) FROM web_users WHERE web_users.project_id = projects.id AND web_users.is_active = 1) AS active_users,
               (SELECT COUNT(*) FROM persons WHERE persons.project_id = projects.id) AS people_count
        FROM projects
        LEFT JOIN web_users owner ON owner.id = projects.owner_user_id
        WHERE projects.status <> 'deleted'
        ORDER BY projects.id
        """
    ).fetchall()


def render_projects_admin(user, query):
    if not is_super_admin(user):
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage projects.</div>')
    flash = None
    deleted = query.get("deleted", [""])[0]
    switched = query.get("switched", [""])[0]
    if deleted:
        flash = {"type": "info", "text": "Projet supprimé."}
    elif switched:
        flash = {"type": "info", "text": "Projet sélectionné."}
    with connect_db() as conn:
        rows = project_summary_rows(conn)
    current_id = user_project_id(user)
    rows_html = ""
    for row in rows:
        owner = row["owner_display_name"] or row["owner_username"] or ""
        current_badge = " <span class=\"badge present\">Actuel</span>" if row["id"] == current_id else ""
        delete_form = ""
        if row["id"] != 1:
            delete_form = f"""
              <a class="btn danger" href="/projects/delete?project_id={row['id']}">Supprimer</a>
            """
        rows_html += f"""
          <tr>
            <td>{row['id']}</td>
            <td>{html.escape(row['name'])}{current_badge}</td>
            <td>{html.escape(row['status'])}</td>
            <td>{html.escape(owner)}</td>
            <td>{row['active_users']}</td>
            <td>{row['people_count']}</td>
            <td style="display:flex;gap:6px;align-items:center;flex-wrap:wrap">
              <form method="post" action="/projects/switch" data-no-wait="true">
                <input type="hidden" name="project_id" value="{row['id']}">
                <button class="btn" type="submit">Ouvrir</button>
              </form>
              {delete_form}
            </td>
          </tr>
        """
    body = f"""
    <div class="panel">
      <h2>Projets</h2>
      <div class="muted" style="margin-bottom:10px">Compte concepteur: {html.escape(user['username'])}</div>
      <div class="btn-row" style="margin-bottom:10px">
        <a class="btn" href="/projects/diagnostics">Diagnostics</a>
      </div>
      <div class="table-wrap">
        <table>
          <thead>
            <tr><th>ID</th><th>Projet</th><th>Statut</th><th>Propriétaire</th><th>Accounts</th><th>Personnes</th><th>Action</th></tr>
          </thead>
          <tbody>{rows_html or '<tr><td colspan="7" class="muted">No projects</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Projets", user, body, flash=flash)


def render_project_diagnostics(user):
    if not is_super_admin(user):
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view project diagnostics.</div>')
    with connect_db() as conn:
        project_rows = conn.execute(
            """
            SELECT projects.id, projects.name, projects.status,
                   (SELECT COUNT(*) FROM web_users WHERE web_users.project_id = projects.id AND web_users.is_active = 1) AS active_users,
                   (SELECT COUNT(*) FROM persons WHERE persons.project_id = projects.id AND persons.role = 'children') AS children_count,
                   (SELECT COUNT(*) FROM persons WHERE persons.project_id = projects.id AND persons.role = 'teachers') AS staff_person_count,
                   (SELECT COUNT(*) FROM mobile_invitations WHERE mobile_invitations.project_id = projects.id) AS invitation_count
            FROM projects
            WHERE projects.status <> 'deleted'
            ORDER BY projects.id
            """
        ).fetchall()
        mismatch_rows = conn.execute(
            """
            SELECT web_users.id, web_users.username, web_users.display_name, web_users.role,
                   web_users.project_id AS account_project_id,
                   persons.id AS person_id, persons.name AS person_name, persons.role AS person_role,
                   persons.project_id AS person_project_id
            FROM web_users
            JOIN persons ON persons.id = web_users.person_id
            WHERE web_users.is_active = 1
              AND web_users.project_id <> persons.project_id
            ORDER BY web_users.project_id, web_users.role, web_users.display_name
            LIMIT 200
            """
        ).fetchall()
        invitation_mismatch_rows = conn.execute(
            """
            SELECT mobile_invitations.id, mobile_invitations.email, mobile_invitations.role,
                   mobile_invitations.project_id AS invitation_project_id,
                   persons.id AS person_id, persons.name AS person_name,
                   persons.project_id AS person_project_id
            FROM mobile_invitations
            JOIN persons ON persons.id = mobile_invitations.person_id
            WHERE mobile_invitations.project_id <> persons.project_id
            ORDER BY mobile_invitations.project_id, mobile_invitations.id DESC
            LIMIT 200
            """
        ).fetchall()
    project_html = "".join(
        f"""
        <tr>
          <td>{row['id']}</td>
          <td>{html.escape(row['name'])}</td>
          <td>{html.escape(row['status'])}</td>
          <td>{row['active_users']}</td>
          <td>{row['children_count']}</td>
          <td>{row['staff_person_count']}</td>
          <td>{row['invitation_count']}</td>
        </tr>
        """
        for row in project_rows
    )
    mismatch_html = "".join(
        f"""
        <tr>
          <td>{row['id']}</td>
          <td>{html.escape(row['username'])}</td>
          <td>{html.escape(row['display_name'] or '')}</td>
          <td>{html.escape(row['role'])}</td>
          <td>{row['account_project_id']}</td>
          <td>{row['person_id']}</td>
          <td>{html.escape(row['person_name'] or '')}</td>
          <td>{row['person_project_id']}</td>
        </tr>
        """
        for row in mismatch_rows
    )
    invitation_mismatch_html = "".join(
        f"""
        <tr>
          <td>{row['id']}</td>
          <td>{html.escape(row['email'] or '')}</td>
          <td>{html.escape(row['role'] or '')}</td>
          <td>{row['invitation_project_id']}</td>
          <td>{row['person_id']}</td>
          <td>{html.escape(row['person_name'] or '')}</td>
          <td>{row['person_project_id']}</td>
        </tr>
        """
        for row in invitation_mismatch_rows
    )
    body = f"""
    <div class="panel">
      <h2>Diagnostics projets</h2>
      <div class="btn-row" style="margin-bottom:10px"><a class="btn" href="/projects">Retour</a></div>
      <div class="table-wrap">
        <table>
          <thead><tr><th>ID</th><th>Projet</th><th>Statut</th><th>Accounts</th><th>Enfants</th><th>Staff persons</th><th>Invitations</th></tr></thead>
          <tbody>{project_html or '<tr><td colspan="7" class="muted">No project data.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <div class="panel" style="margin-top:16px">
      <h2>Accounts avec projet incohérent</h2>
      <div class="table-wrap">
        <table>
          <thead><tr><th>User ID</th><th>Username</th><th>Name</th><th>Role</th><th>Account project</th><th>Person ID</th><th>Person</th><th>Person project</th></tr></thead>
          <tbody>{mismatch_html or '<tr><td colspan="8" class="muted">No account/person mismatch.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <div class="panel" style="margin-top:16px">
      <h2>Invitations avec projet incohérent</h2>
      <div class="table-wrap">
        <table>
          <thead><tr><th>Invitation ID</th><th>Email</th><th>Role</th><th>Invitation project</th><th>Person ID</th><th>Person</th><th>Person project</th></tr></thead>
          <tbody>{invitation_mismatch_html or '<tr><td colspan="7" class="muted">No invitation/person mismatch.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Diagnostics projets", user, body)


def render_project_delete_confirm(user, project_id, error=None):
    if not is_super_admin(user):
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to delete projects.</div>')
    with connect_db() as conn:
        project = conn.execute(
            """
            SELECT projects.*,
                   (SELECT COUNT(*) FROM web_users WHERE web_users.project_id = projects.id AND web_users.is_active = 1) AS active_users,
                   (SELECT COUNT(*) FROM persons WHERE persons.project_id = projects.id) AS people_count
            FROM projects
            WHERE projects.id = ? AND projects.status <> 'deleted'
            """,
            (project_id,),
        ).fetchone()
    if not project:
        return html_page("Not Found", user, '<div class="panel">Projet introuvable.</div>')
    if project["id"] == 1:
        return html_page("Forbidden", user, '<div class="panel">Le projet principal ne peut pas être supprimé.</div>')
    body = f"""
    <div class="panel">
      <h2>Confirmer la suppression</h2>
      <div class="alert warn">
        Cette opération supprimera définitivement ce projet et ses données liées.
      </div>
      {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
      <div class="table-wrap" style="margin:12px 0">
        <table>
          <tbody>
            <tr><th>ID</th><td>{project['id']}</td></tr>
            <tr><th>Projet</th><td>{html.escape(project['name'])}</td></tr>
            <tr><th>Accounts actifs</th><td>{project['active_users']}</td></tr>
            <tr><th>Personnes</th><td>{project['people_count']}</td></tr>
          </tbody>
        </table>
      </div>
      <form method="post" action="/projects/delete" class="grid" style="gap:12px;max-width:420px">
        <input type="hidden" name="project_id" value="{project['id']}">
        <input type="hidden" name="confirm" value="DELETE">
        <div>
          <label>Mot de passe actuel</label>
          <input name="password" type="password" autocomplete="current-password" required>
        </div>
        <div style="display:flex;gap:8px;flex-wrap:wrap">
          <button class="btn danger" type="submit">Supprimer définitivement</button>
          <a class="btn" href="/projects">Annuler</a>
        </div>
      </form>
    </div>
    """
    return html_page("Supprimer projet", user, body)


def delete_project_data(conn, project_id):
    project_id = int(project_id)
    if project_id == 1:
        raise ValueError("Default project cannot be deleted")
    project = conn.execute("SELECT * FROM projects WHERE id = ?", (project_id,)).fetchone()
    if not project:
        raise ValueError("Project not found")
    user_ids = [row["id"] for row in conn.execute("SELECT id FROM web_users WHERE project_id = ?", (project_id,)).fetchall()]
    person_ids = [row["id"] for row in conn.execute("SELECT id FROM persons WHERE project_id = ?", (project_id,)).fetchall()]
    if user_ids:
        placeholders = ",".join("?" for _ in user_ids)
        conn.execute(f"DELETE FROM sessions WHERE user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM user_profiles WHERE user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM child_calendar_events WHERE user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM child_calendar_events WHERE created_by_user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM child_agenda_entries WHERE child_user_id IN ({placeholders})", user_ids)
        conn.execute(f"UPDATE child_agenda_entries SET author_user_id = NULL WHERE author_user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM user_files WHERE owner_user_id IN ({placeholders})", user_ids)
        conn.execute(f"UPDATE user_files SET uploader_user_id = owner_user_id WHERE uploader_user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM internal_messages WHERE sender_user_id IN ({placeholders}) OR recipient_user_id IN ({placeholders})", user_ids + user_ids)
        conn.execute(f"DELETE FROM mobile_devices WHERE user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM user_connection_approvals WHERE user_id IN ({placeholders})", user_ids)
        conn.execute(f"UPDATE user_connection_approvals SET approved_by_user_id = NULL WHERE approved_by_user_id IN ({placeholders})", user_ids)
        conn.execute(f"DELETE FROM user_ui_preferences WHERE user_id IN ({placeholders})", user_ids)
    if person_ids:
        placeholders = ",".join("?" for _ in person_ids)
        conn.execute(f"DELETE FROM attendance WHERE person_id IN ({placeholders})", person_ids)
        conn.execute(f"DELETE FROM child_agenda_entries WHERE child_person_id IN ({placeholders})", person_ids)
    conn.execute("DELETE FROM mobile_invitations WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM attendance_locations WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM teacher_schedule WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM deleted_user_archives WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM hidden_class_names WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM class_names WHERE project_id = ?", (project_id,))
    conn.execute("UPDATE projects SET owner_user_id = NULL WHERE id = ?", (project_id,))
    conn.execute("DELETE FROM web_users WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM persons WHERE project_id = ?", (project_id,))
    conn.execute("DELETE FROM projects WHERE id = ?", (project_id,))


def normalize_contact_value(value):
    return re.sub(r"[\s\-\(\)\.]+", "", (value or "").strip().lower())


def contact_matches_recovery(profile, recovery_value):
    target = normalize_contact_value(recovery_value)
    if not target:
        return False
    try:
        phones = json.loads(profile["phones_json"] or "[]") if profile else []
    except (json.JSONDecodeError, TypeError):
        phones = []
    try:
        emails = json.loads(profile["emails_json"] or "[]") if profile else []
    except (json.JSONDecodeError, TypeError):
        emails = []
    for value in list(phones) + list(emails):
        if normalize_contact_value(value) == target:
            return True
    return False


def render_password_reset(error=None, success=None):
    body = """
    <div class="login-box">
      <h1 style="margin-top:0">Réinitialiser le mot de passe</h1>
      <div class="alert warn">La réinitialisation automatique du mot de passe est temporairement désactivée.</div>
      <div style="margin-top:12px"><a href="/login">Retour à Connexion</a></div>
    </div>
    """
    return html_page("Réinitialiser le mot de passe", None, body)


def session_cookie_header(token):
    c = cookies.SimpleCookie()
    c["session"] = token
    c["session"]["path"] = "/"
    c["session"]["httponly"] = True
    c["session"]["samesite"] = "Lax"
    return c.output(header="").strip()


def connection_device_cookie_header(device_key):
    c = cookies.SimpleCookie()
    c[CONNECTION_DEVICE_COOKIE] = device_key
    c[CONNECTION_DEVICE_COOKIE]["path"] = "/"
    c[CONNECTION_DEVICE_COOKIE]["httponly"] = True
    c[CONNECTION_DEVICE_COOKIE]["samesite"] = "Lax"
    c[CONNECTION_DEVICE_COOKIE]["max-age"] = 60 * 60 * 24 * 365
    return c.output(header="").strip()


def project_context_cookie_header(project_id):
    c = cookies.SimpleCookie()
    c[PROJECT_CONTEXT_COOKIE] = str(int(project_id))
    c[PROJECT_CONTEXT_COOKIE]["path"] = "/"
    c[PROJECT_CONTEXT_COOKIE]["httponly"] = True
    c[PROJECT_CONTEXT_COOKIE]["samesite"] = "Lax"
    c[PROJECT_CONTEXT_COOKIE]["max-age"] = 60 * 60 * 24 * 365
    return c.output(header="").strip()


def invited_login_cookie_header():
    c = cookies.SimpleCookie()
    c[INVITED_LOGIN_COOKIE] = "1"
    c[INVITED_LOGIN_COOKIE]["path"] = "/"
    c[INVITED_LOGIN_COOKIE]["httponly"] = True
    c[INVITED_LOGIN_COOKIE]["samesite"] = "Lax"
    c[INVITED_LOGIN_COOKIE]["max-age"] = 60 * 60 * 24 * 30
    return c.output(header="").strip()


def clear_session_cookie():
    c = cookies.SimpleCookie()
    c["session"] = ""
    c["session"]["path"] = "/"
    c["session"]["httponly"] = True
    c["session"]["samesite"] = "Lax"
    c["session"]["max-age"] = 0
    return c.output(header="").strip()


def clear_project_context_cookie():
    c = cookies.SimpleCookie()
    c[PROJECT_CONTEXT_COOKIE] = ""
    c[PROJECT_CONTEXT_COOKIE]["path"] = "/"
    c[PROJECT_CONTEXT_COOKIE]["httponly"] = True
    c[PROJECT_CONTEXT_COOKIE]["samesite"] = "Lax"
    c[PROJECT_CONTEXT_COOKIE]["max-age"] = 0
    return c.output(header="").strip()


def parse_cookie(header):
    c = cookies.SimpleCookie()
    if not header:
        return c
    try:
        c.load(header)
    except cookies.CookieError:
        pass
    return c


def normalize_classes_list(value, all_classes):
    if not value:
        return []
    if value == "all":
        return list(all_classes)
    if isinstance(value, list):
        flat = []
        for item in value:
            if isinstance(item, str):
                flat.append(item)
        return sorted(set(flat))
    if isinstance(value, str):
        return [part for part in value.split(",") if part]
    return []


def classes_for_user(user, conn):
    all_classes = get_classes(conn, user)
    if user["role"] == "children":
        if not user["person_id"]:
            return []
        row = conn.execute("SELECT class_name FROM persons WHERE id = ? AND role = 'children' AND project_id = ?", (user["person_id"], effective_project_id(conn, user))).fetchone()
        return [row["class_name"]] if row and row["class_name"] else []
    if user["role"] in VIEW_ALL_CLASSES_ROLES:
        return all_classes
    allowed = safe_json_list(user["allowed_classes_json"])
    return [c for c in all_classes if c in allowed]


def can_edit_child(user):
    return user["role"] in EDIT_ROLES


def can_view_all_classes(user):
    return user["role"] in VIEW_ALL_CLASSES_ROLES


def can_manage_users(actor, target):
    if target and int(target["project_id"] or 1) != user_project_id(actor):
        return False
    if actor["role"] in MANAGE_ALL_USERS_ROLES:
        return True
    if not target or not target["is_active"]:
        return False
    if actor["role"] != "principal":
        return False
    return target["role"] in {"teacher", "cook", "children"}


def can_reset_user_password(actor, target):
    if actor["role"] == "boss":
        return True
    if not target or not target["is_active"]:
        return False
    if actor["role"] == "principal":
        return target["role"] in {"teacher", "cook", "children"} or target["id"] == actor["id"]
    return False


def person_role_for_user_role(role):
    return {
        "boss": "teachers",
        "principal": "teachers",
        "teacher": "teachers",
        "children": "children",
        "cook": "teachers",
    }.get(role)


def prevent_child_teacher_name_conflict(conn, name, person_role, project_id=1):
    if person_role not in {"children", "teachers"}:
        return
    conflicting_role = "teachers" if person_role == "children" else "children"
    existing = conn.execute(
        "SELECT id, name, role FROM persons WHERE lower(name) = lower(?) AND role = ? AND project_id = ? ORDER BY id LIMIT 1",
        (name, conflicting_role, int(project_id or 1)),
    ).fetchone()
    if not existing:
        return
    existing_label = "teacher" if conflicting_role == "teachers" else "child"
    new_label = "teacher" if person_role == "teachers" else "child"
    raise ValueError(
        f"{name} already exists as a {existing_label}. "
        f"Rename or remove that record before creating a {new_label} with the same name."
    )


def create_or_reuse_person_for_user_role(conn, role, display_name, class_name="", photo_path="", project_id=1):
    person_role = person_role_for_user_role(role)
    if not person_role:
        return None
    name = (display_name or "").strip()
    if not name:
        raise ValueError("Display name is required")
    existing = conn.execute(
        "SELECT * FROM persons WHERE lower(name) = lower(?) AND role = ? AND project_id = ? ORDER BY id LIMIT 1",
        (name, person_role, int(project_id or 1)),
    ).fetchone()
    if existing:
        if role == "children" and class_name and not (existing["class_name"] or "").strip():
            conn.execute(
                "UPDATE persons SET class_name = ?, updated_at = ? WHERE id = ?",
                (class_name, now_text(), existing["id"]),
            )
            ensure_class_name(conn, class_name, project_id=project_id)
        return existing["id"]
    prevent_child_teacher_name_conflict(conn, name, person_role, project_id=project_id)
    resolved_photo_path = (photo_path or "").strip()
    resolved_class_name = (class_name or "").strip()
    if role == "children":
        if resolved_class_name:
            ensure_class_name(conn, resolved_class_name, project_id=project_id)
        if not resolved_photo_path:
            resolved_photo_path = default_child_photo_path(name)
        qr_token = f"CHILD:{secrets.token_urlsafe(16)}"
    elif role in {"teacher", "principal", "boss"}:
        qr_token = f"STAFF:{secrets.token_urlsafe(16)}"
    elif role == "cook":
        qr_token = f"COOK:{secrets.token_urlsafe(16)}"
    else:
        qr_token = f"USER:{secrets.token_urlsafe(16)}"
    conn.execute(
        """
        INSERT INTO persons(project_id, name, role, class_name, photo_path, qr_token, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (int(project_id or 1), name, person_role, resolved_class_name, resolved_photo_path, qr_token, now_text()),
    )
    return conn.execute("SELECT last_insert_rowid()").fetchone()[0]


def create_or_reuse_person_with_role(conn, role, display_name, class_name="", photo_path="", project_id=1):
    if role not in {"boss", "principal", "teacher", "cook", "children"}:
        return None
    person_role = person_role_for_user_role(role) or role
    name = (display_name or "").strip()
    if not name:
        raise ValueError("Display name is required")
    existing = conn.execute(
        "SELECT * FROM persons WHERE lower(name) = lower(?) AND role = ? AND project_id = ? ORDER BY id LIMIT 1",
        (name, person_role, int(project_id or 1)),
    ).fetchone()
    if existing:
        if role == "children" and class_name and not (existing["class_name"] or "").strip():
            conn.execute(
                "UPDATE persons SET class_name = ?, updated_at = ? WHERE id = ?",
                (class_name, now_text(), existing["id"]),
            )
            ensure_class_name(conn, class_name, project_id=project_id)
        return existing["id"]
    prevent_child_teacher_name_conflict(conn, name, person_role, project_id=project_id)
    resolved_photo_path = (photo_path or "").strip()
    resolved_class_name = (class_name or "").strip()
    if role == "children":
        if resolved_class_name:
            ensure_class_name(conn, resolved_class_name, project_id=project_id)
        if not resolved_photo_path:
            resolved_photo_path = default_child_photo_path(name)
        qr_token = f"CHILD:{secrets.token_urlsafe(16)}"
    elif person_role == "teachers":
        qr_token = f"STAFF:{secrets.token_urlsafe(16)}"
    else:
        qr_token = f"USER:{secrets.token_urlsafe(16)}"
    conn.execute(
        """
        INSERT INTO persons(project_id, name, role, class_name, photo_path, qr_token, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (int(project_id or 1), name, person_role, resolved_class_name, resolved_photo_path, qr_token, now_text()),
    )
    return conn.execute("SELECT last_insert_rowid()").fetchone()[0]


def creatable_roles_for_user(actor):
    if actor["role"] == "boss":
        return ["boss", "principal", "teacher", "cook", "children"]
    if actor["role"] == "principal":
        return ["teacher", "cook", "children"]
    return []


def editable_roles_for_user(actor, target=None):
    roles = creatable_roles_for_user(actor)
    if target is not None and target["role"] == actor["role"] == "boss":
        return ["boss"] + roles
    return roles


def password_is_expired(user):
    try:
        due = datetime.strptime(user["next_password_change_at"], "%Y-%m-%d %H:%M:%S")
    except Exception:
        return True
    return local_now() >= due


def recent_teacher_event_block(conn, person_id, event_type):
    row = conn.execute(
        """
        SELECT timestamp
        FROM attendance
        WHERE person_id = ? AND role = 'teachers'
        ORDER BY timestamp DESC, id DESC
        LIMIT 1
        """,
        (person_id,),
    ).fetchone()
    if not row:
        return False
    try:
        last = datetime.strptime(row["timestamp"], "%Y-%m-%d %H:%M:%S")
    except ValueError:
        return False
    return (local_now() - last).total_seconds() < 30 * 60


def record_attendance(conn, actor, person_id, event_type, source="web", request_handler=None, snapshot_path=None):
    person = conn.execute("SELECT id, name, role, project_id FROM persons WHERE id = ?", (person_id,)).fetchone()
    if not person:
        raise ValueError("Child or teacher not found")
    if actor and int(person["project_id"] or 1) != effective_project_id(conn, actor):
        raise ValueError("Person is not in this project")
    if person["role"] == "teachers" and recent_teacher_event_block(conn, person_id, event_type):
        raise ValueError("Teacher attendance changes are locked for 30 minutes after the last record")
    timestamp = now_text()
    try:
        conn.execute(
            """
            INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path)
            VALUES (?, ?, ?, ?, ?, ?)
            """,
            (person["id"], person["name"], person["role"], event_type, timestamp, snapshot_path),
        )
    except sqlite3.IntegrityError as exc:
        raise ValueError(f"Database error: {exc}") from exc
    details = {
        "person_name": person["name"],
        "role": person["role"],
        "event_type": event_type,
        "source": source,
        "operator_name": user_display_name(actor),
    }
    if snapshot_path:
        details["snapshot_path"] = snapshot_path
    if request_handler is not None:
        audit_request(
            request_handler,
            conn,
            actor["id"] if actor else None,
            f"{source}_{event_type}",
            "attendance",
            object_id=person["id"],
            details=details,
        )
    else:
        audit(
            conn,
            actor["id"] if actor else None,
            f"{source}_{event_type}",
            "attendance",
            object_id=person["id"],
            details=details,
        )


def delete_today_attendance(conn, actor, person_id, day_text, request_handler=None):
    conn.execute(
        "DELETE FROM attendance WHERE person_id = ? AND timestamp LIKE ?",
        (person_id, f"{day_text}%"),
    )
    if request_handler is not None:
        audit_request(
            request_handler,
            conn,
            actor["id"] if actor else None,
            "delete_attendance",
            "attendance",
            object_id=person_id,
            details={"day": day_text},
        )
    else:
        audit(
            conn,
            actor["id"] if actor else None,
            "delete_attendance",
            "attendance",
            object_id=person_id,
            details={"day": day_text},
        )


def delete_teacher_day_attendance(conn, actor, teacher_id, day_text, request_handler=None):
    teacher = conn.execute(
        "SELECT id, name FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
        (teacher_id, effective_project_id(conn, actor)),
    ).fetchone()
    if not teacher:
        raise ValueError("Teacher not found")
    deleted = conn.execute(
        """
        DELETE FROM attendance
        WHERE person_id = ?
          AND role = 'teachers'
          AND timestamp LIKE ?
        """,
        (teacher["id"], f"{day_text}%"),
    ).rowcount
    details = {"day": day_text, "person_name": teacher["name"], "role": "teachers", "deleted_count": deleted}
    if request_handler is not None:
        audit_request(
            request_handler,
            conn,
            actor["id"] if actor else None,
            "delete_teacher_day_attendance",
            "attendance",
            object_id=teacher["id"],
            details=details,
        )
    else:
        audit(
            conn,
            actor["id"] if actor else None,
            "delete_teacher_day_attendance",
            "attendance",
            object_id=teacher["id"],
            details=details,
        )
    return deleted


def latest_attendance_rows(conn, person_id, limit=30):
    person = conn.execute("SELECT name, role FROM persons WHERE id = ?", (person_id,)).fetchone()
    if not person:
        return []
    return conn.execute(
        """
        SELECT
            attendance.id,
            attendance.event_type,
            attendance.timestamp,
            COALESCE(attendance.snapshot_path, '') AS snapshot_path,
            COALESCE((
                SELECT
                  CASE
                    WHEN audit_log.details_json LIKE '%"source": "desktop"%'
                    THEN attendance.name
                    ELSE COALESCE(NULLIF(web_users.display_name, ''), NULLIF(web_users.username, ''), 'System')
                  END
                FROM audit_log
                LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                WHERE audit_log.object_type = 'attendance'
                  AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                  AND (
                    audit_log.action LIKE '%' || attendance.event_type
                    OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                  )
                  AND (
                    audit_log.created_at <= attendance.timestamp
                    OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                  )
                ORDER BY audit_log.created_at DESC, audit_log.id DESC
                LIMIT 1
              ), 'System') AS actor_name
        FROM attendance
        WHERE lower(name) = lower(?) AND role = ?
        ORDER BY timestamp DESC, id DESC
        LIMIT ?
        """,
        (person["name"], person["role"], limit),
    ).fetchall()


def attendance_by_day(conn, person_id, start_day, days=28):
    rows = []
    current = datetime.strptime(start_day, "%Y-%m-%d").date()
    closed_dates = set(load_closed_dates())
    for _ in range(days):
        day_text = current.strftime("%Y-%m-%d")
        if day_text in closed_dates:
            status = "F"
        else:
            events = get_attendance_rows(conn, person_id, day_text)
            if not events:
                status = "A"
            else:
                status = "P" if events[-1]["event_type"] == "checkin" else "A"
        rows.append((day_text, status))
        current += timedelta(days=1)
    return rows


def fiche_summary(conn, person_id, start_day):
    rows = attendance_by_day(conn, person_id, start_day, days=28)
    weeks = [rows[i:i + 7] for i in range(0, 28, 7)]
    return weeks


def render_fiche_calendar(weeks):
    day_names = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
    week_blocks = []
    total_counts = {"P": 0, "A": 0, "F": 0}
    for week_index, week in enumerate(weeks, start=1):
        counts = {"P": 0, "A": 0, "F": 0}
        day_cards = []
        for day_index, (day_text, status) in enumerate(week):
            dt = datetime.strptime(day_text, "%Y-%m-%d").date()
            counts[status] += 1
            total_counts[status] += 1
            day_cards.append(f"""
              <div class="fiche-day {status}">
                <div class="fiche-day-name">{day_names[day_index]}</div>
                <div><span class="fiche-day-date">{dt.day}</span> <span class="fiche-day-month">{dt.strftime('%b')}</span></div>
                <span class="pill {status}">{status}</span>
              </div>
            """)
        week_blocks.append(f"""
          <div class="fiche-week">
            <div class="fiche-week-label">
              <strong>Week {week_index}</strong>
              <span>P {counts['P']} / A {counts['A']} / F {counts['F']}</span>
            </div>
            {''.join(day_cards)}
          </div>
        """)
    legend = f"""
      <div class="fiche-legend">
        <span>Toute:</span>
        <span><span class="pill P">P</span> Present {total_counts['P']}</span>
        <span><span class="pill A">A</span> Absence {total_counts['A']}</span>
        <span><span class="pill F">F</span> Closed {total_counts['F']}</span>
      </div>
    """
    return f"<div class=\"fiche-calendar\">{''.join(week_blocks)}</div>{legend}"


def render_mobile_dashboard(user, query):
    if user["role"] in STAFF_MOBILE_ATTENDANCE_ROLES:
        return render_teacher_mobile_dashboard(user)
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        classes = classes_for_user(user, conn)
        selected_class = query.get("class", [get_last_selected_class(conn, user["id"])])[0]
        selected_date = query.get("date", [today_text()])[0]
        selected_child_id = query.get("child_id", [""])[0]
        if selected_class not in classes and selected_class != "all":
            selected_class = classes[0] if classes else "all"
        set_last_selected_class(conn, user["id"], selected_class)
        children = get_children(conn, user, selected_class)
        is_child_account = user["role"] == "children"
        can_mark = can_edit_child(user) or bool(is_child_account and selected_date == today_text())
        counts = count_statuses(conn, children, selected_date)
        selected_child = None
        if selected_child_id:
            for child in children:
                if str(child["id"]) == selected_child_id:
                    selected_child = child
                    break
        if is_child_account and not selected_child and children:
            selected_child = children[0]
            selected_child_id = str(selected_child["id"])
        class_options = "".join(
            f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{"Toute" if cls == "all" else html.escape(cls)}</option>'
            for cls in (["all"] + classes)
        )
        child_cards = []
        for child in children:
            status = current_child_status(conn, child["id"], selected_date)
            status_class = {"P": "present", "A": "absent", "F": "closed"}.get(status, "absent")
            photo_url = child_card_image_url(child["photo_path"])
            image_html = f'<img src="{photo_url}" alt="{html.escape(child["name"])}">' if photo_url else '<div class="mobile-photo-empty">?</div>'
            detail_url = f"/mobile?class={quote(selected_class)}&date={quote(selected_date)}&child_id={child['id']}#mobile-selected-child"
            child_cards.append(f"""
              <a class="mobile-child-link" href="{detail_url}">
              <section class="mobile-child {status_class} {'selected' if str(child['id']) == selected_child_id else ''}">
                <div class="mobile-child-head">
                  <div class="mobile-photo">{image_html}</div>
                  <div class="mobile-child-main">
                    <div class="mobile-child-name">{html.escape(child['name'])}</div>
                    <div class="mobile-child-class">{html.escape(child['class_name'] or 'Unassigned')}</div>
                    <div class="badge {status_class}">{status_label(status)}</div>
                  </div>
                </div>
              </section>
              </a>
            """)
        selected_child_panel = ""
        if selected_child:
            status = current_child_status(conn, selected_child["id"], selected_date)
            status_class = {"P": "present", "A": "absent", "F": "closed"}.get(status, "absent")
            photo_url = child_card_image_url(selected_child["photo_path"])
            image_html = f'<img src="{photo_url}" alt="{html.escape(selected_child["name"])}">' if photo_url else '<div class="mobile-photo-empty">?</div>'
            checkin_disabled = status in {"P", "F"} or not can_mark
            checkout_disabled = status in {"A", "F"} or not can_mark
            attendance_rows = get_attendance_rows(conn, selected_child["id"], selected_date)
            checkin_times = [row["timestamp"][11:16] for row in attendance_rows if row["event_type"] == "checkin" and len(row["timestamp"] or "") >= 16]
            checkout_times = [row["timestamp"][11:16] for row in attendance_rows if row["event_type"] == "checkout" and len(row["timestamp"] or "") >= 16]
            checkin_time_html = f'<div class="mobile-action-time">{html.escape(checkin_times[0])}</div>' if checkin_times else '<div class="mobile-action-time">&nbsp;</div>'
            checkout_time_html = f'<div class="mobile-action-time">{html.escape(checkout_times[-1])}</div>' if checkout_times else '<div class="mobile-action-time">&nbsp;</div>'
            actions = "" if selected_date != today_text() and is_child_account else f"""
              <div class="mobile-actions">
                <form method="post" action="/child/{selected_child['id']}/event" onsubmit="return confirm('Confirmer arrivée de {html.escape(selected_child['name'], quote=True)} ?')">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <input type="hidden" name="event_type" value="checkin">
                  <input type="hidden" name="return_to" value="mobile">
                  <button class="mobile-btn arrive" type="submit" {"disabled" if checkin_disabled else ""}>Arrivée</button>
                  {checkin_time_html}
                </form>
                <form method="post" action="/child/{selected_child['id']}/event" onsubmit="return confirm('Confirmer départ de {html.escape(selected_child['name'], quote=True)} ?')">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <input type="hidden" name="event_type" value="checkout">
                  <input type="hidden" name="return_to" value="mobile">
                  <button class="mobile-btn depart" type="submit" {"disabled" if checkout_disabled else ""}>Départ</button>
                  {checkout_time_html}
                </form>
              </div>
            """
            list_url = f"/mobile?class={quote(selected_class)}&date={quote(selected_date)}"
            list_link_html = "" if is_child_account else f'<a class="btn ghost" href="{list_url}" style="width:100%;margin-top:2px">Retour à la liste</a>'
            selected_child_panel = f"""
              <section class="mobile-child {status_class}" id="mobile-selected-child">
                <div class="mobile-child-head">
                  <div class="mobile-photo">{image_html}</div>
                  <div class="mobile-child-main">
                    <div class="mobile-child-name">{html.escape(selected_child['name'])}</div>
                    <div class="mobile-child-class">{html.escape(selected_child['class_name'] or 'Unassigned')}</div>
                    <div class="badge {status_class}">{status_label(status)}</div>
                  </div>
                </div>
                {actions}
                {list_link_html}
              </section>
            """

    filters_html = "" if is_child_account else f"""
      <form method="get" action="/mobile" class="mobile-filters">
        <div class="mobile-filter-row">
          <label>Groupe</label>
          <select name="class" onchange="this.form.submit()">{class_options}</select>
        </div>
        <div class="mobile-filter-row">
          <label>Date</label>
          <input type="date" name="date" value="{html.escape(selected_date)}" onchange="this.form.submit()">
        </div>
      </form>
    """
    mobile_overview_html = "" if is_child_account else f"""
      <div class="panel">
        <div class="mobile-title">
          <h2 class="mobile-tableau-title">Tableau</h2>
          <div class="mobile-date">{html.escape(selected_date)}</div>
        </div>
        <div style="margin-top:12px">{filters_html}</div>
        <div class="mobile-stats" style="margin-top:12px">
          <div class="mobile-stat"><span>Enfants</span><strong>{len(children)}</strong></div>
          <div class="mobile-stat"><span>Présent</span><strong style="color:#2f8f58">{counts['P']}</strong></div>
          <div class="mobile-stat"><span>Absence</span><strong style="color:#6b7785">{counts['A']}</strong></div>
        </div>
      </div>
    """
    body = f"""
    <style>
      .mobile-shell {{ max-width: 520px; margin: 0 auto; display: grid; gap: 12px; }}
      .mobile-title {{ display:flex; align-items:center; justify-content:space-between; gap:10px; }}
      .mobile-title h2 {{ margin:0; font-size:20px; }}
      .mobile-date {{ color:var(--muted); font-size:12px; font-weight:700; }}
      .mobile-filters {{ display:grid; grid-template-columns:1fr 1fr; gap:10px; }}
      .mobile-tableau-title {{ display:none; }}
      .mobile-filter-row {{ display:grid; grid-template-columns:auto minmax(0,1fr); gap:8px; align-items:center; }}
      .mobile-filter-row label {{ margin:0; white-space:nowrap; }}
      .mobile-filter-row select, .mobile-filter-row input {{ width:100%; min-width:0; }}
      .mobile-stats {{ display:grid; grid-template-columns:repeat(3, 1fr); gap:8px; }}
      .mobile-stat {{ border:1px solid var(--line); border-radius:8px; background:#fff; padding:10px; min-height:58px; }}
      .mobile-stat span {{ display:block; color:var(--muted); font-size:11px; font-weight:700; }}
      .mobile-stat strong {{ display:block; font-size:22px; line-height:1.1; margin-top:4px; }}
      .mobile-list {{ display:grid; gap:10px; }}
      .mobile-child-link {{ color:inherit; text-decoration:none; display:block; }}
      .mobile-child-link:hover {{ text-decoration:none; }}
      .mobile-child {{ border:1px solid var(--line); border-radius:8px; background:#fff; padding:12px; display:grid; gap:12px; }}
      .mobile-child.selected {{ border-color:var(--blue); box-shadow:0 0 0 2px rgba(47,128,194,0.14); }}
      .mobile-child.present {{ border-color:#8fd8b5; background:var(--green-soft); }}
      .mobile-child.absent, .mobile-child.closed {{ background:#f8fafc; color:#6b7785; }}
      .mobile-child-head {{ display:grid; grid-template-columns:64px minmax(0, 1fr); gap:12px; align-items:center; }}
      .mobile-photo, .mobile-photo img, .mobile-photo-empty {{ width:64px; height:64px; border-radius:50%; }}
      .mobile-photo {{ overflow:hidden; background:var(--blue-soft); border:1px solid #d7e4f2; display:flex; align-items:center; justify-content:center; }}
      .mobile-photo img {{ object-fit:cover; display:block; }}
      .mobile-photo-empty {{ display:flex; align-items:center; justify-content:center; color:#7c8b9c; font-weight:800; }}
      .mobile-child-name {{ font-size:17px; line-height:1.15; font-weight:800; color:var(--text); overflow-wrap:anywhere; }}
      .mobile-child-class {{ color:var(--muted); font-size:13px; margin:2px 0 5px; }}
      .mobile-actions {{ display:grid; grid-template-columns:1fr 1fr; gap:8px; }}
      .mobile-actions form {{ margin:0; }}
      .mobile-action-time {{ min-height:14px; margin-top:3px; color:var(--muted); font-size:11px; line-height:1.1; text-align:center; font-weight:700; }}
      .mobile-btn {{ width:100%; min-height:48px; border:1px solid transparent; border-radius:8px; font-size:16px; font-weight:800; cursor:pointer; }}
      .mobile-btn.arrive {{ background:var(--green); border-color:#188b58; color:#fff; }}
      .mobile-btn.depart {{ background:var(--blue); border-color:#236fa8; color:#fff; }}
      .mobile-btn:disabled {{ background:#edf1f5; color:#9aa7b6; border-color:#dbe3ec; cursor:not-allowed; }}
      .mobile-empty {{ padding:18px; text-align:center; color:var(--muted); }}
      @media (max-width: 560px) {{
        .wrap {{ padding:12px; }}
        .topbar {{ padding:10px 12px; }}
        .nav {{ gap:5px; }}
        .nav a, .nav button {{ padding:6px 8px; font-size:12px; }}
        .mobile-filters {{ grid-template-columns:1fr; gap:6px; }}
      }}
    </style>
    <div class="mobile-shell">
      {mobile_overview_html}
      <div class="mobile-list">
        {selected_child_panel if selected_child else (''.join(child_cards) if child_cards else '<div class="panel mobile-empty">Aucun enfant trouvé.</div>')}
      </div>
    </div>
    """
    return html_page("Mobile", user, body)


def render_child_agenda(user):
    if user["role"] != "children":
        return html_page("Forbidden", user, '<div class="panel">Agenda is available for child accounts only.</div>')
    with connect_db() as conn:
        if user["person_id"]:
            entries = conn.execute(
                """
                SELECT *
                FROM child_agenda_entries
                WHERE child_user_id = ? OR child_person_id = ?
                ORDER BY day_text DESC, created_at DESC, id DESC
                """,
                (user["id"], user["person_id"]),
            ).fetchall()
        else:
            entries = conn.execute(
                """
                SELECT *
                FROM child_agenda_entries
                WHERE child_user_id = ?
                ORDER BY day_text DESC, created_at DESC, id DESC
                """,
                (user["id"],),
            ).fetchall()
    rows = []
    for entry in entries:
        rows.append(
            f"""
            <div class="panel" style="padding:12px">
              <div style="display:flex;justify-content:space-between;gap:12px;flex-wrap:wrap">
                <div>
                  <div style="font-weight:800">{html.escape(entry['title'] or 'Rapport')}</div>
                  <div class="small muted">{html.escape(entry['day_text'])} &middot; {html.escape(entry['class_name'] or '')}</div>
                </div>
                <div class="small muted">Par {html.escape(entry['author_name'] or 'Educatrice')}</div>
              </div>
              <div class="muted-box" style="margin-top:10px;white-space:pre-wrap">{html.escape(entry['body'])}</div>
              <div class="small muted" style="margin-top:8px">{html.escape(entry['created_at'])}</div>
            </div>
            """
        )
    body = f"""
    <div class="panel">
      <h2>Agenda</h2>
      <div class="grid" style="gap:10px">
        {''.join(rows) or '<div class="muted-box">Aucun événement pour le moment.</div>'}
      </div>
    </div>
    """
    return html_page("Agenda", user, body)


def render_staff_agenda(user, query):
    if user["role"] == "children":
        return render_child_agenda(user)
    selected_class = query.get("class", [""])[0]
    selected_day = query.get("date", [today_text()])[0]
    try:
        datetime.strptime(selected_day, "%Y-%m-%d")
    except ValueError:
        selected_day = today_text()
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        if not selected_class and classes:
            selected_class = get_last_selected_class(conn, user["id"], classes[0])
        if selected_class not in classes:
            selected_class = classes[0] if classes else ""
        set_last_selected_class(conn, user["id"], selected_class)
        children = get_children(conn, user, selected_class) if selected_class else []
        present_children = [child for child in children if current_child_status(conn, child["id"], selected_day) == "P"]
        child_accounts_by_person = {}
        if present_children:
            person_ids = [int(child["id"]) for child in present_children]
            placeholders = ",".join("?" for _ in person_ids)
            child_accounts = conn.execute(
                f"""
                SELECT web_users.*, persons.name AS child_name
                FROM web_users
                JOIN persons ON persons.id = web_users.person_id
                WHERE web_users.role = 'children'
                  AND web_users.is_active = 1
                  AND web_users.project_id = ?
                  AND web_users.person_id IN ({placeholders})
                ORDER BY persons.name
                """,
                [int(user["project_id"] or 1)] + person_ids,
            ).fetchall()
            for account in child_accounts:
                child_accounts_by_person.setdefault(int(account["person_id"]), []).append(account)
        recent = conn.execute(
            """
            SELECT day_text, class_name, author_name, created_at, COUNT(*) AS sent_count
            FROM child_agenda_entries
            WHERE author_user_id = ?
            GROUP BY day_text, class_name, author_name, created_at
            ORDER BY created_at DESC
            LIMIT 8
            """,
            (user["id"],),
        ).fetchall()
    class_options = "".join(
        f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{html.escape(cls)}</option>'
        for cls in classes
    )
    recent_rows = "".join(
        f"<tr><td>{html.escape(row['created_at'])}</td><td>{html.escape(row['day_text'])}</td><td>{html.escape(row['class_name'])}</td><td>{row['sent_count']}</td></tr>"
        for row in recent
    )
    agenda_rows = []
    for child in present_children:
        accounts = child_accounts_by_person.get(int(child["id"]), [])
        if accounts:
            field_name = f"body_person_{child['id']}"
            input_html = (
                f'<input type="hidden" name="child_person_ids" value="{child["id"]}">'
                f'<textarea name="{field_name}" rows="3" placeholder="Contenu pour {html.escape(child["name"])}"></textarea>'
            )
        else:
            input_html = '<textarea rows="3" disabled placeholder="Aucun compte enfant actif"></textarea>'
        agenda_rows.append(
            f"""
            <tr>
              <td style="width:170px;white-space:nowrap">
                <div style="font-weight:700">{html.escape(child['name'])}</div>
              </td>
              <td>{input_html}</td>
            </tr>
            """
        )
    sendable_count = sum(len(accounts) for accounts in child_accounts_by_person.values())
    sent = query.get("sent", [""])[0]
    skipped = query.get("skipped", [""])[0]
    sent_html = ""
    if sent:
        sent_html = f'<div class="alert info">Agenda envoyé à {html.escape(sent)} enfant(s). Sans compte enfant: {html.escape(skipped or "0")}.</div>'
    body = f"""
    {sent_html}
    <div class="panel">
      <h2>AGENDA</h2>
      <form method="get" action="/agenda" class="toolbar">
        <div>
          <label>Groupe</label>
          <select name="class" onchange="this.form.submit()">{class_options}</select>
        </div>
        <div>
          <label>Date</label>
          <input type="date" name="date" value="{html.escape(selected_day)}" onchange="this.form.submit()">
        </div>
      </form>
      <form method="post" action="/agenda/send" class="grid" style="gap:10px">
        <input type="hidden" name="class_name" value="{html.escape(selected_class)}">
        <input type="hidden" name="day_text" value="{html.escape(selected_day)}">
        <div class="table-wrap">
          <table>
            <thead><tr><th style="width:170px">Enfant</th><th>Contenu</th></tr></thead>
            <tbody>{''.join(agenda_rows) or '<tr><td colspan="2" class="muted">Aucun enfant présent.</td></tr>'}</tbody>
          </table>
        </div>
        <div><button class="btn primary" type="submit" {"disabled" if not sendable_count else ""}>Envoyer aux agendas des enfants</button></div>
      </form>
      </div>
    <div class="panel" style="margin-top:16px">
      <h2>Envois récents</h2>
      <div class="table-wrap">
        <table>
          <thead><tr><th>Créé</th><th>Date</th><th>Groupe</th><th>Enfants</th></tr></thead>
          <tbody>{recent_rows or '<tr><td colspan="4" class="muted">Aucun envoi.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("AGENDA", user, body)


def render_staff_calendar(user, query):
    if user["role"] == "children":
        return html_page("Forbidden", user, '<div class="panel">CALENDRIER is available for staff accounts only.</div>')
    selected_month = query.get("month", [datetime.now().strftime("%Y-%m")])[0]
    try:
        month_start = datetime.strptime(selected_month, "%Y-%m").date().replace(day=1)
    except ValueError:
        month_start = date.today().replace(day=1)
        selected_month = month_start.strftime("%Y-%m")
    _, days_in_month = calendar.monthrange(month_start.year, month_start.month)
    month_end = month_start.replace(day=days_in_month)
    previous_month = (month_start - timedelta(days=1)).replace(day=1).strftime("%Y-%m")
    next_month = (month_end + timedelta(days=1)).replace(day=1).strftime("%Y-%m")
    tomorrow = date.today() + timedelta(days=1)
    chart_end = tomorrow + timedelta(days=27)
    query_start = min(month_start, tomorrow)
    query_end = max(month_end, chart_end)
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        selected_class = query.get("class", [get_last_selected_class(conn, user["id"])])[0]
        if selected_class not in classes and selected_class != "all":
            selected_class = classes[0] if classes else "all"
        set_last_selected_class(conn, user["id"], selected_class)
        children = get_children(conn, user, selected_class)
        person_ids = [int(child["id"]) for child in children]
        excluded_by_day = {}
        event_counts_by_day = {}
        present_by_day = {}
        if person_ids:
            placeholders = ",".join("?" for _ in person_ids)
            event_rows = conn.execute(
                f"""
                SELECT child_calendar_events.day_text, child_calendar_events.event_type, web_users.person_id
                FROM child_calendar_events
                JOIN web_users ON web_users.id = child_calendar_events.user_id
                WHERE web_users.person_id IN ({placeholders})
                  AND child_calendar_events.event_type IN ('VACANCES', 'MALADIE', 'ABSENCE')
                  AND child_calendar_events.day_text BETWEEN ? AND ?
                """,
                [*person_ids, query_start.strftime("%Y-%m-%d"), query_end.strftime("%Y-%m-%d")],
            ).fetchall()
            excluded_people_by_day = {}
            event_people_by_day = {}
            for row in event_rows:
                day_text = row["day_text"]
                event_type = row["event_type"]
                person_id = int(row["person_id"])
                excluded_people_by_day.setdefault(day_text, set()).add(person_id)
                event_people_by_day.setdefault(day_text, {}).setdefault(event_type, set()).add(person_id)
            excluded_by_day = {day_text: len(people) for day_text, people in excluded_people_by_day.items()}
            event_counts_by_day = {
                day_text: {event_type: len(people) for event_type, people in events.items()}
                for day_text, events in event_people_by_day.items()
            }
            attendance_rows = conn.execute(
                f"""
                SELECT person_id, event_type, timestamp
                FROM attendance
                WHERE person_id IN ({placeholders})
                  AND role = 'children'
                  AND timestamp BETWEEN ? AND ?
                ORDER BY timestamp ASC, id ASC
                """,
                [*person_ids, tomorrow.strftime("%Y-%m-%d 00:00:00"), chart_end.strftime("%Y-%m-%d 23:59:59")],
            ).fetchall()
            latest_status_by_day_person = {}
            for row in attendance_rows:
                timestamp = row["timestamp"] or ""
                if len(timestamp) < 10:
                    continue
                latest_status_by_day_person[(timestamp[:10], int(row["person_id"]))] = row["event_type"]
            for (day_text, _person_id), event_type in latest_status_by_day_person.items():
                if event_type == "checkin":
                    present_by_day[day_text] = present_by_day.get(day_text, 0) + 1
    closed_dates = set(load_closed_dates())
    total_children = len(children)
    class_options = "".join(
        f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{"Toute" if cls == "all" else html.escape(cls)}</option>'
        for cls in (["all"] + classes)
    )
    weeks = calendar.Calendar(firstweekday=0).monthdatescalendar(month_start.year, month_start.month)
    week_head = "".join(f'<th style="width:54px;padding:6px 2px;text-align:center">{label}</th>' for label in ["Lun", "Mar", "Mer", "Jeu", "Ven", "Sam", "Dim"])
    rows_html = []
    for week in weeks:
        cells = []
        for day in week:
            day_text = day.strftime("%Y-%m-%d")
            outside = day.month != month_start.month
            is_closed = day_text in closed_dates
            planned = 0 if is_closed else max(total_children - excluded_by_day.get(day_text, 0), 0)
            planned_html = str(planned) if day >= tomorrow else ""
            closed_html = '<div class="badge closed">Fermé</div>' if is_closed else ""
            outside_style = "opacity:0.42;" if outside else ""
            cells.append(
                f"""
                <td style="width:54px;height:23px;vertical-align:top;text-align:center;padding:4px 2px;{outside_style}">
                  <div style="font-weight:800;font-size:20px;line-height:1">{day.day}</div>
                  <div style="margin-top:1px;font-size:14px;font-weight:700;color:#7a8795">{planned_html}</div>
                  {closed_html}
                </td>
                """
            )
        rows_html.append(f"<tr>{''.join(cells)}</tr>")
    chart_values = []
    for offset in range(28):
        chart_day = tomorrow + timedelta(days=offset)
        chart_day_text = chart_day.strftime("%Y-%m-%d")
        planned_value = 0 if chart_day_text in closed_dates else max(total_children - excluded_by_day.get(chart_day_text, 0), 0)
        value = None if chart_day_text in closed_dates or (chart_day.weekday() >= 5 and planned_value == 0) else planned_value
        chart_values.append((chart_day, value))
    chart_max = max([value for _day, value in chart_values if value is not None] + [1])
    chart_w, chart_h = 420, 190
    pad_l, pad_t, pad_r, pad_b = 34, 18, 14, 30
    plot_w = chart_w - pad_l - pad_r
    plot_h = chart_h - pad_t - pad_b
    chart_xy = []
    for index, (chart_day, value) in enumerate(chart_values):
        x = pad_l + (plot_w * index / 27 if len(chart_values) > 1 else 0)
        y = None if value is None else pad_t + plot_h - (plot_h * value / chart_max if chart_max else 0)
        chart_xy.append((x, y, chart_day, value))
    parts = []
    current_segment = []
    for point in chart_xy:
        if point[1] is None:
            if current_segment:
                if len(current_segment) == 1:
                    parts.append(f"M {current_segment[0][0]:.1f} {current_segment[0][1]:.1f}")
                else:
                    parts.append(f"M {current_segment[0][0]:.1f} {current_segment[0][1]:.1f}")
                    for index in range(len(current_segment) - 1):
                        x0, y0 = current_segment[index][0], current_segment[index][1]
                        x1, y1 = current_segment[index + 1][0], current_segment[index + 1][1]
                        cx0 = x0 + (x1 - x0) / 2
                        cx1 = x1 - (x1 - x0) / 2
                        parts.append(f"C {cx0:.1f} {y0:.1f}, {cx1:.1f} {y1:.1f}, {x1:.1f} {y1:.1f}")
                current_segment = []
            continue
        current_segment.append(point)
    if current_segment:
        if len(current_segment) == 1:
            parts.append(f"M {current_segment[0][0]:.1f} {current_segment[0][1]:.1f}")
        else:
            parts.append(f"M {current_segment[0][0]:.1f} {current_segment[0][1]:.1f}")
            for index in range(len(current_segment) - 1):
                x0, y0 = current_segment[index][0], current_segment[index][1]
                x1, y1 = current_segment[index + 1][0], current_segment[index + 1][1]
                cx0 = x0 + (x1 - x0) / 2
                cx1 = x1 - (x1 - x0) / 2
                parts.append(f"C {cx0:.1f} {y0:.1f}, {cx1:.1f} {y1:.1f}, {x1:.1f} {y1:.1f}")
    chart_path = " ".join(parts)
    chart_grid = "".join(
        f'<line x1="{pad_l}" y1="{pad_t + plot_h * i / 4:.1f}" x2="{chart_w - pad_r}" y2="{pad_t + plot_h * i / 4:.1f}"></line>'
        for i in range(5)
    )
    chart_labels = "".join(
        f'<text x="{chart_xy[index][0]:.1f}" y="{chart_h - 8}" text-anchor="middle">{chart_xy[index][2].strftime("%m-%d")}</text>'
        for index in [0, 6, 13, 20, 27]
        if index < len(chart_xy)
    )
    chart_y_labels = "".join(
        f'<text x="{pad_l - 6}" y="{pad_t + plot_h - (plot_h * i / 4):.1f}" text-anchor="end" dominant-baseline="middle">{round(chart_max * i / 4)}</text>'
        for i in range(5)
    )
    chart_total_text = f"{chart_values[0][1]} demain" if chart_values and chart_values[0][1] is not None else ""
    future_rows = []
    for offset in range(28):
        future_day = tomorrow + timedelta(days=offset)
        future_day_text = future_day.strftime("%Y-%m-%d")
        event_counts = event_counts_by_day.get(future_day_text, {})
        planned_count = 0 if future_day_text in closed_dates else max(total_children - excluded_by_day.get(future_day_text, 0), 0)
        future_rows.append(
            f"""
            <tr>
              <td>{html.escape(future_day.strftime("%Y-%m-%d"))}</td>
              <td>{planned_count}</td>
              <td>{present_by_day.get(future_day_text, 0)}</td>
              <td>{event_counts.get("VACANCES", 0)}</td>
              <td>{event_counts.get("MALADIE", 0)}</td>
            </tr>
            """
        )
    planned_chart_html = f"""
      <div class="dashboard-chart staff-calendar-chart">
        <div class="dashboard-chart-head">
          <div class="dashboard-chart-title">PLANIFIES 28 JOURS</div>
          <div class="dashboard-chart-total">{html.escape(chart_total_text)}</div>
        </div>
        <svg class="arrival-chart" viewBox="0 0 {chart_w} {chart_h}" preserveAspectRatio="none" style="height:190px">
          <g class="chart-grid">{chart_grid}</g>
          <line x1="{pad_l}" y1="{pad_t}" x2="{pad_l}" y2="{pad_t + plot_h}" stroke="#cfd8e3" stroke-width="1"></line>
          <line x1="{pad_l}" y1="{pad_t + plot_h}" x2="{chart_w - pad_r}" y2="{pad_t + plot_h}" stroke="#cfd8e3" stroke-width="1"></line>
          {chart_y_labels}
          {chart_labels}
          <path class="chart-line" d="{chart_path}"></path>
        </svg>
      </div>
    """
    body = f"""
    <style>
      .staff-calendar-layout {{ display:grid; grid-template-columns:auto minmax(360px,1fr); gap:28px; align-items:start; }}
      .staff-calendar-layout > * {{ min-width:0; }}
      .staff-calendar-chart {{ min-height:230px; max-width:460px; margin-left:0; }}
      .staff-calendar-table-wrap table {{ width:auto; table-layout:fixed; border-collapse:collapse; }}
      .staff-calendar-side {{ width:100%; max-width:460px; min-width:0; }}
      .staff-calendar-future {{ margin-top:12px; max-width:460px; }}
      .staff-calendar-future table {{ width:100%; table-layout:fixed; }}
      .staff-calendar-future th, .staff-calendar-future td {{ padding:5px 6px; text-align:center; }}
      .staff-calendar-future th:first-child, .staff-calendar-future td:first-child {{ text-align:left; width:35%; }}
      @media (max-width:720px) {{
        .staff-calendar-panel {{ overflow:hidden; padding:8px; }}
        .staff-calendar-title {{ display:none; }}
        .staff-calendar-layout {{ grid-template-columns:1fr; gap:10px; }}
        .staff-calendar-toolbar {{ display:grid !important; grid-template-columns:minmax(0,1fr) minmax(0,1fr) !important; gap:6px !important; align-items:end !important; }}
        .staff-calendar-toolbar > div {{ width:100%; min-width:0; }}
        .staff-calendar-toolbar select, .staff-calendar-toolbar input {{ width:100%; min-width:0; }}
        .staff-calendar-toolbar .staff-calendar-nav-buttons {{ grid-column:1 / -1; }}
        .staff-calendar-nav-buttons {{ display:flex !important; flex-direction:row !important; flex-wrap:nowrap !important; gap:6px; width:100%; }}
        .staff-calendar-nav-buttons .btn {{ flex:0 0 calc(50% - 3px) !important; width:calc(50% - 3px) !important; min-width:0; white-space:nowrap; padding-left:4px; padding-right:4px; }}
        .staff-calendar-table-wrap {{ width:100%; max-width:100%; overflow-x:hidden; }}
        .staff-calendar-table-wrap table {{ width:100%; min-width:0; }}
        .staff-calendar-table-wrap th {{ width:auto !important; padding:4px 1px !important; font-size:11px; }}
        .staff-calendar-table-wrap td {{ width:auto !important; height:36px !important; padding:2px 1px !important; }}
        .staff-calendar-table-wrap td > div:first-child {{ font-size:13px !important; }}
        .staff-calendar-table-wrap td > div:nth-child(2) {{ font-size:11px !important; }}
        .staff-calendar-table-wrap .badge {{ font-size:9px; padding:1px 3px; }}
        .staff-calendar-side {{ width:100%; max-width:100%; }}
        .staff-calendar-chart {{ box-sizing:border-box; width:100%; max-width:100%; min-height:142px; padding:6px; overflow:hidden; }}
        .staff-calendar-chart .dashboard-chart-head {{ gap:6px; }}
        .staff-calendar-chart .dashboard-chart-title {{ font-size:11px; }}
        .staff-calendar-chart .dashboard-chart-total {{ font-size:10px; }}
        .staff-calendar-chart .arrival-chart {{ height:108px !important; }}
        .staff-calendar-future {{ width:100%; max-width:100%; margin-top:8px; overflow:hidden; }}
        .staff-calendar-future table {{ width:100%; min-width:0; table-layout:fixed; }}
        .staff-calendar-future th, .staff-calendar-future td {{ padding:3px 2px; font-size:11px; line-height:1.15; }}
        .staff-calendar-future th:first-child, .staff-calendar-future td:first-child {{ width:34%; }}
      }}
    </style>
    <div class="panel staff-calendar-panel">
      <h2 class="staff-calendar-title">CALENDRIER</h2>
      <form method="get" action="/calendar" class="toolbar staff-calendar-toolbar">
        <div class="staff-calendar-side">
          <label>Groupe</label>
          <select name="class" onchange="this.form.submit()">{class_options}</select>
        </div>
        <div>
          <label>Mois</label>
          <input type="month" name="month" value="{html.escape(selected_month)}" onchange="this.form.submit()">
        </div>
        <div style="align-self:end" class="btn-row staff-calendar-nav-buttons">
          <a class="btn" href="/calendar?month={quote(previous_month)}&class={quote(selected_class)}">Précédent</a>
          <a class="btn" href="/calendar?month={quote(next_month)}&class={quote(selected_class)}">Suivant</a>
        </div>
      </form>
      <div class="stats">
        <div class="stat"><div class="muted">Enfants</div><div class="value">{total_children}</div></div>
      </div>
      <div class="staff-calendar-layout">
        <div class="table-wrap staff-calendar-table-wrap">
          <table>
            <thead><tr>{week_head}</tr></thead>
            <tbody>{''.join(rows_html)}</tbody>
          </table>
        </div>
        <div>
          {planned_chart_html}
          <div class="table-wrap staff-calendar-future">
            <table>
              <thead><tr><th>Date</th><th>Nb</th><th>Prés.</th><th>Vac.</th><th>Mal.</th></tr></thead>
              <tbody>{''.join(future_rows)}</tbody>
            </table>
          </div>
        </div>
      </div>
    </div>
    """
    return html_page("CALENDRIER", user, body)


def render_allergic_children(user, query):
    if user["role"] == "children":
        return html_page("Forbidden", user, '<div class="panel">ENFANTS ALLERGIQUES is available for staff accounts only.</div>')
    selected_class = query.get("class", ["all"])[0]
    selected_date = query.get("date", [today_text()])[0]
    try:
        datetime.strptime(selected_date, "%Y-%m-%d")
    except ValueError:
        selected_date = today_text()
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        if selected_class not in classes and selected_class != "all":
            selected_class = classes[0] if classes else "all"
        children = get_children(conn, user, selected_class)
        rows = []
        for child in children:
            if current_child_status(conn, child["id"], selected_date) != "P":
                continue
            profile = conn.execute(
                """
                SELECT user_profiles.allergies
                FROM web_users
                JOIN user_profiles ON user_profiles.user_id = web_users.id
                WHERE web_users.person_id = ? AND web_users.role = 'children'
                  AND web_users.project_id = ?
                """,
                (child["id"], effective_project_id(conn, user)),
            ).fetchone()
            allergies = (profile["allergies"] if profile else "").strip()
            if not allergies:
                continue
            latest = conn.execute(
                """
                SELECT timestamp
                FROM attendance
                WHERE person_id = ? AND role = 'children' AND timestamp LIKE ?
                ORDER BY timestamp DESC, id DESC
                LIMIT 1
                """,
                (child["id"], f"{selected_date}%"),
            ).fetchone()
            rows.append({
                "child": child,
                "allergies": allergies,
                "latest": latest["timestamp"] if latest else "",
            })
    class_options = "".join(
        f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{"Toute" if cls == "all" else html.escape(cls)}</option>'
        for cls in (["all"] + classes)
    )
    cards = []
    for row in rows:
        child = row["child"]
        photo_url = child_card_image_url(child["photo_path"])
        photo_html = f'<img src="{photo_url}" alt="{html.escape(child["name"])}" style="width:64px;height:64px;object-fit:cover;display:block">' if photo_url else '<div class="muted">No photo</div>'
        cards.append(
            f"""
            <div class="panel" style="padding:12px">
              <div class="selected-child-head present" style="margin-bottom:10px">
                <div class="photo" style="width:64px;height:64px;border-radius:8px;overflow:hidden">{photo_html}</div>
                <div>
                  <div class="selected-child-name">{html.escape(child['name'])}</div>
                  <div class="small muted">{html.escape(child['class_name'] or 'Unassigned')}</div>
                  <div class="badge present" style="margin-top:6px">Present</div>
                </div>
              </div>
              <div class="muted-box">
                <div style="white-space:pre-wrap">{html.escape(row['allergies'])}</div>
              </div>
              <div class="small muted" style="margin-top:8px">Dernière présence: {html.escape(row['latest'] or '-')}</div>
            </div>
            """
        )
    body = f"""
    <div class="panel">
      <h2>ENFANTS ALLERGIQUES</h2>
      <form method="get" action="/allergic-children" class="toolbar">
        <div>
          <label>Date</label>
          <input type="date" name="date" value="{html.escape(selected_date)}" onchange="this.form.submit()">
        </div>
        <div>
          <label>Groupe</label>
          <select name="class" onchange="this.form.submit()">{class_options}</select>
        </div>
      </form>
      <div class="stats">
        <div class="stat"><div class="muted">Present</div><div class="value">{len(rows)}</div></div>
      </div>
      <div class="grid" style="grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:12px">
        {''.join(cards) or '<div class="muted-box">Aucun enfant présent avec allergies enregistrées.</div>'}
      </div>
    </div>
    """
    return html_page("ENFANTS ALLERGIQUES", user, body)


def render_teacher_mobile_dashboard(user):
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        linked_person = None
        if user["person_id"]:
            linked_person = conn.execute(
                "SELECT * FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                (user["person_id"], project_id),
            ).fetchone()
        status = mobile_person_status(conn, user)
        location_policy = attendance_location_payload(conn, user)
        schedule = teacher_schedule_for_day(conn, linked_person["name"], today_text(), project_id) if linked_person else {"schedule_in": "", "schedule_out": ""}
        if linked_person and (not schedule["schedule_in"] or not schedule["schedule_out"]):
            previous_schedule = latest_teacher_schedule(conn, linked_person["name"], project_id)
            schedule = {
                **schedule,
                "schedule_in": schedule["schedule_in"] or previous_schedule["schedule_in"],
                "schedule_out": schedule["schedule_out"] or previous_schedule["schedule_out"],
            }
        reference_face_count = len(reference_face_paths_for_person(linked_person["name"])) if linked_person else 0
        has_reference_faces = reference_face_count > 0
    if not linked_person:
        body = """
        <div class="panel" style="max-width:560px;margin:0 auto">
          <div class="alert warn">Ce compte n'est pas lié à une fiche employé.</div>
          <div class="muted-box">Dans User Management, renseignez le Linked person ID correspondant à cette personne dans la liste PEOPLE/teachers.</div>
        </div>
        """
        return html_page("Présence", user, body)
    is_present = bool(status and status["status"] == "in")
    status_text = "Present" if is_present else "Sorti"
    status_class = "present" if is_present else "out"
    last_text = status["last_event_time"] if status and status.get("last_event_time") else "-"
    schedule_in_picker = time_picker_html("schedule_in", schedule["schedule_in"], element_id="mobile-schedule-in", css_class="mobile-schedule-value")
    schedule_out_picker = time_picker_html("schedule_out", schedule["schedule_out"], element_id="mobile-schedule-out", css_class="mobile-schedule-value")
    location_warning = "" if location_policy.get("configured") else '<div class="alert warn">Le lieu de travail mobile n\'est pas encore configuré.</div>'
    face_warning = "" if has_reference_faces else '<div class="alert warn">Aucune photo de référence. Enregistrez le visage avant la première présence.</div>'
    enroll_face_full = reference_face_count >= 5
    enroll_face_disabled = "disabled" if enroll_face_full else ""
    enroll_face_class = "gray" if enroll_face_full else "amber"
    body = f"""
    <style>
      .teacher-mobile-shell {{ max-width:520px; margin:0 auto; display:grid; gap:12px; }}
      .teacher-status {{ display:flex; align-items:center; justify-content:flex-start; gap:5px; }}
      .teacher-status-label {{ color:var(--muted); font-size:13px; font-weight:800; }}
      .teacher-status strong {{ font-size:18px; line-height:1.1; }}
      .teacher-status-value.present {{ color:var(--green); }}
      .teacher-status-value.out {{ color:var(--blue); }}
      .teacher-camera-panel {{ display:grid; gap:0; overflow:hidden; }}
      .teacher-camera-frame {{ width:220px; height:220px; margin:0 auto; overflow:hidden; border:0; border-radius:999px; background:#e8f1f8; }}
      .teacher-camera {{ width:220px; height:220px; display:block; border:0; border-radius:999px; object-fit:cover; transform:scale(1.4); transform-origin:center; }}
      .teacher-canvas {{ display:none; }}
      .teacher-actions {{ display:flex; flex-wrap:wrap; justify-content:center; align-items:center; gap:8px; }}
      .teacher-actions .btn {{ width:auto; min-width:0; min-height:36px; font-size:15px; line-height:1; padding:6px 10px; border-radius:6px; white-space:nowrap; }}
      .teacher-actions .btn.depart:not(:disabled) {{ background:var(--blue); color:#fff; border-color:#236fa8; }}
      #enroll-face-button {{ display:block; width:max-content; max-width:100%; min-height:36px; line-height:1; padding:6px 10px; border-radius:6px; white-space:nowrap; margin-left:auto; margin-right:auto; }}
      .teacher-actions .btn:disabled {{ background:#edf1f5 !important; color:#9aa7b6 !important; border-color:#dbe3ec !important; cursor:not-allowed; box-shadow:none; }}
      #enroll-face-button:disabled {{ background:#edf1f5 !important; color:#9aa7b6 !important; border-color:#dbe3ec !important; cursor:not-allowed; box-shadow:none; }}
      .teacher-schedule-grid {{ display:grid; grid-template-columns:1fr 1fr; gap:10px; margin-top:12px; }}
      .time-picker {{ display:flex; align-items:center; gap:4px; }}
      .time-picker select {{ min-height:44px; width:100%; font-size:16px; padding:7px 8px; }}
      .teacher-log {{ white-space:pre-wrap; overflow-wrap:anywhere; }}
      .teacher-log.success {{ background:#e6f7ed; border-color:#bce6cf; color:#135c36; font-weight:700; }}
      .teacher-log.error {{ background:#fff0f0; border-color:#f5b0b0; color:#921919; font-weight:700; }}
      @media (max-width:560px) {{ .wrap {{ padding:12px; }} }}
    </style>
    <div class="teacher-mobile-shell">
      <div class="panel">
        <div class="teacher-status">
          <span class="teacher-status-label">Statut</span>
          <strong id="teacher-status" class="teacher-status-value {status_class}">{html.escape(status_text)}</strong>
        </div>
        <div class="small muted">Dernier: <span id="teacher-last">{html.escape(last_text)}</span></div>
        <div class="teacher-schedule-grid">
          <div>
            <label>SCHEDULE IN</label>
            {schedule_in_picker}
          </div>
          <div>
            <label>SCHEDULE OUT</label>
            {schedule_out_picker}
          </div>
        </div>
      </div>
      {location_warning}
      {face_warning}
      <div class="panel teacher-camera-panel">
        <div class="teacher-camera-frame">
          <video id="teacher-video" class="teacher-camera" autoplay playsinline muted></video>
        </div>
        <canvas id="teacher-canvas" class="teacher-canvas"></canvas>
        <div class="teacher-actions" style="margin-top:0">
          <button class="btn green" type="button" data-event-type="checkin" {"disabled" if is_present else ""}>Arrivée visage</button>
          <button class="btn depart" type="button" data-event-type="checkout" {"disabled" if not is_present else ""}>Départ visage</button>
        </div>
        <button class="btn {enroll_face_class}" type="button" id="enroll-face-button" style="margin-top:8px" {enroll_face_disabled}>Enregistrer le visage</button>
        <div id="teacher-message" class="muted-box teacher-log" style="margin-top:12px">Autorisez la caméra et la position du téléphone.</div>
      </div>
    </div>
    <script>
    (function() {{
      const video = document.getElementById('teacher-video');
      const canvas = document.getElementById('teacher-canvas');
      const message = document.getElementById('teacher-message');
      const statusText = document.getElementById('teacher-status');
      const lastText = document.getElementById('teacher-last');
      const checkinButton = document.querySelector('[data-event-type="checkin"]');
      const checkoutButton = document.querySelector('[data-event-type="checkout"]');
      const enrollButton = document.getElementById('enroll-face-button');
      const scheduleInInput = document.getElementById('mobile-schedule-in');
      const scheduleOutInput = document.getElementById('mobile-schedule-out');
      const mobileUserRole = "{html.escape(user['role'])}";
      let faceEnrollmentComplete = {str(enroll_face_full).lower()};
      let streamStarted = false;
      let cameraStream = null;
      let idleTimer = null;
      let presenceClosed = false;
      let enrollImages = [];
      let enrollMode = false;
      let enrollCount = 0;
      let pendingAttendanceEvent = null;
      let pendingAttendanceButton = null;
      let pendingAttendancePosition = null;
      function setMessage(text, level) {{
        message.textContent = text;
        message.classList.remove('success', 'error');
        if (level) message.classList.add(level);
      }}
      function setPresenceState(isIn) {{
        if (checkinButton) checkinButton.disabled = !!isIn;
        if (checkoutButton) checkoutButton.disabled = !isIn;
        if (statusText) {{
          statusText.classList.toggle('present', !!isIn);
          statusText.classList.toggle('out', !isIn);
        }}
      }}
      function stopCamera() {{
        if (cameraStream) {{
          cameraStream.getTracks().forEach(function(track) {{ track.stop(); }});
          cameraStream = null;
        }}
        if (video) video.srcObject = null;
        streamStarted = false;
      }}
      function closePresenceWindow() {{
        if (presenceClosed) return;
        presenceClosed = true;
        stopCamera();
        window.open('', '_self');
        window.close();
        window.setTimeout(function() {{
          if (!document.hidden) {{
            document.body.innerHTML = '<div style="font-family:Arial,sans-serif;padding:24px;text-align:center;color:#24476f">Presence fermée.</div>';
          }}
        }}, 300);
      }}
      function resetIdleTimer() {{
        if (presenceClosed) return;
        if (idleTimer) window.clearTimeout(idleTimer);
        idleTimer = window.setTimeout(closePresenceWindow, 90000);
      }}
      async function startCamera() {{
        if (streamStarted) return;
        if (!window.isSecureContext && location.hostname !== 'localhost' && location.hostname !== '127.0.0.1') {{
          throw new Error('Camera requires HTTPS. Open this page with a secure https address or use the native mobile app.');
        }}
        if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {{
          throw new Error('Camera is not available in this browser. Use Safari/Chrome with HTTPS.');
        }}
        cameraStream = await navigator.mediaDevices.getUserMedia({{ video: {{ facingMode: 'user' }}, audio: false }});
        video.srcObject = cameraStream;
        streamStarted = true;
      }}
      function getPosition() {{
        return new Promise(function(resolve, reject) {{
          if (!navigator.geolocation) reject(new Error('Location is not available in this browser.'));
          navigator.geolocation.getCurrentPosition(resolve, reject, {{ enableHighAccuracy: true, timeout: 15000, maximumAge: 0 }});
        }});
      }}
      function captureBase64(quality, maxSideValue) {{
        const sourceWidth = video.videoWidth || 720;
        const sourceHeight = video.videoHeight || 960;
        const cropSize = Math.min(sourceWidth, sourceHeight);
        const sx = Math.max(0, Math.round((sourceWidth - cropSize) / 2));
        const sy = Math.max(0, Math.round((sourceHeight - cropSize) / 2));
        const maxSide = maxSideValue || 520;
        const width = Math.max(1, Math.min(maxSide, cropSize));
        const height = width;
        canvas.width = width;
        canvas.height = height;
        const ctx = canvas.getContext('2d');
        ctx.drawImage(video, sx, sy, cropSize, cropSize, 0, 0, width, height);
        return canvas.toDataURL('image/jpeg', quality || 0.62).split(',', 2)[1];
      }}
      function wait(ms) {{
        return new Promise(function(resolve) {{ window.setTimeout(resolve, ms); }});
      }}
      async function waitForVideoReady() {{
        for (let index = 0; index < 30; index += 1) {{
          if (video.videoWidth > 0 && video.videoHeight > 0) return;
          await wait(100);
        }}
        throw new Error('Camera image is not ready. Please try again.');
      }}
      function getDeviceId() {{
        let value = window.localStorage.getItem('garderie_mobile_device_id');
        if (!value) {{
          value = 'web-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
          window.localStorage.setItem('garderie_mobile_device_id', value);
        }}
        return value;
      }}
      function syncTimePicker(picker) {{
        const hidden = picker.querySelector('.time-picker-value');
        const hour = picker.querySelector('.time-picker-hour');
        const minute = picker.querySelector('.time-picker-minute');
        if (!hidden || !hour || !minute) return;
        if (hour.value === '19' && minute.value && minute.value !== '00') minute.value = '00';
        hidden.value = hour.value && minute.value ? hour.value + ':' + minute.value : '';
        hidden.dispatchEvent(new Event('input', {{ bubbles: true }}));
        hidden.dispatchEvent(new Event('change', {{ bubbles: true }}));
      }}
      document.querySelectorAll('.split-time-picker').forEach(function(picker) {{
        const hour = picker.querySelector('.time-picker-hour');
        const minute = picker.querySelector('.time-picker-minute');
        if (hour) hour.addEventListener('change', function() {{ syncTimePicker(picker); }});
        if (minute) minute.addEventListener('change', function() {{ syncTimePicker(picker); }});
        syncTimePicker(picker);
      }});
      async function saveSchedule() {{
        const scheduleIn = scheduleInInput ? scheduleInInput.value : '';
        const scheduleOut = scheduleOutInput ? scheduleOutInput.value : '';
        if (!scheduleIn || !scheduleOut) {{
          setMessage('SCHEDULE IN et SCHEDULE OUT sont requis.', 'error');
          return;
        }}
        if (!window.confirm('Confirmer l’enregistrement du schedule ?')) return false;
        setMessage('Sauvegarde du schedule...');
        const response = await fetch('/api/mobile/teacher-schedule', {{
          method: 'POST',
          credentials: 'same-origin',
          headers: {{ 'Content-Type': 'application/json' }},
          body: JSON.stringify({{
            schedule_in: scheduleIn,
            schedule_out: scheduleOut
          }})
        }});
        const rawText = await response.text();
        let data = null;
        try {{
          data = JSON.parse(rawText);
        }} catch (_parseError) {{
          throw new Error('Server returned a non-JSON error page. HTTP ' + response.status + '. ' + rawText.slice(0, 120).replace(/\\s+/g, ' '));
        }}
        if (!response.ok || data.ok === false) throw new Error(data.error || 'Erreur');
        setMessage('Schedule sauvegardé.', 'success');
        return true;
      }}
      async function saveScheduleIfComplete() {{
        const scheduleIn = scheduleInInput ? scheduleInInput.value : '';
        const scheduleOut = scheduleOutInput ? scheduleOutInput.value : '';
        if (!scheduleIn || !scheduleOut) return false;
        return await saveSchedule();
      }}
      function confirmMissingScheduleForCheckin(eventType) {{
        if (eventType !== 'checkin' || mobileUserRole === 'principal' || mobileUserRole === 'cook') return true;
        const scheduleIn = scheduleInInput ? scheduleInInput.value : '';
        const scheduleOut = scheduleOutInput ? scheduleOutInput.value : '';
        if (scheduleIn && scheduleOut) return true;
        return window.confirm('SCHEDULE IN et SCHEDULE OUT ne sont pas remplis. Continuer la signature sans schedule ?');
      }}
      async function submitAttendance(eventType, button) {{
        const currentlyIn = statusText.textContent.trim() === 'Present';
        if ((eventType === 'checkin' && currentlyIn) || (eventType === 'checkout' && !currentlyIn)) {{
          setPresenceState(currentlyIn);
          return;
        }}
        if (!confirmMissingScheduleForCheckin(eventType)) return;
        try {{
          if (!await saveScheduleIfComplete()) return;
        }} catch (error) {{
          setMessage(error.message || 'Erreur', 'error');
          return;
        }}
        if (pendingAttendanceEvent !== eventType) {{
          if (pendingAttendanceButton && pendingAttendanceButton !== button) {{
            pendingAttendanceButton.textContent = pendingAttendanceEvent === 'checkin' ? 'Arrivée visage' : 'Départ visage';
          }}
          pendingAttendanceEvent = eventType;
          pendingAttendanceButton = button;
          pendingAttendancePosition = null;
          button.textContent = eventType === 'checkin' ? 'Capturer arrivée' : 'Capturer départ';
          setMessage('Préparez le visage, puis appuyez sur ' + button.textContent + '.');
          try {{
            await startCamera();
            await waitForVideoReady();
            pendingAttendancePosition = await getPosition();
          }} catch (error) {{
            pendingAttendanceEvent = null;
            pendingAttendanceButton = null;
            pendingAttendancePosition = null;
            button.textContent = eventType === 'checkin' ? 'Arrivée visage' : 'Départ visage';
            setMessage(error.message || 'Erreur', 'error');
          }}
          return;
        }}
        const attendanceLabel = eventType === 'checkin' ? 'l’arrivée' : 'le départ';
        if (!window.confirm('Confirmer l’enregistrement de ' + attendanceLabel + ' ?')) return;
        button.disabled = true;
        setMessage('Vérification en cours...');
        let submittedPresenceState = null;
        try {{
          await startCamera();
          await waitForVideoReady();
          const position = pendingAttendancePosition || await getPosition();
          const faceImage = captureBase64(0.55, 520);
          const response = await fetch('/api/mobile/teacher-face-attendance', {{
            method: 'POST',
            credentials: 'same-origin',
            headers: {{ 'Content-Type': 'application/json' }},
            body: JSON.stringify({{
              event_type: eventType,
              device_id: getDeviceId(),
              device_name: navigator.userAgent || 'Mobile browser',
              latitude: position.coords.latitude,
              longitude: position.coords.longitude,
              accuracy_meters: position.coords.accuracy,
              face_image_base64: faceImage
            }})
          }});
          const rawText = await response.text();
          let data = null;
          try {{
            data = JSON.parse(rawText);
          }} catch (_parseError) {{
            throw new Error('Server returned a non-JSON error page. HTTP ' + response.status + '. ' + rawText.slice(0, 120).replace(/\\s+/g, ' '));
          }}
          if (!response.ok || data.ok === false) throw new Error(data.error || 'Erreur');
          statusText.textContent = data.status && data.status.status === 'in' ? 'Present' : 'Sorti';
          lastText.textContent = data.status && data.status.last_event_time ? data.status.last_event_time : '-';
          submittedPresenceState = data.status && data.status.status === 'in';
          setPresenceState(submittedPresenceState);
          const label = eventType === 'checkin' ? 'Arrivée' : 'Départ';
          setMessage(label + ' enregistré avec succès. Distance: ' + (data.location ? data.location.distance_meters + ' m' : '-'), 'success');
          pendingAttendanceEvent = null;
          pendingAttendanceButton = null;
          pendingAttendancePosition = null;
          button.textContent = eventType === 'checkin' ? 'Arrivée visage' : 'Départ visage';
          stopCamera();
          window.setTimeout(function() {{
            window.location.href = '/teacher-attendance';
          }}, 450);
        }} catch (error) {{
          pendingAttendanceEvent = null;
          pendingAttendanceButton = null;
          pendingAttendancePosition = null;
          button.textContent = eventType === 'checkin' ? 'Arrivée visage' : 'Départ visage';
          setMessage(error.message || 'Erreur', 'error');
        }} finally {{
          if (submittedPresenceState === null) {{
            button.disabled = false;
          }} else {{
            setPresenceState(submittedPresenceState);
          }}
        }}
      }}
      async function enrollFace(button) {{
        if (faceEnrollmentComplete) return;
        if (!enrollMode) {{
          if (!window.confirm('Confirmer l’enregistrement du visage ?')) return;
          enrollMode = true;
          enrollImages = [];
          enrollCount = 0;
          button.textContent = 'Photo 1 / 5';
          setMessage('Mode enregistrement. Centrez le visage puis appuyez sur Photo 1 / 5.');
          try {{
            await startCamera();
            await waitForVideoReady();
          }} catch (error) {{
            enrollMode = false;
            enrollImages = [];
            enrollCount = 0;
            button.textContent = 'Enregistrer le visage';
            setMessage(error.message || 'Erreur', 'error');
          }}
          return;
        }}
        button.disabled = true;
        try {{
          await startCamera();
          await waitForVideoReady();
          const image = captureBase64(0.42, 360);
          button.textContent = 'Envoi photo ' + (enrollCount + 1) + ' / 5...';
          setMessage('Envoi photo ' + (enrollCount + 1) + ' / 5...');
          const response = await fetch('/api/mobile/enroll-face', {{
            method: 'POST',
            credentials: 'same-origin',
            headers: {{ 'Content-Type': 'application/json' }},
            body: JSON.stringify({{
              device_id: getDeviceId(),
              device_name: navigator.userAgent || 'Mobile browser',
              face_images_base64: [image]
            }})
          }});
          const rawText = await response.text();
          let data = null;
          try {{
            data = JSON.parse(rawText);
          }} catch (_parseError) {{
            throw new Error('Server returned a non-JSON error page. HTTP ' + response.status + '. ' + rawText.slice(0, 120).replace(/\\s+/g, ' '));
          }}
          if (!response.ok || data.ok === false) throw new Error(data.error || 'Erreur');
          enrollCount += 1;
          if (enrollCount < 5) {{
            button.textContent = 'Photo ' + (enrollCount + 1) + ' / 5';
            setMessage('Photo ' + enrollCount + ' enregistrée. Changez légèrement la position puis appuyez sur Photo ' + (enrollCount + 1) + ' / 5.', 'success');
            return;
          }}
          setMessage('Visage enregistré avec succès. Photos: 5', 'success');
          faceEnrollmentComplete = true;
          button.disabled = true;
          button.classList.remove('amber');
          button.classList.add('gray');
          enrollMode = false;
          enrollImages = [];
          enrollCount = 0;
          button.textContent = 'Enregistrer le visage';
        }} catch (error) {{
          enrollMode = false;
          enrollImages = [];
          enrollCount = 0;
          button.textContent = 'Enregistrer le visage';
          setMessage(error.message || 'Erreur', 'error');
        }} finally {{
          if (!faceEnrollmentComplete) button.disabled = false;
        }}
      }}
      document.querySelectorAll('[data-event-type]').forEach(function(button) {{
        button.addEventListener('click', function() {{ submitAttendance(button.getAttribute('data-event-type'), button); }});
      }});
      if (enrollButton) {{
        enrollButton.addEventListener('click', function() {{ enrollFace(enrollButton); }});
      }}
      [scheduleInInput, scheduleOutInput].forEach(function(input) {{
        if (!input) return;
        input.addEventListener('change', function() {{
          if (scheduleInInput && scheduleOutInput && scheduleInInput.value && scheduleOutInput.value) {{
            saveSchedule().catch(function(error) {{ setMessage(error.message || 'Erreur', 'error'); }});
          }}
        }});
      }});
      ['click', 'touchstart', 'keydown', 'change', 'input', 'scroll'].forEach(function(eventName) {{
        window.addEventListener(eventName, resetIdleTimer, {{passive: true}});
      }});
      window.addEventListener('pagehide', stopCamera);
      resetIdleTimer();
      setPresenceState(statusText && statusText.textContent.trim() === 'Present');
      startCamera().then(function() {{ setMessage(''); }}).catch(function(error) {{ setMessage(error.message, 'error'); }});
    }})();
    </script>
    """
    return html_page("Présence", user, body)


def render_owner_initialization_prompt(user, child_count):
    if user["role"] != "boss" or int(child_count or 0) != 0:
        return ""
    return """
    <style>
      .owner-setup-overlay { position:fixed; inset:0; z-index:3000; display:flex; align-items:center; justify-content:center; padding:20px; background:rgba(15,35,42,.48); backdrop-filter:blur(3px); }
      .owner-setup-dialog { width:min(620px,100%); max-height:calc(100vh - 40px); overflow-y:auto; position:relative; padding:26px; border:1px solid #c8dfe5; border-radius:18px; background:#fff; box-shadow:0 28px 80px rgba(15,35,42,.30); }
      .owner-setup-close { position:absolute; top:12px; right:12px; width:34px; height:34px; padding:0; border:0; border-radius:50%; background:#eef4f5; color:#36565c; font-size:22px; line-height:1; cursor:pointer; }
      .owner-setup-language { position:absolute; top:13px; right:54px; display:inline-flex; gap:3px; padding:3px; border:1px solid #d7e0e3; border-radius:999px; background:#f4f7f8; }
      .owner-setup-language button { min-width:34px; padding:5px 7px; border:0; border-radius:999px; background:transparent; color:#52666b; font-size:11px; font-weight:900; cursor:pointer; }
      .owner-setup-language button[aria-pressed="true"] { background:#2f80c2; color:#fff; }
      .owner-setup-kicker { margin:0 128px 5px 0; color:#2f80c2; font-size:12px; font-weight:900; letter-spacing:.1em; text-transform:uppercase; }
      .owner-setup-dialog h2 { margin:0 42px 8px 0; color:#173b3f; font-size:25px; }
      .owner-setup-intro { margin:0 0 18px; color:#52666b; line-height:1.5; }
      .owner-setup-steps { display:grid; gap:10px; }
      .owner-setup-step { display:grid; grid-template-columns:34px minmax(0,1fr); gap:11px; align-items:start; padding:13px; border:1px solid #dbe7e9; border-radius:13px; background:#f8fbfb; }
      .owner-setup-number { display:grid; width:30px; height:30px; place-items:center; border-radius:50%; background:#e5f2fa; color:#1f6fa9; font-weight:900; }
      .owner-setup-step strong { display:block; margin:1px 0 4px; color:#173b3f; }
      .owner-setup-step p { margin:0; color:#52666b; font-size:14px; line-height:1.45; }
      .owner-setup-actions { display:flex; flex-wrap:wrap; gap:9px; margin-top:18px; }
      .owner-setup-actions .btn { text-align:center; }
      @media (max-width:640px) { .owner-setup-overlay { padding:12px; align-items:flex-end; } .owner-setup-dialog { max-height:calc(100vh - 24px); padding:22px 17px 18px; border-radius:18px 18px 12px 12px; } .owner-setup-dialog h2 { font-size:21px; } .owner-setup-step { padding:11px; } .owner-setup-actions { display:grid; grid-template-columns:1fr; } .owner-setup-actions .btn { width:100%; } }
    </style>
    <div class="owner-setup-overlay" id="owner-setup-overlay" role="dialog" aria-modal="true" aria-labelledby="owner-setup-title">
      <div class="owner-setup-dialog">
        <button class="owner-setup-close" type="button" data-owner-setup-close data-aria-fr="Fermer" data-aria-en="Close" aria-label="Fermer">&times;</button>
        <div class="owner-setup-language" role="group" aria-label="Language"><button type="button" data-owner-language="fr" aria-pressed="true">FR</button><button type="button" data-owner-language="en" aria-pressed="false">EN</button></div>
        <p class="owner-setup-kicker" data-fr="Premiers réglages" data-en="First steps">Premiers réglages</p>
        <h2 id="owner-setup-title" data-fr="Vous devez initialiser votre espace de travail" data-en="You need to initialize your workspace">Vous devez initialiser votre espace de travail</h2>
        <p class="owner-setup-intro" data-fr="Votre garderie ne contient encore aucun enfant. Effectuez les étapes suivantes pour commencer." data-en="Your childcare centre does not have any children yet. Complete the following steps to get started.">Votre garderie ne contient encore aucun enfant. Effectuez les étapes suivantes pour commencer.</p>
        <div class="owner-setup-steps">
          <div class="owner-setup-step">
            <span class="owner-setup-number">1</span>
            <div><strong>LIEU TRAVAIL MOBILE</strong><p data-fr="Configurez les coordonnées du lieu de travail pour permettre la présence mobile du personnel." data-en="Set the work location coordinates to enable mobile staff attendance.">Configurez les coordonnées du lieu de travail pour permettre la présence mobile du personnel.</p></div>
          </div>
          <div class="owner-setup-step">
            <span class="owner-setup-number">2</span>
            <div><strong>ACCOUNT ET INVITER</strong><p data-fr="Ajoutez les employés et les enfants, puis envoyez une invitation ou transmettez le nom d’utilisateur et le mot de passe temporaire." data-en="Add staff and children, then send an invitation or provide the username and temporary password.">Ajoutez les employés et les enfants, puis envoyez une invitation ou transmettez le nom d’utilisateur et le mot de passe temporaire.</p></div>
          </div>
        </div>
        <div class="owner-setup-actions">
          <a class="btn primary" href="/mobile-invitations#work-location" data-fr="Configurer le lieu" data-en="Set work location">Configurer le lieu</a>
          <a class="btn green" href="/users" data-fr="Ajouter employés et enfants" data-en="Add staff and children">Ajouter employés et enfants</a>
          <button class="btn gray" type="button" data-owner-setup-close data-fr="Plus tard" data-en="Later">Plus tard</button>
        </div>
      </div>
    </div>
    <script>
    (function() {
      const overlay = document.getElementById('owner-setup-overlay');
      if (!overlay) return;
      function setLanguage(language) {
        const selected = language === 'en' ? 'en' : 'fr';
        overlay.querySelectorAll('[data-fr][data-en]').forEach(function(element) {
          element.textContent = element.getAttribute('data-' + selected) || '';
        });
        overlay.querySelectorAll('[data-aria-fr][data-aria-en]').forEach(function(element) {
          element.setAttribute('aria-label', element.getAttribute('data-aria-' + selected) || '');
        });
        overlay.querySelectorAll('[data-owner-language]').forEach(function(button) {
          button.setAttribute('aria-pressed', button.getAttribute('data-owner-language') === selected ? 'true' : 'false');
        });
        document.documentElement.lang = selected;
        try { window.localStorage.setItem('pititpas-language', selected); } catch (_error) {}
      }
      function closeGuide() { overlay.remove(); }
      overlay.querySelectorAll('[data-owner-language]').forEach(function(button) {
        button.addEventListener('click', function() { setLanguage(button.getAttribute('data-owner-language')); });
      });
      overlay.querySelectorAll('[data-owner-setup-close]').forEach(function(button) {
        button.addEventListener('click', closeGuide);
      });
      overlay.addEventListener('click', function(event) {
        if (event.target === overlay) closeGuide();
      });
      document.addEventListener('keydown', function(event) {
        if (event.key === 'Escape' && document.getElementById('owner-setup-overlay')) closeGuide();
      });
      const firstAction = overlay.querySelector('a');
      let savedLanguage = '';
      try { savedLanguage = window.localStorage.getItem('pititpas-language') || ''; } catch (_error) {}
      setLanguage(savedLanguage === 'en' ? 'en' : 'fr');
      if (firstAction) window.setTimeout(function() { firstAction.focus(); }, 0);
    })();
    </script>
    """

def render_dashboard(user, query):
    with connect_db() as conn:
        project_child_count = conn.execute(
            "SELECT COUNT(*) FROM persons WHERE role = 'children' AND project_id = ?",
            (effective_project_id(conn, user),),
        ).fetchone()[0]
        owner_initialization_html = render_owner_initialization_prompt(user, project_child_count)
        classes = classes_for_user(user, conn)
        selected_class = query.get("class", [get_last_selected_class(conn, user["id"])])[0]
        selected_date = query.get("date", [today_text()])[0]
        selected_child_id = query.get("child_id", [""])[0]
        selected_sort = query.get("sort", ["class"])[0]
        if selected_sort not in {"class", "name"}:
            selected_sort = "class"
        if selected_class not in classes and selected_class != "all":
            selected_class = classes[0] if classes else "all"
        set_last_selected_class(conn, user["id"], selected_class)
        children = get_children(conn, user, selected_class)
        is_child_account = user["role"] == "children"
        show_child_actions = user["role"] != "cook"
        child_can_mark_self = bool(is_child_account and selected_date == today_text() and user["person_id"])
        if selected_sort == "name":
            children = sorted(children, key=lambda child: ((child["name"] or "").casefold(), (child["class_name"] or "").casefold()))
        else:
            children = sorted(children, key=lambda child: ((child["class_name"] or "Unassigned").casefold(), (child["name"] or "").casefold()))
        if children and (not selected_child_id or not any(str(child["id"]) == selected_child_id for child in children)):
            selected_child_id = str(children[0]["id"])
        selected_child = None
        for child in children:
            if str(child["id"]) == selected_child_id:
                selected_child = child
                break
        if selected_child is None and children:
            selected_child = children[0]
            selected_child_id = str(selected_child["id"])
        counts = count_statuses(conn, children, selected_date)
        version = dashboard_version(conn, children, selected_date)
        present_count = counts["P"]
        absent_count = counts["A"]
        closed_count = counts["F"]
        total = len(children)
        staff_compact_dashboard = user["role"] not in {"boss", "children"}
        arrival_chart_html = "" if is_child_account else render_dashboard_arrival_chart(conn, children, selected_date)
        summary_rows = []
        by_class = {}
        for child in children:
            by_class.setdefault(child["class_name"] or "Unassigned", []).append(child)
        for class_name in sorted(by_class):
            class_children = by_class[class_name]
            class_counts = count_statuses(conn, class_children, selected_date)
            summary_rows.append((class_name, len(class_children), class_counts["P"], class_counts["A"], class_counts["F"]))
        cards = []
        for child in children:
            status = current_child_status(conn, child["id"], selected_date)
            status_class = {"P": "present", "A": "absent", "F": "closed"}.get(status, "absent")
            photo_url = child_card_image_url(child["photo_path"])
            image_html = f'<img src="{photo_url}" alt="{html.escape(child["name"])}">' if photo_url else '<div class="muted">No photo</div>'
            card_href = f"/dashboard?class={quote(selected_class)}&date={quote(selected_date)}&sort={quote(selected_sort)}"
            selected_class_marker = "selected" if show_child_actions and str(child["id"]) == selected_child_id else ""
            if show_child_actions:
                card_href = f"{card_href}&child_id={child['id']}#selected-child-actions"
            cards.append(
                f"""
                <a class="card-link" href="{card_href}">
                  <div class="card {status_class} {selected_class_marker}">
                    <div class="photo">{image_html}</div>
                    <div class="content">
                      <div class="name">{html.escape(child['name'])}</div>
                      <div class="class-tag">{html.escape(child['class_name'] or 'Unassigned')}</div>
                      <div class="badge {status_class}">{status_label(status)}</div>
                      <div class="small muted">{html.escape(selected_date)}</div>
                    </div>
                  </div>
                </a>
                """
            )
        summary_html = "".join(
            f"<tr><td>{html.escape(name)}</td><td>{total_count}</td><td>{p}</td><td>{a}</td><td>{fcount}</td></tr>"
            for name, total_count, p, a, fcount in summary_rows
        )
        class_summary_body_html = summary_html or '<tr><td colspan="5" class="muted">No data</td></tr>'
        if staff_compact_dashboard:
            total_summary_html = f"<tr class=\"summary-total\"><td>Total</td><td>{total}</td><td>{present_count}</td><td>{absent_count}</td><td>{closed_count}</td></tr>"
            class_summary_body_html = total_summary_html + summary_html
        class_count_items = "".join(
            f'<span class="count-chip">{html.escape(name)}: {total_count}</span>'
            for name, total_count, _p, _a, _fcount in summary_rows
        )
        class_count_html = f'<div class="count-strip"><span class="count-chip strong">Toute: {total}</span>{class_count_items}</div>'
        control_options = "".join(
            f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{"Toute" if cls == "all" else html.escape(cls)}</option>'
            for cls in (["all"] + classes)
        )
        dashboard_filters_html = "" if is_child_account else f"""
              <form method="get" action="/dashboard" class="dashboard-filters" id="dashboard-filters">
                <div class="dashboard-filter-row">
                  <label>Groupe</label>
                  <select name="class" id="dashboard-class" onchange="this.form.submit()">{control_options}</select>
                </div>
                <div class="dashboard-filter-row">
                  <label>Date</label>
                  <input type="date" name="date" value="{html.escape(selected_date)}" onchange="this.form.submit()">
                </div>
              </form>
        """
        sort_options = "".join(
            f'<option value="{value}" {"selected" if value == selected_sort else ""}>{label}</option>'
            for value, label in (("class", "Groupe"), ("name", "Nom"))
        )
        child_options = "".join(
            f'<option value="{child["id"]}" {"selected" if str(child["id"]) == selected_child_id else ""}>{html.escape(child["name"])}</option>'
            for child in children
        )
        selected_name = html.escape(selected_child["name"]) if selected_child else "No child selected"
        selected_class_name = html.escape(selected_child["class_name"] or "Unassigned") if selected_child else ""
        selected_status = current_child_status(conn, selected_child["id"], selected_date) if selected_child else "A"
        can_mark_selected = can_edit_child(user) or child_can_mark_self
        checkin_disabled = selected_status == "P" or selected_status == "F" or not can_mark_selected or not selected_child
        checkout_disabled = selected_status == "A" or selected_status == "F" or not can_mark_selected or not selected_child
        checkin_class = "green" if not checkin_disabled else "gray"
        checkout_class = "primary" if not checkout_disabled else "gray"
        checkin_label = "Arrivée"
        checkout_label = "Départ"
        if selected_status == "P":
            checkin_label = "Déjà présent"
        elif selected_status == "A":
            checkout_label = "Déjà sorti"
        elif selected_status == "F":
            checkin_label = "Fermé"
            checkout_label = "Fermé"
        action_disabled_note = "" if can_mark_selected else '<div class="small muted">Editing is not allowed for this account.</div>'
        clear_day_html = ""
        if user["role"] in {"principal", "boss"}:
            clear_day_html = f"""
                <form method="post" action="/child/{selected_child['id'] if selected_child else 0}/delete-day" onsubmit="return confirm('Clear attendance for {selected_name} on {html.escape(selected_date)} ?')" style="display:inline">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <button class="btn red" type="submit">Effacer la journée</button>
                </form>
            """
        selected_recent_rows = ""
        selected_photo_url = ""
        if selected_child and user["role"] == "boss":
            selected_recent = latest_attendance_rows(conn, selected_child["id"], 10)
            selected_recent_rows = "".join(
                f"<tr><td>{html.escape(r['timestamp'])}</td><td>{html.escape(r['event_type'])}</td><td>{html.escape(r['actor_name'] or 'System')}</td></tr>"
                for r in selected_recent
            )
            selected_photo_url = child_card_image_url(selected_child["photo_path"]) or ""
        selected_status_class = {"P": "present", "A": "absent", "F": "closed"}.get(selected_status, "absent")
        admin_tools_html = ""
        children_panel_html = "" if is_child_account else f"""
          <div class="panel">
            <div class="cards">{''.join(cards) if cards else '<div class="muted">No children found for this scope.</div>'}</div>
          </div>
        """
        selected_recent_html = "" if user["role"] != "boss" else f"""
              <div class="table-wrap">
                <table>
                  <thead><tr><th>Timestamp</th><th>Event</th><th>By</th></tr></thead>
                  <tbody>{selected_recent_rows or '<tr><td colspan="3" class="muted">No records</td></tr>'}</tbody>
                </table>
              </div>
        """
        class_summary_panel_class = "panel staff-class-summary" if staff_compact_dashboard else "panel"
        class_summary_title = "" if staff_compact_dashboard else "<h3>Groupe</h3>"
        class_summary_first_header = "<th></th>" if staff_compact_dashboard else "<th>Groupe</th>"
        class_summary_html = "" if is_child_account else f"""
            <div class="{class_summary_panel_class}">
              {class_summary_title}
              <div class="table-wrap">
                <table>
                  <thead><tr>{class_summary_first_header}<th>Toute</th><th>P</th><th>A</th><th>F</th></tr></thead>
                  <tbody>{class_summary_body_html}</tbody>
                </table>
              </div>
            </div>
        """
        if staff_compact_dashboard:
            children_panel_html = f"""
          <div class="panel">
            {class_summary_html}
            <div class="cards">{''.join(cards) if cards else '<div class="muted">No children found for this scope.</div>'}</div>
          </div>
        """
            class_summary_html = ""
        dashboard_grid_class = "grid" if is_child_account else "grid two-col"
        if user["role"] in {"principal", "boss"}:
            export_url = "/export.xlsx"
            admin_tools_html = f"""
            <div class="panel">
              <div class="btn-row">
                <a class="btn" href="{export_url}">Exporter Excel</a>
              </div>
            </div>
            """
        dashboard_overview_panel_html = "" if is_child_account else f"""
        <div class="panel">
          <h2 class="dashboard-tableau-title">Tableau</h2>
          <div class="dashboard-overview">
            <div>
              <div class="action-panel">
                <div class="action-card">
                  {dashboard_filters_html}
                </div>
              </div>
              <div class="stats">
                <div class="stat"><div class="muted">Enfants</div><div class="value">{total}</div></div>
                <div class="stat"><div class="muted">Present</div><div class="value" style="color:var(--green)">{present_count}</div></div>
                <div class="stat"><div class="muted">Absence</div><div class="value" style="color:var(--gray)">{absent_count}</div></div>
                <div class="stat"><div class="muted">Closed</div><div class="value" style="color:var(--amber)">{closed_count}</div></div>
              </div>
            </div>
            {arrival_chart_html}
          </div>
        </div>
        """
        dashboard_root_classes = []
        if is_child_account:
            dashboard_root_classes.append("child-dashboard")
        elif staff_compact_dashboard:
            dashboard_root_classes.append("staff-compact-dashboard")
        if user["role"] in {"boss", "principal"}:
            dashboard_root_classes.append("admin-compact-dashboard")
        if user["role"] == "cook":
            dashboard_root_classes.append("cook-dashboard")
        dashboard_root_class = " ".join(dashboard_root_classes)
        body = f"""
        <style>
        .cook-dashboard .two-col {{ grid-template-columns:1fr; }}
        .cook-dashboard .dashboard-side {{ display:none; }}
        .dashboard-tableau-title {{ display:none; }}
        .dashboard-filter-row {{ display:grid; grid-template-columns:auto minmax(0,1fr); gap:8px; align-items:center; }}
        .dashboard-filter-row label {{ margin:0; white-space:nowrap; }}
        .dashboard-filter-row select,
        .dashboard-filter-row input {{ width:100%; min-width:0; }}
        @media (max-width:720px) {{
          .dashboard-filters {{ grid-template-columns:1fr !important; gap:6px; }}
          .staff-compact-dashboard .dashboard-overview .stats {{ display:none !important; }}
          .staff-compact-dashboard .dashboard-overview {{ display:block; }}
          .staff-compact-dashboard .dashboard-overview .action-panel {{ margin-bottom:0; }}
          .staff-compact-dashboard > .panel:first-child {{ margin-bottom:8px; }}
          .staff-compact-dashboard .cards {{ grid-template-columns:repeat(2,minmax(0,1fr)); gap:3px; }}
          .staff-compact-dashboard .card {{ min-height:38px; grid-template-columns:30px minmax(0,1fr); padding:3px; gap:4px; }}
          .staff-compact-dashboard .card .photo,
          .staff-compact-dashboard .card .photo img {{ width:28px; height:28px; }}
          .staff-compact-dashboard .card .content {{ gap:0; }}
          .staff-compact-dashboard .card .name {{ font-size:11px; line-height:1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .staff-compact-dashboard .card .class-tag,
          .staff-compact-dashboard .card .small {{ font-size:9px; line-height:1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .staff-compact-dashboard .card .badge {{ font-size:9px; padding:1px 4px; margin-top:0; line-height:1; }}
          .staff-compact-dashboard .staff-class-summary {{ padding:0; border:0; box-shadow:none; background:transparent; margin-bottom:6px; }}
          .staff-compact-dashboard .staff-class-summary .table-wrap {{ overflow-x:visible; }}
          .staff-compact-dashboard .staff-class-summary table {{ width:auto; min-width:0; table-layout:fixed; }}
          .staff-compact-dashboard .staff-class-summary th,
          .staff-compact-dashboard .staff-class-summary td {{ padding:3px 5px; font-size:11px; white-space:nowrap; }}
          .staff-compact-dashboard .staff-class-summary th:first-child,
          .staff-compact-dashboard .staff-class-summary td:first-child {{ width:86px; padding-left:0; }}
          .staff-compact-dashboard .staff-class-summary th:not(:first-child),
          .staff-compact-dashboard .staff-class-summary td:not(:first-child) {{ width:30px; text-align:center; }}
          .staff-compact-dashboard .staff-class-summary .summary-total td {{ font-weight:700; background:#f4f7f6; }}
          .staff-compact-dashboard .selected-child-panel {{ padding:8px; }}
          .staff-compact-dashboard .selected-child-panel h3 {{ display:none; }}
          .staff-compact-dashboard .selected-child-head {{ grid-template-columns:44px minmax(0,1fr); gap:7px; margin-bottom:6px; }}
          .staff-compact-dashboard .selected-child-head img,
          .staff-compact-dashboard .selected-child-head .muted {{ width:44px; height:44px; }}
          .staff-compact-dashboard .selected-child-name {{ font-size:15px; line-height:1.1; }}
          .staff-compact-dashboard .action-buttons {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(72px,1fr)); gap:4px; margin-bottom:4px !important; }}
          .staff-compact-dashboard .action-buttons form {{ min-width:0; }}
          .staff-compact-dashboard .action-buttons .btn {{ width:100%; min-width:0; min-height:34px; padding:5px 4px; font-size:11px; line-height:1.05; }}
          .admin-compact-dashboard .panel {{ min-width:0; }}
          .admin-compact-dashboard .cards {{ width:100%; max-width:100%; min-width:0; grid-template-columns:repeat(2,minmax(0,1fr)); gap:2px; }}
          .admin-compact-dashboard .card-link {{ min-width:0; max-width:100%; overflow:hidden; }}
          .admin-compact-dashboard .card {{ width:100%; max-width:100%; min-width:0; min-height:34px; grid-template-columns:24px minmax(0,1fr); padding:2px; gap:3px; }}
          .admin-compact-dashboard .card .photo,
          .admin-compact-dashboard .card .photo img {{ width:22px; height:22px; min-width:0; }}
          .admin-compact-dashboard .card .content {{ gap:0; min-width:0; overflow:hidden; }}
          .admin-compact-dashboard .card .name {{ display:block; width:100%; min-width:0; font-size:10px; line-height:1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .admin-compact-dashboard .card .class-tag,
          .admin-compact-dashboard .card .small {{ display:block; max-width:100%; min-width:0; font-size:8px; line-height:1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .admin-compact-dashboard .card .badge {{ max-width:100%; min-width:0; font-size:8px; padding:1px 3px; margin-top:0; line-height:1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .admin-compact-dashboard .dashboard-side {{ gap:8px !important; min-width:0; }}
          .admin-compact-dashboard .dashboard-side .panel {{ padding:8px; }}
          .admin-compact-dashboard .dashboard-side .table-wrap {{ width:100%; max-width:100%; overflow-x:visible; }}
          .admin-compact-dashboard .dashboard-side table {{ width:100%; min-width:0 !important; table-layout:fixed; }}
          .admin-compact-dashboard .dashboard-side th,
          .admin-compact-dashboard .dashboard-side td {{ padding:3px 4px; font-size:10px; line-height:1.05; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
          .admin-compact-dashboard .dashboard-side th:first-child,
          .admin-compact-dashboard .dashboard-side td:first-child {{ width:42%; }}
          .admin-compact-dashboard .dashboard-side th:not(:first-child),
          .admin-compact-dashboard .dashboard-side td:not(:first-child) {{ text-align:center; }}
          .admin-compact-dashboard .selected-child-panel table th:first-child,
          .admin-compact-dashboard .selected-child-panel table td:first-child {{ width:44%; }}
          .admin-compact-dashboard .selected-child-panel table th:nth-child(2),
          .admin-compact-dashboard .selected-child-panel table td:nth-child(2) {{ width:24%; }}
          .admin-compact-dashboard .selected-child-panel table th:nth-child(3),
          .admin-compact-dashboard .selected-child-panel table td:nth-child(3) {{ width:32%; }}
        }}
        </style>
        <div class="{dashboard_root_class}">
        {dashboard_overview_panel_html}
          <div class="{dashboard_grid_class}" style="margin-top:{'0' if is_child_account else '16px'}">
          {children_panel_html}
            <div class="grid dashboard-side" style="gap:16px">
            <div class="panel selected-child-panel" id="selected-child-actions">
              <h3>Enfant</h3>
              <div class="selected-child-head {selected_status_class}">
                {f'<img src="{selected_photo_url}" alt="{selected_name}">' if selected_photo_url else '<div class="muted">No photo</div>'}
                <div>
                  <div class="selected-child-name">{selected_name}</div>
                  <div class="small muted">{selected_class_name}</div>
                  <div class="badge {selected_status_class}">{status_label(selected_status)}</div>
                </div>
              </div>
              <div class="action-buttons" style="margin-bottom:10px">
                <form method="post" action="/child/{selected_child['id'] if selected_child else 0}/event" onsubmit="return confirm('Check in {selected_name} ?')" style="display:inline">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <input type="hidden" name="event_type" value="checkin">
                  <button class="btn {checkin_class}" type="submit" {"disabled" if checkin_disabled else ""}>{checkin_label}</button>
                </form>
                <form method="post" action="/child/{selected_child['id'] if selected_child else 0}/event" onsubmit="return confirm('Check out {selected_name} ?')" style="display:inline">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <input type="hidden" name="event_type" value="checkout">
                  <button class="btn {checkout_class}" type="submit" {"disabled" if checkout_disabled else ""}>{checkout_label}</button>
                </form>
                {clear_day_html}
              </div>
              {action_disabled_note}
              {selected_recent_html}
            </div>
            {class_summary_html}
            {admin_tools_html}
          </div>
        </div>
        </div>
        {owner_initialization_html}
      <script>
        (function() {{
          const version = {version};
          const currentUrl = new URL(window.location.href);
          function poll() {{
            fetch('/api/dashboard-version?class=' + encodeURIComponent(currentUrl.searchParams.get('class') || '{html.escape(selected_class)}') + '&date=' + encodeURIComponent(currentUrl.searchParams.get('date') || '{html.escape(selected_date)}') + '&_=' + Date.now(), {{
              credentials: 'same-origin',
              cache: 'no-store'
            }})
            .then(r => r.ok ? r.json() : null)
            .then(data => {{
              if (!data) return;
              if (typeof data.version === 'number' && data.version !== version) {{
                window.location.reload();
              }}
            }})
            .catch(() => {{}});
          }}
          setInterval(poll, 5000);
        }})();
        </script>
        """
        return html_page("Tableau", user, body)


def render_child_detail(user, child_id, query):
    with connect_db() as conn:
        child = conn.execute(
            "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
            (child_id, effective_project_id(conn, user)),
        ).fetchone()
        if not child:
            return html_page("Not Found", user, '<div class="panel">Child not found.</div>')
        if not can_view_all_classes(user) and child["class_name"] not in classes_for_user(user, conn):
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to view this child.</div>')
        selected_date = query.get("date", [today_text()])[0]
        status = current_child_status(conn, child["id"], selected_date)
        history_panel_html = ""
        if user["role"] in {"boss", "principal"}:
            rows = latest_attendance_rows(conn, child["id"], 30)
            rows_html = "".join(
                f"<tr><td>{html.escape(r['timestamp'])}</td><td>{html.escape(r['event_type'])}</td><td>{html.escape(r['actor_name'] or 'System')}</td></tr>"
                for r in rows
            )
            history_panel_html = f"""
            <div class="panel">
            <h3>Recent Attendance</h3>
            <div class="table-wrap">
              <table>
                <thead><tr><th>Timestamp</th><th>Event</th><th>By</th></tr></thead>
                <tbody>{rows_html or '<tr><td colspan="3" class="muted">No records</td></tr>'}</tbody>
              </table>
            </div>
          </div>
            """
        photo_url = child_card_image_url(child["photo_path"])
        badge_class = {"P": "present", "A": "absent", "F": "closed"}.get(status, "absent")
        body = f"""
        <div class="grid two-col">
          <div class="panel">
            <h2>{html.escape(child['name'])}</h2>
            <div class="muted">{html.escape(child['class_name'] or 'Unassigned')}</div>
            <div class="no-print" style="margin:8px 0 12px">
              <a class="btn" href="/dashboard">Retour au tableau de bord</a>
            </div>
            <div style="margin:14px 0">
              {f'<img src="{photo_url}" alt="{html.escape(child["name"])}" style="max-width:25%;border-radius:8px;border:1px solid var(--line)">' if photo_url else '<div class="muted">No photo</div>'}
            </div>
            <div class="badge {badge_class}" style="margin-bottom:12px">{status_label(status)}</div>
            <div class="muted-box no-print">
              No direct actions on this page.
            </div>
          </div>
          {history_panel_html}
        </div>
        """
        return html_page(child["name"], user, body)


def contact_list_rows(conn, user):
    return conn.execute(
        """
        SELECT web_users.id, web_users.username, web_users.display_name, web_users.role,
               COALESCE(persons.class_name, '') AS linked_class_name,
               COALESCE(user_profiles.phones_json, '[]') AS phones_json,
               COALESCE(user_profiles.emails_json, '[]') AS emails_json
        FROM web_users
        LEFT JOIN user_profiles ON user_profiles.user_id = web_users.id
        LEFT JOIN persons ON persons.id = web_users.person_id
        WHERE web_users.is_active = 1
          AND web_users.project_id = ?
        ORDER BY web_users.role, web_users.display_name
        """,
        (effective_project_id(conn, user),),
    ).fetchall()


def contact_values(row):
    try:
        phones = json.loads(row["phones_json"] or "[]")
    except json.JSONDecodeError:
        phones = []
    try:
        emails = json.loads(row["emails_json"] or "[]")
    except json.JSONDecodeError:
        emails = []
    return phones, emails


def contact_role_label(row):
    if row["role"] == "children":
        class_name = (row["linked_class_name"] or "").strip()
        if class_name:
            return class_name
    return ROLE_LABELS.get(row["role"], row["role"])


def render_contacts(user, query=None):
    if user["role"] not in {"principal", "boss", "teacher", "cook"}:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view contacts.</div>')
    query = query or {}
    sort_key = query.get("sort", ["name"])[0]
    sort_dir = query.get("dir", ["asc"])[0]
    if sort_key not in {"name", "role"}:
        sort_key = "name"
    if sort_dir not in {"asc", "desc"}:
        sort_dir = "asc"
    with connect_db() as conn:
        rows = contact_list_rows(conn, user)
    rows = sorted(
        rows,
        key=lambda row: (
            (contact_role_label(row) if sort_key == "role" else (row["display_name"] or row["username"] or "")).lower(),
            (row["display_name"] or row["username"] or "").lower(),
        ),
        reverse=(sort_dir == "desc"),
    )
    def sort_header(key, label):
        next_dir = "desc" if sort_key == key and sort_dir == "asc" else "asc"
        marker = " ▲" if sort_key == key and sort_dir == "asc" else (" ▼" if sort_key == key else "")
        return f'<a href="/contacts?sort={key}&dir={next_dir}">{html.escape(label + marker)}</a>'
    body_rows = []
    for row in rows:
        phones, emails = contact_values(row)
        body_rows.append(
            f"<tr>"
            f"<td>{html.escape(row['display_name'] or row['username'])}</td>"
            f"<td>{html.escape(contact_role_label(row))}</td>"
            f"<td>{html.escape('; '.join(phones))}</td>"
            f"<td>{html.escape('; '.join(emails))}</td>"
            f"</tr>"
        )
    body = f"""
    <div class="panel">
      <h2>Phone and e-mail list</h2>
      <div class="toolbar">
        <a class="btn primary" href="/contacts.xlsx">Exporter Excel</a>
      </div>
      <div class="table-wrap">
        <table>
          <thead><tr><th>{sort_header("name", "Name")}</th><th>{sort_header("role", "Role")}</th><th>Phones</th><th>e-mail</th></tr></thead>
          <tbody>{''.join(body_rows) or '<tr><td colspan="4" class="muted">No contacts found.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Contacts", user, body)


def build_contacts_xlsx(user):
    with connect_db() as conn:
        rows = contact_list_rows(conn, user)
    export_rows = []
    for row in rows:
        phones, emails = contact_values(row)
        export_rows.append([
            row["display_name"] or row["username"],
            contact_role_label(row),
            "; ".join(phones),
            "; ".join(emails),
        ])
    return build_xlsx_bytes([
        {
            "name": "Contacts",
            "headers": ["Name", "Role", "Phones", "MESSAGE"],
            "rows": export_rows,
        }
    ])


def build_users_xlsx(user):
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        rows = conn.execute(
            """
            SELECT web_users.*, persons.class_name AS linked_class_name,
                   mobile_devices.device_name, mobile_devices.last_seen_at
            FROM web_users
            LEFT JOIN persons ON persons.id = web_users.person_id
            LEFT JOIN mobile_devices ON mobile_devices.user_id = web_users.id AND mobile_devices.is_active = 1
            WHERE web_users.is_active = 1
              AND web_users.project_id = ?
            ORDER BY web_users.role, web_users.display_name, web_users.username
            """
            , (project_id,)
        ).fetchall()
    export_rows = []
    for row in rows:
        if row["role"] == "children":
            classes_text = (row["linked_class_name"] or "").strip()
        else:
            classes = safe_json_list(row["allowed_classes_json"])
            classes_text = ", ".join(classes) if classes else ""
        device_text = ""
        if row["device_name"] or row["last_seen_at"]:
            device_text = " / ".join(value for value in [row["device_name"], row["last_seen_at"]] if value)
        export_rows.append([
            row["username"],
            row["display_name"],
            ROLE_LABELS.get(row["role"], row["role"]),
            classes_text,
            row["created_at"],
            row["updated_at"],
        ])
    return build_xlsx_bytes([
        {
            "name": "Accounts",
            "headers": ["Username", "Name", "Role", "Classes", "Created", "Updated"],
            "rows": export_rows,
        }
    ])


def render_reports(user, query):
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        children = get_children(conn, user)
        person_id = query.get("person_id", [str(children[0]["id"]) if children else ""])[0]
        selected_format = query.get("format", ["detailed"])[0]
        selected_date = query.get("date", [today_text()])[0]
        if person_id:
            child = conn.execute(
                "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                (person_id, effective_project_id(conn, user)),
            ).fetchone()
        else:
            child = None
        if not child and children:
            child = children[0]
        if not child:
            return html_page("Reports", user, '<div class="panel">No children found.</div>')
        if not can_view_all_classes(user) and child["class_name"] not in classes:
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to view this child.</div>')
        try:
            chosen_date = datetime.strptime(selected_date, "%Y-%m-%d").date()
        except ValueError:
            chosen_date = datetime.now().date()
        start = chosen_date - timedelta(days=chosen_date.weekday())
        start_text = start.strftime("%Y-%m-%d")
        weeks = fiche_summary(conn, child["id"], start_text)
        sheet = render_fiche_calendar(weeks)
        body = f"""
        <div class="panel no-print">
          <h2>4-Week Fiche</h2>
          <form method="get" action="/reports" class="toolbar" style="margin-bottom:0">
            <div>
              <label>Child</label>
              <select name="person_id" onchange="this.form.submit()">
                {''.join(f'<option value="{c["id"]}" {"selected" if c["id"] == child["id"] else ""}>{html.escape(c["name"])}</option>' for c in children)}
              </select>
            </div>
            <div>
              <label>Date</label>
              <input type="date" name="date" value="{html.escape(selected_date)}" onchange="this.form.submit()">
            </div>
            <div>
              <label>Format</label>
              <select name="format">
                <option value="detailed" {"selected" if selected_format == "detailed" else ""}>Detailed 4 week</option>
                <option value="summary" {"selected" if selected_format == "summary" else ""}>Summary 4 week</option>
              </select>
            </div>
            <div>
              <button class="btn primary" type="submit" name="generate" value="1" data-wait-message="Génération du PDF..." data-wait-text="Génération..." data-download-wait="true">Générer le PDF</button>
            </div>
          </form>
        </div>
        <div class="panel" style="margin-top:16px">
          <div class="muted small">Child: {html.escape(child['name'])} &middot; Groupe: {html.escape(child['class_name'] or 'Unassigned')} &middot; Start: {html.escape(start_text)}</div>
          {sheet}
        </div>
        """
        return html_page("Reports", user, body)


def render_statistics_15min(user, query):
    if user["role"] not in {"principal", "boss"}:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view statistics.</div>')
    selected_date_text = query.get("date", [today_text()])[0]
    try:
        selected_date = datetime.strptime(selected_date_text, "%Y-%m-%d").date()
    except ValueError:
        selected_date = datetime.now().date()
    selected_date_text = selected_date.strftime("%Y-%m-%d")
    selected_month = selected_date.replace(day=1)
    prev_month = (selected_month - timedelta(days=1)).replace(day=1)
    next_month = (selected_month + timedelta(days=32)).replace(day=1)

    with connect_db() as conn:
        rows = attendance_export_source_rows(conn, selected_date_text)
        children = get_children(conn, user, "all")
        chart_html = render_dashboard_arrival_chart(conn, children, selected_date_text)
    summary_rows = build_presence_summary_rows(rows)
    table_rows = "".join(
        f"<tr><td>{html.escape(day)}</td><td>{html.escape(time)}</td><td>{present}</td><td>{html.escape(classes)}</td></tr>"
        for day, time, present, classes in summary_rows
    )

    calendar_rows = []
    for week in calendar.Calendar(firstweekday=0).monthdatescalendar(selected_month.year, selected_month.month):
        cells = []
        for day in week:
            day_text = day.strftime("%Y-%m-%d")
            classes = ["day-cell"]
            if day.month != selected_month.month:
                classes.append("out-month")
            if day_text == selected_date_text:
                classes.append("selected")
            if day_text == today_text():
                classes.append("today")
            cells.append(
                f'<td class="{" ".join(classes)}"><a href="/statistics?date={quote(day_text)}">{day.day}</a></td>'
            )
        calendar_rows.append(f"<tr>{''.join(cells)}</tr>")

    body = f"""
    <style>
      .stats-presence-top {{ display: grid; grid-template-columns: 360px minmax(720px, 1fr); gap: 28px; align-items: start; }}
      .stats-calendar-wrap {{ width: 100%; max-width: 360px; }}
      .stats-calendar {{ margin-top: 8px; border: 1px solid var(--line); border-radius: 8px; overflow: hidden; background: #fbfbfd; }}
      .stats-calendar table {{ width: 100%; table-layout: fixed; border-collapse: collapse; font-size: 12px; }}
      .stats-calendar th {{ background: #f3f4f6; color: var(--muted); font-weight: 700; }}
      .stats-calendar th, .stats-calendar td {{ text-align: center; padding: 3px 2px; border: 1px solid #eceff3; }}
      .stats-calendar td {{ background: #fff; }}
      .stats-calendar td.out-month a {{ color: #b6bcc6; }}
      .stats-calendar td.today a {{ font-weight: 700; color: #111827; }}
      .stats-calendar td.selected {{ background: #d7b5ff; }}
      .stats-calendar td.selected a {{ color: #000; font-weight: 700; }}
      .stats-calendar td a {{ display: block; min-height: 20px; line-height: 20px; border-radius: 4px; text-decoration: none; color: inherit; }}
      .stats-calendar td a:hover {{ background: #eef2ff; }}
      .stats-calendar-nav {{ display: flex; align-items: center; justify-content: space-between; gap: 6px; margin-bottom: 6px; }}
      .stats-calendar-nav .btn {{ padding: 5px 8px; }}
      @media (max-width: 1180px) {{ .stats-presence-top {{ grid-template-columns: 1fr; }} }}
    </style>
    {principal_self_panel}
    <div class="panel">
      <h2>Résumé des présences</h2>
      <div class="stats-presence-top">
        <div class="stats-calendar-wrap">
          <div class="stats-calendar-nav">
            <a class="btn" href="/statistics?date={quote(prev_month.strftime('%Y-%m-%d'))}">&lt;</a>
            <div class="muted small">{html.escape(selected_month.strftime('%B %Y'))}</div>
            <a class="btn" href="/statistics?date={quote(next_month.strftime('%Y-%m-%d'))}">&gt;</a>
          </div>
          <div class="stats-calendar">
            <table>
              <thead><tr><th>Mon</th><th>Tue</th><th>Wed</th><th>Thu</th><th>Fri</th><th>Sat</th><th>Sun</th></tr></thead>
              <tbody>{''.join(calendar_rows)}</tbody>
            </table>
          </div>
        </div>
        {chart_html}
      </div>
      <div class="muted small" style="margin-top:10px">Selected date: {html.escape(selected_date_text)}. Child attendance records: {len(rows)}</div>
      <div class="table-wrap" style="margin-top:10px">
        <table>
          <thead><tr><th>Date</th><th>Time</th><th>Children Present</th><th>Class Counts</th></tr></thead>
          <tbody>{table_rows or '<tr><td colspan="4" class="muted">No child attendance records are available for this date.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Résumé des présences", user, body)


def teacher_attendance_day_summary(conn, day_text, project_id=1):
    project_id = int(project_id or 1)
    teachers = conn.execute(
        """
        SELECT id, name, photo_path, created_at
        FROM persons
        WHERE role = 'teachers'
          AND project_id = ?
          AND id NOT IN (SELECT person_id FROM deleted_user_archives WHERE person_id IS NOT NULL AND project_id = ?)
        ORDER BY name COLLATE NOCASE
        """,
        (project_id, project_id),
    ).fetchall()
    rows = []
    total = len(teachers)
    present_now = 0
    arrived_today = 0
    not_arrived = 0
    total_checkins = 0
    total_checkouts = 0
    actual_hours_person_ids = actual_hours_staff_person_ids(conn, project_id)

    for teacher in teachers:
        events = conn.execute(
            """
            SELECT event_type, timestamp, COALESCE(snapshot_path, '') AS snapshot_path
            FROM attendance
            WHERE person_id = ? AND role = 'teachers' AND timestamp LIKE ?
            ORDER BY timestamp ASC, id ASC
            """,
            (teacher["id"], f"{day_text}%"),
        ).fetchall()
        checkin_events = [event for event in events if event["event_type"] == "checkin"]
        checkout_events = [event for event in events if event["event_type"] == "checkout"]
        checkins = [event["timestamp"] for event in checkin_events]
        checkouts = [event["timestamp"] for event in checkout_events]
        first_checkin_event = checkin_events[0] if checkin_events else None
        last_checkout_event = checkout_events[-1] if checkout_events else None
        total_checkins += len(checkins)
        total_checkouts += len(checkouts)
        latest_event = events[-1]["event_type"] if events else ""
        latest_time = events[-1]["timestamp"] if events else ""
        latest_snapshot_path = events[-1]["snapshot_path"] if events else ""
        status = "P" if latest_event == "checkin" else "A"
        if status == "P":
            present_now += 1
        if checkins:
            arrived_today += 1
        else:
            not_arrived += 1
        schedule = teacher_schedule_for_day(conn, teacher["name"], day_text, project_id)
        actual_work_hours = calculate_teacher_work_hours(
            day_text,
            checkins[0] if checkins else "",
            checkouts[-1] if checkouts else "",
            schedule["schedule_in"],
            use_schedule=int(teacher["id"]) not in actual_hours_person_ids,
        )
        rows.append(
            {
                "id": teacher["id"],
                "name": teacher["name"],
                "photo_path": teacher["photo_path"],
                "status": status,
                "first_checkin": checkins[0] if checkins else "",
                "last_checkout": checkouts[-1] if checkouts else "",
                "first_checkin_mobile": attendance_event_is_mobile(first_checkin_event),
                "last_checkout_mobile": attendance_event_is_mobile(last_checkout_event),
                "latest_event": latest_event,
                "latest_time": latest_time,
                "latest_snapshot_path": latest_snapshot_path,
                "event_count": len(events),
                "schedule_in": schedule["schedule_in"],
                "schedule_out": schedule["schedule_out"],
                "scheduled_hours": schedule["work_hours"],
                "scheduled_class": schedule["class_name"],
                "work_hours": actual_work_hours,
            }
        )
    return {
        "teachers": rows,
        "total": total,
        "present_now": present_now,
        "arrived_today": arrived_today,
        "not_arrived": not_arrived,
        "total_checkins": total_checkins,
        "total_checkouts": total_checkouts,
    }


def teacher_pay_hours_summary(conn, start_date_text, end_date_text, project_id=1):
    project_id = int(project_id or 1)
    try:
        start_date = datetime.strptime(start_date_text, "%Y-%m-%d").date()
        end_date = datetime.strptime(end_date_text, "%Y-%m-%d").date()
    except ValueError:
        start_date = local_now().date()
        end_date = start_date
    if end_date < start_date:
        start_date, end_date = end_date, start_date

    day_values = []
    current_day = start_date
    while current_day <= end_date:
        day_values.append(current_day.strftime("%Y-%m-%d"))
        current_day += timedelta(days=1)
    teachers = conn.execute(
        """
        SELECT id, name
        FROM persons
        WHERE role = 'teachers'
          AND project_id = ?
          AND id NOT IN (SELECT person_id FROM deleted_user_archives WHERE person_id IS NOT NULL AND project_id = ?)
        ORDER BY name COLLATE NOCASE
        """,
        (project_id, project_id),
    ).fetchall()

    rows = []
    actual_hours_person_ids = actual_hours_staff_person_ids(conn, project_id)
    for teacher in teachers:
        total_hours = 0.0
        schedule_total_hours = 0.0
        payable_days = 0
        event_count = 0
        open_record = False
        daily_values = {}
        for day_text in day_values:
            events = conn.execute(
                """
                SELECT event_type, timestamp
                FROM attendance
                WHERE person_id = ?
                  AND role = 'teachers'
                  AND timestamp LIKE ?
                ORDER BY timestamp ASC, id ASC
                """,
                (teacher["id"], f"{day_text}%"),
            ).fetchall()
            event_count += len(events)
            if events and events[-1]["event_type"] == "checkin":
                open_record = True
            checkins = [event["timestamp"] for event in events if event["event_type"] == "checkin"]
            checkouts = [event["timestamp"] for event in events if event["event_type"] == "checkout"]
            schedule = teacher_schedule_for_day(conn, teacher["name"], day_text, project_id)
            uses_actual_hours = int(teacher["id"]) in actual_hours_person_ids
            daily_value = calculate_teacher_work_hours(
                day_text,
                checkins[0] if checkins else "",
                checkouts[-1] if checkouts else "",
                schedule["schedule_in"],
                use_schedule=not uses_actual_hours,
            )
            if uses_actual_hours:
                schedule_total_hours += float(daily_value or 0)
            else:
                schedule_total_hours += float(schedule.get("work_hours") or 0)
            if daily_value:
                daily_values[day_text] = daily_value
                total_hours += float(daily_value)
                payable_days += 1
            else:
                daily_values[day_text] = ""
        rows.append(
            {
                "name": teacher["name"],
                "hours": total_hours,
                "schedule_hours": schedule_total_hours,
                "daily_hours": daily_values,
                "pairs": payable_days,
                "events": event_count,
                "open_record": open_record,
            }
        )
    return start_date.strftime("%Y-%m-%d"), end_date.strftime("%Y-%m-%d"), day_values, rows


def staff_in_out_rows(conn, person_id, start_date_text, end_date_text):
    try:
        start_date = datetime.strptime(start_date_text, "%Y-%m-%d").date()
        end_date = datetime.strptime(end_date_text, "%Y-%m-%d").date()
    except ValueError:
        start_date = local_now().date()
        end_date = start_date
    if end_date < start_date:
        start_date, end_date = end_date, start_date

    day_values = []
    current_day = start_date
    while current_day <= end_date:
        if current_day.weekday() < 5:
            day_values.append(current_day.strftime("%Y-%m-%d"))
        current_day += timedelta(days=1)

    rows = []
    person = conn.execute("SELECT name, project_id FROM persons WHERE id = ? AND role = 'teachers'", (person_id,)).fetchone()
    person_name = person["name"] if person else ""
    project_id = int(person["project_id"] or 1) if person else 1
    for day_text in day_values:
        events = conn.execute(
            """
            SELECT event_type, timestamp
            FROM attendance
            WHERE person_id = ?
              AND role = 'teachers'
              AND timestamp LIKE ?
            ORDER BY timestamp ASC, id ASC
            """,
            (person_id, f"{day_text}%"),
        ).fetchall()
        schedule = teacher_schedule_for_day(conn, person_name, day_text, project_id) if person_name else {"schedule_in": "", "schedule_out": ""}
        checkins = [event["timestamp"][11:16] for event in events if event["event_type"] == "checkin"]
        checkouts = [event["timestamp"][11:16] for event in events if event["event_type"] == "checkout"]
        rows.append(
            {
                "date": day_text,
                "in": checkins[0] if checkins else "",
                "out": checkouts[-1] if checkouts else "",
                "schedule_in": schedule["schedule_in"],
                "schedule_out": schedule["schedule_out"],
            }
        )
    return start_date.strftime("%Y-%m-%d"), end_date.strftime("%Y-%m-%d"), rows


def staff_in_out_panel_html(person, start_text, end_text, rows, heading="Présences des éducatrices"):
    heading_html = "" if heading == "Présences des éducatrices" else f"<h2>{html.escape(heading)}</h2>"
    table_rows = "".join(
        f"""
        <tr>
          <td>{html.escape(row['date'])}</td>
          <td>{html.escape(row['in'] or '-')}</td>
          <td>{html.escape(row['out'] or '-')}</td>
          <td>{html.escape(row['schedule_in'] or '-')}</td>
          <td>{html.escape(row['schedule_out'] or '-')}</td>
        </tr>
        """
        for row in rows
    )
    return f"""
    <div class="panel">
      {heading_html}
      <div class="muted">{html.escape(person['name'])}</div>
      <form method="get" action="/teacher-attendance" class="pay-hours-form staff-inout-range" data-staff-inout-range>
        <div>
          <label>Début</label>
          <input type="date" name="pay_start" value="{html.escape(start_text)}">
        </div>
        <div>
          <label>Fin</label>
          <input type="date" name="pay_end" value="{html.escape(end_text)}">
        </div>
      </form>
      <style>
        .staff-inout-range {{ display:grid; grid-template-columns:minmax(0, 1fr) minmax(0, 1fr); gap:8px; align-items:end; margin-top:10px; }}
        .staff-inout-range input[type="date"] {{ width:100%; min-width:0; }}
        .staff-inout-table {{ margin-top:12px; max-width:520px; }}
        .staff-inout-table table {{ table-layout:fixed; width:auto; min-width:0; }}
        .staff-inout-table th, .staff-inout-table td {{ padding:6px 8px; white-space:nowrap; }}
        .staff-inout-table th:nth-child(1), .staff-inout-table td:nth-child(1) {{ width:112px; }}
        .staff-inout-table th:nth-child(2), .staff-inout-table td:nth-child(2),
        .staff-inout-table th:nth-child(3), .staff-inout-table td:nth-child(3),
        .staff-inout-table th:nth-child(4), .staff-inout-table td:nth-child(4),
        .staff-inout-table th:nth-child(5), .staff-inout-table td:nth-child(5) {{ width:58px; text-align:center; }}
      </style>
      <div class="table-wrap staff-inout-table">
        <table>
          <thead><tr><th>Date</th><th>IN</th><th>OUT</th><th>S-IN</th><th>S-OUT</th></tr></thead>
          <tbody>{table_rows or '<tr><td colspan="5" class="muted">No records.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """


def staff_in_out_range_script():
    return """
    {principal_self_script}
    <script>
    (function() {
      const form = document.querySelector('[data-staff-inout-range]');
      if (!form) return;
      const start = form.querySelector('input[name="pay_start"]');
      const end = form.querySelector('input[name="pay_end"]');
      [start, end].forEach(function(input) {
        if (!input) return;
        input.addEventListener('change', function() {
          form.requestSubmit();
        });
      });
    })();
    </script>
    """


def render_staff_teacher_attendance(user, query):
    if user["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES or user["role"] == "boss":
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view teacher attendance.</div>')
    if not user["person_id"]:
        return html_page(
            "Présences éducatrices",
            user,
            '<div class="panel"><h2>Présences des éducatrices</h2><div class="alert warn">Ce compte n\'est pas lié à une fiche employé.</div></div>',
        )
    with connect_db() as conn:
        saved_start, saved_end = get_teacher_attendance_range(conn, user["id"], today_text(), today_text())
        default_start = query.get("pay_start", [saved_start])[0]
        default_end = query.get("pay_end", [saved_end])[0]
        person = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'teachers'", (user["person_id"],)).fetchone()
        if not person:
            return html_page("Présences éducatrices", user, '<div class="panel"><div class="alert warn">Fiche employé introuvable.</div></div>')
        start_text, end_text, rows = staff_in_out_rows(conn, int(user["person_id"]), default_start, default_end)
        set_teacher_attendance_range(conn, user["id"], start_text, end_text)
    body = staff_in_out_panel_html(person, start_text, end_text, rows) + staff_in_out_range_script()
    return html_page("Présences éducatrices", user, body)


def teacher_six_week_hours_summary(conn, end_date_text, project_id=1):
    try:
        end_date = datetime.strptime(end_date_text, "%Y-%m-%d").date()
    except ValueError:
        end_date = local_now().date()
    week_start = end_date - timedelta(days=end_date.weekday())
    weeks = []
    for offset in range(5, -1, -1):
        start = week_start - timedelta(days=offset * 7)
        end = start + timedelta(days=6)
        _start, _end, _days, rows = teacher_pay_hours_summary(conn, start.strftime("%Y-%m-%d"), end.strftime("%Y-%m-%d"), project_id)
        weeks.append(
            {
                "label": f"{start.strftime('%m-%d')}",
                "actual": sum(float(row["hours"] or 0) for row in rows),
                "schedule": sum(float(row["schedule_hours"] or 0) for row in rows),
            }
        )
    return weeks


def teacher_hours_trend_chart_html(weeks):
    chart_w, chart_h = 430, 145
    pad_l, pad_t, pad_r, pad_b = 38, 14, 14, 26
    plot_w = chart_w - pad_l - pad_r
    plot_h = chart_h - pad_t - pad_b
    max_value = max([week["actual"] for week in weeks] + [week["schedule"] for week in weeks] + [1])

    def points_for(key):
        points = []
        for index, week in enumerate(weeks):
            x = pad_l + (plot_w * index / (len(weeks) - 1) if len(weeks) > 1 else 0)
            y = pad_t + plot_h - (plot_h * float(week[key] or 0) / max_value)
            points.append((x, y))
        return points

    def smooth_path(points):
        if not points:
            return ""
        if len(points) == 1:
            return f"M {points[0][0]:.1f} {points[0][1]:.1f}"
        parts = [f"M {points[0][0]:.1f} {points[0][1]:.1f}"]
        for index in range(len(points) - 1):
            x0, y0 = points[index]
            x1, y1 = points[index + 1]
            cx0 = x0 + (x1 - x0) / 2
            cx1 = x1 - (x1 - x0) / 2
            parts.append(f"C {cx0:.1f} {y0:.1f}, {cx1:.1f} {y1:.1f}, {x1:.1f} {y1:.1f}")
        return " ".join(parts)

    actual_path = smooth_path(points_for("actual"))
    schedule_path = smooth_path(points_for("schedule"))
    grid = "".join(
        f'<line x1="{pad_l}" y1="{pad_t + plot_h * i / 4:.1f}" x2="{chart_w - pad_r}" y2="{pad_t + plot_h * i / 4:.1f}"></line>'
        for i in range(5)
    )
    x_labels = "".join(
        f'<text x="{pad_l + (plot_w * index / (len(weeks) - 1) if len(weeks) > 1 else 0):.1f}" y="{chart_h - 8}" text-anchor="middle">{html.escape(week["label"])}</text>'
        for index, week in enumerate(weeks)
    )
    y_labels = "".join(
        f'<text x="{pad_l - 6}" y="{pad_t + plot_h - (plot_h * i / 4):.1f}" text-anchor="end" dominant-baseline="middle">{round(max_value * i / 4)}</text>'
        for i in range(5)
    )
    return f"""
      <div class="teacher-hours-chart">
        <div class="dashboard-chart-head">
          <div class="dashboard-chart-title">6 SEMAINES</div>
          <div class="teacher-chart-legend"><span class="actual"></span>WORK <span class="schedule"></span>SCHEDULE</div>
        </div>
        <svg class="arrival-chart" viewBox="0 0 {chart_w} {chart_h}" preserveAspectRatio="none" style="height:145px">
          <g class="chart-grid">{grid}</g>
          <line x1="{pad_l}" y1="{pad_t}" x2="{pad_l}" y2="{pad_t + plot_h}" stroke="#cfd8e3" stroke-width="1"></line>
          <line x1="{pad_l}" y1="{pad_t + plot_h}" x2="{chart_w - pad_r}" y2="{pad_t + plot_h}" stroke="#cfd8e3" stroke-width="1"></line>
          {y_labels}
          {x_labels}
          <path class="chart-line teacher-actual-line" d="{actual_path}"></path>
          <path class="chart-line teacher-schedule-line" d="{schedule_path}"></path>
        </svg>
      </div>
    """


def parse_attendance_time_value(value):
    value = (value or "").strip()
    if not value:
        return ""
    for fmt in ("%H:%M", "%H:%M:%S"):
        try:
            return datetime.strptime(value, fmt).strftime("%H:%M:%S")
        except ValueError:
            pass
    raise ValueError("Invalid time value")


def time_picker_html(name, value="", element_id="", css_class="teacher-time-input"):
    value = (value or "").strip()
    selected_value = value if re.match(r"^\d{2}:\d{2}$", value) else ""
    input_id = f' id="{html.escape(element_id)}"' if element_id else ""
    selected_hour = selected_value[:2] if selected_value else ""
    selected_minute = selected_value[3:5] if selected_value else ""
    hour_options = '<option value="">--</option>' + "".join(
        f'<option value="{hour:02d}" {"selected" if f"{hour:02d}" == selected_hour else ""}>{hour:02d}</option>'
        for hour in range(24)
    )
    minute_options = '<option value="">--</option>' + "".join(
        f'<option value="{minute:02d}" {"selected" if f"{minute:02d}" == selected_minute else ""}>{minute:02d}</option>'
        for minute in range(60)
    )
    return f"""
      <div class="time-picker split-time-picker">
        <input{input_id} class="{html.escape(css_class)} time-picker-value" type="hidden" name="{html.escape(name)}" value="{html.escape(selected_value)}">
        <select class="time-picker-hour" name="{html.escape(name)}_hour" aria-label="Hour">{hour_options}</select>
        <span class="time-picker-separator">:</span>
        <select class="time-picker-minute" name="{html.escape(name)}_minute" aria-label="Minute">{minute_options}</select>
      </div>
    """


def locked_time_value_html(name, value):
    value = (value or "").strip()
    return (
        f'<input class="teacher-time-input time-picker-value" type="hidden" '
        f'name="{html.escape(name)}" value="{html.escape(value)}">'
        f'<span class="muted-box" style="display:inline-block;min-width:96px;padding:7px 8px">{html.escape(value or "-")}</span>'
    )


def attendance_event_is_mobile(event):
    return bool(event and (event["snapshot_path"] or "").strip())


def upsert_teacher_attendance_time(conn, actor, handler, teacher, day_text, event_type, time_value):
    parsed_time = parse_attendance_time_value(time_value)
    if not parsed_time:
        return False
    timestamp = f"{day_text} {parsed_time}"
    latest_event = conn.execute(
        """
        SELECT id, event_type, timestamp, COALESCE(snapshot_path, '') AS snapshot_path
        FROM attendance
        WHERE lower(name) = lower(?)
          AND role = 'teachers'
          AND timestamp LIKE ?
        ORDER BY timestamp DESC, id DESC
        LIMIT 1
        """,
        (teacher["name"], f"{day_text}%"),
    ).fetchone()
    if event_type == "checkout" and latest_event and latest_event["event_type"] == "checkin":
        try:
            requested_dt = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S")
            latest_dt = datetime.strptime(latest_event["timestamp"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            requested_dt = None
            latest_dt = None
        if requested_dt is not None and latest_dt is not None and requested_dt < latest_dt:
            timestamp = latest_event["timestamp"]
    order = "ASC" if event_type == "checkin" else "DESC"
    existing = None
    if not (event_type == "checkout" and latest_event and latest_event["event_type"] == "checkin"):
        existing = conn.execute(
            f"""
            SELECT id, timestamp, COALESCE(snapshot_path, '') AS snapshot_path
            FROM attendance
            WHERE lower(name) = lower(?)
              AND role = 'teachers'
              AND event_type = ?
              AND timestamp LIKE ?
            ORDER BY timestamp {order}, id {order}
            LIMIT 1
            """,
            (teacher["name"], event_type, f"{day_text}%"),
        ).fetchone()
    old_value = existing["timestamp"][11:16] if existing else ""
    new_value = timestamp[11:16]
    if old_value == new_value:
        return False
    if existing:
        conn.execute("UPDATE attendance SET timestamp = ? WHERE id = ?", (timestamp, existing["id"]))
        attendance_id = existing["id"]
        action = f"edit_teacher_{event_type}"
    else:
        conn.execute(
            """
            INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path)
            VALUES (?, ?, 'teachers', ?, ?, NULL)
            """,
            (teacher["id"], teacher["name"], event_type, timestamp),
        )
        attendance_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
        action = f"add_teacher_{event_type}"
    audit_request(
        handler,
        conn,
        actor["id"],
        action,
        "attendance",
        object_id=teacher["id"],
        details={
            "attendance_id": attendance_id,
            "person_name": teacher["name"],
            "role": "teachers",
            "event_type": event_type,
            "timestamp": timestamp,
            "field": "First in" if event_type == "checkin" else "Last out",
            "old_value": old_value,
            "new_value": new_value,
            "source": "manual_edit",
            "operator_name": user_display_name(actor),
            "changed_by": user_display_name(actor),
        },
    )
    return True


def schedule_hours_between(schedule_in, schedule_out):
    try:
        start = datetime.strptime(schedule_in, "%H:%M")
        end = datetime.strptime(schedule_out, "%H:%M")
    except ValueError:
        return 0.0
    if end < start:
        end += timedelta(days=1)
    return (end - start).total_seconds() / 3600


def upsert_teacher_schedule_times(conn, actor, handler, teacher, day_text, schedule_in_value, schedule_out_value):
    schedule_in_value = (schedule_in_value or "").strip()
    schedule_out_value = (schedule_out_value or "").strip()
    if not schedule_in_value and not schedule_out_value:
        return False
    project_id = effective_project_id(conn, actor)
    existing = teacher_schedule_for_day(conn, teacher["name"], day_text, project_id)
    schedule_in = parse_attendance_time_value(schedule_in_value)[:5] if schedule_in_value else existing["schedule_in"]
    schedule_out = parse_attendance_time_value(schedule_out_value)[:5] if schedule_out_value else existing["schedule_out"]
    if not schedule_in or not schedule_out:
        return False
    old_schedule_in = existing["schedule_in"]
    old_schedule_out = existing["schedule_out"]
    changes = []
    if old_schedule_in != schedule_in:
        changes.append(("SCHEDULE IN", old_schedule_in, schedule_in))
    if old_schedule_out != schedule_out:
        changes.append(("SCHEDULE OUT", old_schedule_out, schedule_out))
    if not changes:
        return False
    class_name = existing["class_name"]
    work_hours = schedule_hours_between(schedule_in, schedule_out)
    conn.execute(
        "DELETE FROM teacher_schedule WHERE lower(teacher_name) = lower(?) AND day_text = ? AND project_id = ?",
        (teacher["name"], day_text, project_id),
    )
    conn.execute(
        """
        INSERT INTO teacher_schedule(
            project_id, teacher_name, day_text, schedule_in, schedule_out, work_hours,
            class_name, source_filename, uploaded_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (project_id, teacher["name"], day_text, schedule_in, schedule_out, work_hours, class_name, "manual_edit", now_text()),
    )
    schedule_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    for field_name, old_value, new_value in changes:
        audit_request(
            handler,
            conn,
            actor["id"],
            "edit_teacher_schedule_time",
            "teacher_schedule",
            object_id=teacher["id"],
            details={
                "schedule_id": schedule_id,
                "person_name": teacher["name"],
                "date": day_text,
                "field": field_name,
                "old_value": old_value,
                "new_value": new_value,
                "schedule_in": schedule_in,
                "schedule_out": schedule_out,
                "work_hours": f"{work_hours:.2f}",
                "operator_name": user_display_name(actor),
                "changed_by": user_display_name(actor),
            },
        )
    return True


def update_teacher_status_times(conn, actor, handler, form):
    if actor["role"] not in {"principal", "boss"}:
        raise PermissionError("Not allowed")
    day_text = form.get("date", [today_text()])[0]
    try:
        day_text = datetime.strptime(day_text, "%Y-%m-%d").strftime("%Y-%m-%d")
    except ValueError as exc:
        raise ValueError("Invalid date") from exc
    target_teacher_id = form.get("save_teacher_id", [""])[0].strip()
    project_id = effective_project_id(conn, actor)
    teachers = conn.execute(
        """
        SELECT id, name
        FROM persons
        WHERE role = 'teachers'
          AND project_id = ?
          AND id NOT IN (SELECT person_id FROM deleted_user_archives WHERE person_id IS NOT NULL AND project_id = ?)
        ORDER BY name COLLATE NOCASE
        """,
        (project_id, project_id),
    ).fetchall()
    changed = 0

    def submitted_time(field_name):
        hour = form.get(f"{field_name}_hour", [""])[0].strip()
        minute = form.get(f"{field_name}_minute", [""])[0].strip()
        if hour or minute:
            if not hour or not minute:
                raise ValueError("Please select both hour and minute")
            return f"{hour}:{minute}"
        return form.get(field_name, [""])[0]

    for teacher in teachers:
        teacher_id = str(teacher["id"])
        if target_teacher_id and teacher_id != target_teacher_id:
            continue
        if upsert_teacher_attendance_time(conn, actor, handler, teacher, day_text, "checkin", submitted_time(f"first_in_{teacher_id}")):
            changed += 1
        if upsert_teacher_attendance_time(conn, actor, handler, teacher, day_text, "checkout", submitted_time(f"last_out_{teacher_id}")):
            changed += 1
        if upsert_teacher_schedule_times(
            conn,
            actor,
            handler,
            teacher,
            day_text,
            submitted_time(f"schedule_in_{teacher_id}"),
            submitted_time(f"schedule_out_{teacher_id}"),
        ):
            changed += 1
    return day_text, changed


def render_teacher_attendance(user, query):
    if user["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view teacher attendance.</div>')
    if user["role"] not in {"principal", "boss"}:
        return render_staff_teacher_attendance(user, query)
    selected_date = query.get("date", [today_text()])[0]
    try:
        selected_date = datetime.strptime(selected_date, "%Y-%m-%d").strftime("%Y-%m-%d")
    except ValueError:
        selected_date = today_text()
    action_mode = query.get("action", [""])[0]
    if user["role"] == "boss" and action_mode not in {"pay_hours"}:
        action_mode = "pay_hours"
    if user["role"] != "boss":
        action_mode = ""
    principal_self_panel = ""
    principal_self_script = ""

    with connect_db() as conn:
        saved_start, saved_end = get_teacher_attendance_range(conn, user["id"], selected_date, selected_date)
        pay_start = query.get("pay_start", [saved_start])[0]
        pay_end = query.get("pay_end", [saved_end])[0]
        project_id = effective_project_id(conn, user)
        summary = teacher_attendance_day_summary(conn, selected_date, project_id)
        version = teacher_attendance_version(conn, selected_date)
        if user["role"] == "principal":
            if user["person_id"]:
                principal_person = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                    (user["person_id"], project_id),
                ).fetchone()
                if principal_person:
                    self_start, self_end, self_rows = staff_in_out_rows(conn, int(user["person_id"]), pay_start, pay_end)
                    pay_start, pay_end = self_start, self_end
                    principal_self_panel = staff_in_out_panel_html(
                        principal_person,
                        self_start,
                        self_end,
                        self_rows,
                        heading="Mes heures IN / OUT",
                    )
                    principal_self_script = staff_in_out_range_script()
                else:
                    principal_self_panel = '<div class="panel"><div class="alert warn">Ce compte n\'est pas lié à une fiche employé.</div></div>'
            else:
                principal_self_panel = '<div class="panel"><div class="alert warn">Ce compte n\'est pas lié à une fiche employé.</div></div>'
        recent_rows = conn.execute(
            """
            SELECT attendance.id, attendance.person_id, attendance.name, attendance.event_type, attendance.timestamp,
                   COALESCE(attendance.snapshot_path, '') AS snapshot_path,
                   COALESCE((
                       SELECT
                         CASE
                           WHEN audit_log.details_json LIKE '%"source": "desktop"%'
                           THEN attendance.name
                           ELSE COALESCE(NULLIF(web_users.display_name, ''), NULLIF(web_users.username, ''), 'System')
                         END
                       FROM audit_log
                       LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                       WHERE audit_log.object_type = 'attendance'
                         AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                         AND (
                           audit_log.action LIKE '%' || attendance.event_type
                           OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                         )
                         AND (
                           audit_log.created_at <= attendance.timestamp
                           OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                         )
                       ORDER BY audit_log.created_at DESC, audit_log.id DESC
                       LIMIT 1
                     ), 'System') AS actor_name,
                   COALESCE((
                       SELECT audit_log.details_json
                       FROM audit_log
                       LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                       WHERE audit_log.object_type = 'attendance'
                         AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                         AND (
                           audit_log.action LIKE '%' || attendance.event_type
                           OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                         )
                         AND (
                           audit_log.created_at <= attendance.timestamp
                           OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                         )
                       ORDER BY audit_log.created_at DESC, audit_log.id DESC
                       LIMIT 1
                     ), '{}') AS audit_details_json
            FROM attendance
            JOIN persons ON persons.id = attendance.person_id
            WHERE attendance.role = 'teachers' AND attendance.timestamp LIKE ?
              AND persons.project_id = ?
            ORDER BY attendance.timestamp DESC, attendance.id DESC
            LIMIT 40
            """,
            (f"{selected_date}%", project_id),
        ).fetchall()
        teacher_audit_rows = conn.execute(
            """
            SELECT audit_log.*, COALESCE(web_users.display_name, web_users.username, 'System') AS actor_name
            FROM audit_log
            LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
            WHERE audit_log.created_at LIKE ?
              AND (
                audit_log.action IN ('edit_teacher_checkin', 'edit_teacher_checkout', 'add_teacher_checkin', 'add_teacher_checkout', 'edit_teacher_schedule_time')
                OR audit_log.details_json LIKE '%"role": "teachers"%'
              )
            ORDER BY audit_log.created_at DESC, audit_log.id DESC
            LIMIT 80
            """,
            (f"{selected_date}%",),
        ).fetchall()
        pay_start, pay_end, pay_days, pay_rows = teacher_pay_hours_summary(conn, pay_start, pay_end, project_id) if action_mode == "pay_hours" else (pay_start, pay_end, [], [])
        if action_mode == "pay_hours" or user["role"] == "principal":
            set_teacher_attendance_range(conn, user["id"], pay_start, pay_end)
        trend_weeks = teacher_six_week_hours_summary(conn, selected_date, project_id)

    show_teacher_work_data = user["role"] == "boss"
    show_teacher_schedule_out = user["role"] in {"principal", "boss"}
    teacher_rows = []
    for teacher in summary["teachers"]:
        status_class = "present" if teacher["status"] == "P" else "absent"
        latest_snapshot = teacher.get("latest_snapshot_path") or ""
        teacher_photo_html = '<span class="teacher-status-photo empty"></span>'
        if latest_snapshot:
            media_url = f"/media/{file_path_token(latest_snapshot)}"
            teacher_photo_html = f'<a class="teacher-status-photo" href="{html.escape(media_url)}" target="_blank"><img src="{html.escape(media_url)}" alt=""></a>'
        first_in_value = teacher["first_checkin"][11:16] if teacher["first_checkin"] else ""
        last_out_value = teacher["last_checkout"][11:16] if teacher["last_checkout"] else ""
        first_in_name = f"first_in_{teacher['id']}"
        last_out_name = f"last_out_{teacher['id']}"
        first_in_picker = time_picker_html(first_in_name, first_in_value)
        last_out_picker = time_picker_html(last_out_name, last_out_value)
        schedule_in_picker = time_picker_html(f"schedule_in_{teacher['id']}", teacher["schedule_in"])
        schedule_out_cell = f"<td>{time_picker_html(f'schedule_out_{teacher['id']}', teacher['schedule_out'])}</td>" if show_teacher_schedule_out else ""
        work_hours_cell = f'<td class="work-hours-cell">{html.escape(teacher["work_hours"])}</td>' if show_teacher_work_data else ""
        delete_day_button = ""
        if user["role"] == "boss":
            delete_day_button = (
                f'<button class="btn red teacher-row-delete" type="submit" '
                f'formaction="/teacher-attendance/delete-day" formmethod="post" '
                f'name="delete_teacher_id" value="{teacher["id"]}" '
                f'onclick="return confirm(\'Delete all attendance records for {html.escape(teacher["name"], quote=True)} on {html.escape(selected_date, quote=True)} ?\')">'
                f'Delete day</button>'
            )
        teacher_rows.append(
            f"""
            <tr data-teacher-name="{html.escape(teacher['name'])}" data-original-work-hours="{html.escape(teacher['work_hours'] or '0')}">
              <td><div class="teacher-name-cell">{teacher_photo_html}<strong>{html.escape(teacher['name'])}</strong></div></td>
              <td><span class="badge {status_class}">{status_label(teacher['status'])}</span></td>
              <td>{first_in_picker}</td>
              <td>{last_out_picker}</td>
              <td>{schedule_in_picker}</td>
              {schedule_out_cell}
              {work_hours_cell}
              <td><div class="teacher-row-actions"><button class="btn primary teacher-row-save" type="submit" name="save_teacher_id" value="{teacher['id']}">Save</button>{delete_day_button}</div></td>
            </tr>
            """
        )

    recent_items = []
    for row in recent_rows:
        try:
            audit_details = json.loads(row["audit_details_json"] or "{}")
        except json.JSONDecodeError:
            audit_details = {}
        snapshot_path = row["snapshot_path"] or ""
        snapshot_html = ""
        if snapshot_path:
            media_url = f"/media/{file_path_token(snapshot_path)}"
            snapshot_html = f'<a href="{html.escape(media_url)}" target="_blank"><img src="{html.escape(media_url)}" alt="" style="width:54px;height:54px;object-fit:cover;border-radius:6px;border:1px solid var(--line)"></a>'
        source_value = audit_details.get("source") or ("mobile_face" if snapshot_path else "")
        source_label = attendance_source_label(source_value) if source_value else "-"
        device_name = audit_details.get("mobile_device_name") or audit_details.get("device_name") or "-"
        recent_items.append(
            {
                "time": row["timestamp"],
                "teacher": row["name"],
                "event": EVENT_LABELS.get(row["event_type"], row["event_type"]),
                "by": row["actor_name"] or "System",
                "field": "",
                "old": "",
                "new": "",
                "source": source_label,
                "device": device_name,
                "photo": snapshot_html or "-",
            }
        )
    for row in teacher_audit_rows:
        try:
            details = json.loads(row["details_json"] or "{}")
        except json.JSONDecodeError:
            details = {}
        field_name = details.get("field") or row["action"]
        old_value = details.get("old_value") or ""
        new_value = details.get("new_value") or details.get("timestamp") or ""
        if row["action"].startswith("add_teacher_") and not old_value:
            old_value = "-"
        recent_items.append(
            {
                "time": row["created_at"],
                "teacher": details.get("person_name") or "",
                "event": "Modification" if row["action"].startswith("edit_") else "Ajout",
                "by": row["actor_name"] or details.get("operator_name") or "System",
                "field": field_name,
                "old": old_value,
                "new": new_value,
                "source": attendance_source_label(details.get("source") or "manual_edit"),
                "device": details.get("device_name") or details.get("mobile_device_name") or "-",
                "photo": "-",
            }
        )
    recent_items = sorted(recent_items, key=lambda item: item["time"], reverse=True)[:80]
    recent_html = "".join(
        f"<tr>"
        f"<td>{html.escape(item['time'])}</td>"
        f"<td>{html.escape(item['teacher'])}</td>"
        f"<td>{html.escape(item['event'])}</td>"
        f"<td>{html.escape(item['by'])}</td>"
        f"<td>{html.escape(item['field'])}</td>"
        f"<td>{html.escape(item['old'])}</td>"
        f"<td>{html.escape(item['new'])}</td>"
        f"<td>{html.escape(item['source'])}</td>"
        f"<td>{html.escape(item['device'])}</td>"
        f"<td>{item['photo']}</td>"
        f"</tr>"
        for item in recent_items
    )
    pay_day_headers = "".join(f"<th>{html.escape(day[5:])}</th>" for day in pay_days)
    pay_actual_total = sum(float(row["hours"] or 0) for row in pay_rows)
    pay_schedule_total = sum(float(row["schedule_hours"] or 0) for row in pay_rows)
    pay_rows_html = "".join(
        f"<tr data-pay-teacher-name=\"{html.escape(row['name'])}\" data-pay-hours=\"{row['hours']:.2f}\">"
        f"<td><strong>{html.escape(row['name'])}</strong></td>"
        f"<td class=\"pay-hours-cell\">{row['hours']:.2f}</td>"
        f"<td>{row['schedule_hours']:.2f}</td>"
        + "".join(f"<td class=\"pay-day-cell\" data-pay-day=\"{html.escape(day)}\">{html.escape(str(row['daily_hours'].get(day, '')))}</td>" for day in pay_days)
        + f"<td>{row['pairs']}</td><td>{row['events']}</td><td>{'Open' if row['open_record'] else ''}</td></tr>"
        for row in pay_rows
    )
    pay_hours_html = ""
    if action_mode == "pay_hours":
        pay_hours_html = f"""
        <form method="get" action="/teacher-attendance" class="pay-hours-form">
          <input type="hidden" name="action" value="pay_hours">
          <input type="hidden" name="date" value="{html.escape(selected_date)}">
          <div>
            <label>Start</label>
            <input type="date" name="pay_start" value="{html.escape(pay_start)}">
          </div>
          <div>
            <label>End</label>
            <input type="date" name="pay_end" value="{html.escape(pay_end)}">
          </div>
        </form>
        <div class="stats" style="margin-top:10px;grid-template-columns:repeat(auto-fit,minmax(190px,220px))">
          <div class="stat"><div class="muted">WORK HOURS TOTAL</div><div class="value">{pay_actual_total:.2f}</div></div>
          <div class="stat"><div class="muted">SCHEDULE HOURS TOTAL</div><div class="value">{pay_schedule_total:.2f}</div></div>
        </div>
        <div class="table-wrap pay-hours-table teacher-ten-row-table" data-default-table-rows="10">
          <table>
            <thead><tr><th>Teacher</th><th>WORK HOURS TOTAL</th><th>SCHEDULE HOURS TOTAL</th>{pay_day_headers}<th>Days</th><th>Events</th><th>Open</th></tr></thead>
            <tbody>{pay_rows_html or f'<tr><td colspan="{6 + len(pay_days)}" class="muted">No teachers found.</td></tr>'}</tbody>
          </table>
        </div>
        """
    load_schedule_html = ""
    if False and action_mode == "load_schedule":
        load_schedule_html = f"""
        <form method="post" action="/teacher-attendance/load-schedule" enctype="multipart/form-data" class="pay-hours-form">
          <input type="hidden" name="date" value="{html.escape(selected_date)}">
          <input type="hidden" name="action" value="load_schedule">
          <div>
            <label>Schedule file</label>
            <input type="file" name="schedule_file" accept="{schedule_file_accept_types()}" required>
          </div>
          <button class="btn primary" type="submit">LOAD SCHEDULE</button>
        </form>
        """
    teacher_action_buttons_html = ""
    if user["role"] == "boss":
        teacher_action_buttons_html = f"""
          {load_schedule_html}
          {pay_hours_html}
        """
    teacher_trend_chart = teacher_hours_trend_chart_html(trend_weeks) if show_teacher_work_data else ""
    teacher_schedule_out_header = "<th>SCHEDULE OUT</th>" if show_teacher_schedule_out else ""
    teacher_work_headers = "<th>WORK HOURS</th>" if show_teacher_work_data else ""
    teacher_status_colspan = 8 if show_teacher_work_data else (7 if show_teacher_schedule_out else 6)
    teacher_status_date_button = ""
    teacher_status_row_limit_attr = ' data-default-table-rows="10"' if user["role"] == "boss" else ""
    recent_records_html = ""
    if user["role"] == "boss":
        recent_records_html = f"""
    <div class="panel" style="margin-top:16px">
      <h3>Recent teacher records</h3>
      <div class="table-wrap teacher-ten-row-table" data-default-table-rows="10">
        <table>
          <thead><tr><th>Timestamp</th><th>Teacher</th><th>Event</th><th>By</th><th>Field</th><th>Old</th><th>New</th><th>Source</th><th>Device</th><th>Photo</th></tr></thead>
          <tbody>{recent_html or '<tr><td colspan="10" class="muted">No teacher attendance records for this date.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
        """
    body = f"""
    <style>
      .teacher-attendance-head {{ display:flex; align-items:start; justify-content:space-between; gap:12px; flex-wrap:wrap; }}
      .teacher-attendance-date {{ display:grid; grid-template-columns:180px auto; gap:8px; align-items:end; }}
      .teacher-attendance-side {{ display:grid; gap:10px; flex:0 1 400px; min-width:min(100%, 360px); }}
      .teacher-hours-chart {{ border:1px solid var(--line); border-radius:8px; background:#fbfdff; padding:8px 12px 4px; width:100%; max-width:none; margin-top:-12px; }}
      .teacher-hours-chart .arrival-chart {{ height:145px; }}
      .teacher-actual-line {{ stroke:var(--blue); }}
      .teacher-schedule-line {{ stroke:var(--green); }}
      .teacher-chart-legend {{ display:flex; align-items:center; gap:6px; font-size:11px; font-weight:700; color:var(--muted); }}
      .teacher-chart-legend span {{ width:16px; height:3px; border-radius:999px; display:inline-block; }}
      .teacher-chart-legend .actual {{ background:var(--blue); }}
      .teacher-chart-legend .schedule {{ background:var(--green); }}
      .teacher-action-panel {{ display:grid; gap:12px; flex:1 1 780px; min-width:min(100%, 520px); }}
      .teacher-action-buttons {{ display:flex; gap:12px; flex-wrap:wrap; align-items:center; }}
      .teacher-action-buttons .btn {{ min-width:160px; justify-content:center; }}
      .pay-hours-form {{ display:flex; gap:10px; flex-wrap:wrap; align-items:end; }}
      .pay-hours-form input[type="date"] {{ min-width:160px; }}
      .pay-hours-table {{ margin-top:10px; width:100%; max-width:none; max-height:704px; overflow:auto; }}
      .pay-hours-table tbody tr {{ height:44px; }}
      .pay-hours-table table {{ width:100%; min-width:max-content; }}
      .teacher-status-head {{ display:flex; align-items:end; justify-content:space-between; gap:12px; flex-wrap:wrap; margin-bottom:10px; }}
      .teacher-status-head h3 {{ margin:0; }}
      .teacher-status-panel h3 {{ font-size:20px; }}
      .teacher-status-table table {{ font-size:16px; }}
      .teacher-status-table th, .teacher-status-table td {{ padding-top:11px; padding-bottom:11px; }}
      .teacher-status-table .badge {{ font-size:15px; padding:6px 12px; }}
      .teacher-name-cell {{ display:flex; align-items:center; gap:8px; min-width:150px; }}
      .teacher-status-photo {{ width:34px; height:34px; border-radius:6px; border:1px solid var(--line); background:#eef2f6; overflow:hidden; flex:0 0 auto; display:inline-flex; align-items:center; justify-content:center; }}
      .teacher-status-photo img {{ width:100%; height:100%; object-fit:cover; display:block; }}
      .teacher-status-photo.empty::after {{ content:""; width:14px; height:14px; border-radius:50%; background:#c8d3df; display:block; opacity:.55; }}
      .teacher-time-input {{ width:118px; max-width:100%; }}
      .time-picker {{ display:flex; align-items:center; gap:4px; min-width:124px; }}
      .time-picker select {{ min-height:38px; width:118px; padding:6px 6px; font-size:14px; }}
      .split-time-picker {{ min-width:132px; }}
      .split-time-picker select {{ width:56px; }}
      .time-picker-separator {{ font-weight:800; color:#52616e; }}
      .teacher-status-actions {{ display:flex; justify-content:flex-end; margin-top:12px; }}
      .teacher-row-actions {{ display:flex; gap:6px; flex-wrap:wrap; align-items:center; }}
      .teacher-row-actions .btn {{ padding:6px 9px; min-height:34px; }}
      .teacher-ten-row-table {{ overflow:auto; scrollbar-gutter:stable; }}
      .teacher-ten-row-table thead th {{ position:sticky; top:0; z-index:2; background:#eef4f7; box-shadow:0 1px 0 var(--line); }}
      @media (max-width:720px) {{
        .teacher-attendance-head, .teacher-attendance-side {{ display:grid; grid-template-columns:1fr; }}
        .teacher-status-head {{ display:flex; align-items:end; justify-content:space-between; flex-wrap:nowrap; gap:8px; }}
        .teacher-status-head h3 {{ flex:0 0 auto; font-size:17px; white-space:nowrap; }}
        .teacher-status-head .teacher-attendance-date {{ display:flex; align-items:end; justify-content:flex-end; gap:6px; min-width:0; }}
        .teacher-status-head .teacher-attendance-date > div {{ width:min(145px, 42vw); }}
        .teacher-status-head .teacher-attendance-date input[type="date"] {{ width:100%; min-width:0; padding-left:7px; padding-right:4px; }}
        .teacher-status-head .teacher-attendance-date .btn {{ display:none; }}
        .teacher-action-buttons .btn, .pay-hours-form input[type="date"] {{ width:100%; }}
        .teacher-status-table table {{ font-size:15px; }}
        .teacher-status-table .badge {{ font-size:14px; }}
        .pay-hours-table {{ max-height:none; }}
        .teacher-time-input {{ width:100%; min-width:96px; }}
      }}
    </style>
    {principal_self_panel}
    <div class="panel">
      <div class="teacher-attendance-head">
        <div class="teacher-action-panel">
          {teacher_action_buttons_html}
        </div>
        <div class="teacher-attendance-side">
          {teacher_trend_chart}
        </div>
      </div>
    </div>
    <div class="panel teacher-status-panel" style="margin-top:8px">
      <div class="teacher-status-head">
        <form method="get" action="/teacher-attendance" class="teacher-attendance-date">
          <input type="hidden" name="action" value="{html.escape(action_mode)}">
          <input type="hidden" name="pay_start" value="{html.escape(pay_start)}">
          <input type="hidden" name="pay_end" value="{html.escape(pay_end)}">
          <div>
            <label>Date</label>
            <input type="date" name="date" value="{html.escape(selected_date)}">
          </div>
          {teacher_status_date_button}
        </form>
      </div>
      <form method="post" action="/teacher-attendance/update-times" class="teacher-status-form">
        <input type="hidden" name="date" value="{html.escape(selected_date)}">
        <input type="hidden" name="action" value="{html.escape(action_mode)}">
        <input type="hidden" name="pay_start" value="{html.escape(pay_start)}">
        <input type="hidden" name="pay_end" value="{html.escape(pay_end)}">
      <div class="table-wrap teacher-status-table teacher-ten-row-table"{teacher_status_row_limit_attr}>
        <table>
          <thead><tr><th>Teacher</th><th>Status</th><th>First in</th><th>Last out</th><th>SCHEDULE IN</th>{teacher_schedule_out_header}{teacher_work_headers}<th>Action</th></tr></thead>
          <tbody>{''.join(teacher_rows) or f'<tr><td colspan="{teacher_status_colspan}" class="muted">No teachers found.</td></tr>'}</tbody>
        </table>
      </div>
      </form>
    </div>
    {recent_records_html}
    {principal_self_script}
    <script>
      (function() {{
        document.querySelectorAll('[data-default-table-rows]').forEach(function(wrapper) {{
          const limit = Number(wrapper.getAttribute('data-default-table-rows')) || 10;
          const table = wrapper.querySelector('table');
          const rows = table ? Array.from(table.querySelectorAll('tbody > tr')) : [];
          if (!table || rows.length <= limit) return;
          const head = table.querySelector('thead');
          let visibleHeight = head ? head.getBoundingClientRect().height : 0;
          rows.slice(0, limit).forEach(function(row) {{ visibleHeight += row.getBoundingClientRect().height; }});
          wrapper.style.maxHeight = Math.ceil(visibleHeight + 2) + 'px';
          wrapper.style.overflow = 'auto';
        }});
        let version = {version};
        const selectedDate = "{html.escape(selected_date)}";
        function pollTeacherAttendance() {{
          fetch('/api/teacher-attendance-version?date=' + encodeURIComponent(selectedDate), {{
            credentials: 'same-origin'
          }})
          .then(r => r.ok ? r.json() : null)
          .then(data => {{
            if (!data) return;
            if (typeof data.version === 'number' && data.version !== version) {{
              window.location.reload();
            }}
          }})
          .catch(() => {{}});
        }}
        document.querySelectorAll('.teacher-attendance-date input[type="date"], .pay-hours-form input[type="date"]').forEach(input => {{
          input.addEventListener('change', () => {{
            const form = input.closest('form');
            if (form) form.requestSubmit();
          }});
        }});
        document.querySelectorAll('.split-time-picker').forEach(picker => {{
          const hidden = picker.querySelector('.time-picker-value');
          const hour = picker.querySelector('.time-picker-hour');
          const minute = picker.querySelector('.time-picker-minute');
          function syncTimePicker() {{
            if (!hidden || !hour || !minute) return;
            if (hour.value === '19' && minute.value && minute.value !== '00') minute.value = '00';
            hidden.value = hour.value && minute.value ? hour.value + ':' + minute.value : '';
            hidden.dispatchEvent(new Event('input', {{ bubbles: true }}));
            hidden.dispatchEvent(new Event('change', {{ bubbles: true }}));
          }}
          if (hour) hour.addEventListener('change', syncTimePicker);
          if (minute) minute.addEventListener('change', syncTimePicker);
        }});
        function timeMinutes(value) {{
          const match = /^([01][0-9]|2[0-3]):([0-5][0-9])$/.exec((value || '').trim());
          if (!match) return null;
          return Number(match[1]) * 60 + Number(match[2]);
        }}
        function updateRowWorkHours(row) {{
          const firstIn = timeMinutes(row.querySelector('input[name^="first_in_"]')?.value);
          let lastOut = timeMinutes(row.querySelector('input[name^="last_out_"]')?.value);
          const scheduleIn = timeMinutes(row.querySelector('input[name^="schedule_in_"]')?.value);
          const scheduleOut = timeMinutes(row.querySelector('input[name^="schedule_out_"]')?.value);
          const target = row.querySelector('.work-hours-cell');
          if (!target) return;
          if (lastOut === null) lastOut = scheduleOut;
          if (firstIn === null || lastOut === null || scheduleIn === null) {{
            target.textContent = '';
            updatePayHoursRow(row, null);
            return;
          }}
          const paidStart = Math.max(firstIn, scheduleIn);
          const minutes = Math.max(0, lastOut - paidStart);
          const hours = (minutes / 60).toFixed(2);
          target.textContent = hours;
          updatePayHoursRow(row, Number(hours));
        }}
        function updatePayHoursRow(statusRow, currentHours) {{
          const payStart = "{html.escape(pay_start)}";
          const payEnd = "{html.escape(pay_end)}";
          if (!payStart || !payEnd || selectedDate < payStart || selectedDate > payEnd || currentHours === null) return;
          const teacherName = statusRow.dataset.teacherName || '';
          const payRow = Array.from(document.querySelectorAll('tr[data-pay-teacher-name]')).find(row => row.dataset.payTeacherName === teacherName);
          if (!payRow) return;
          const originalWorkHours = Number(statusRow.dataset.originalWorkHours || '0');
          const originalPayHours = Number(payRow.dataset.payHours || '0');
          const nextPayHours = Math.max(0, originalPayHours - originalWorkHours + currentHours);
          const target = payRow.querySelector('.pay-hours-cell');
          if (target) target.textContent = nextPayHours.toFixed(2);
          const dayTarget = payRow.querySelector('.pay-day-cell[data-pay-day="' + selectedDate + '"]');
          if (dayTarget) dayTarget.textContent = currentHours.toFixed(2);
        }}
        let dirtyTeacherRow = null;
        document.querySelectorAll('.teacher-status-table tbody tr').forEach(row => {{
          row.querySelectorAll('.teacher-time-input').forEach(input => {{
            const markDirty = () => {{
              dirtyTeacherRow = row;
              row.classList.add('teacher-row-dirty');
              updateRowWorkHours(row);
            }};
            input.addEventListener('input', markDirty);
            input.addEventListener('change', markDirty);
          }});
        }});
        const teacherStatusForm = document.querySelector('.teacher-status-form');
        if (teacherStatusForm) {{
          const scrollStorageKey = 'teacher-attendance-scroll';
          const savedScroll = window.sessionStorage.getItem(scrollStorageKey);
          if (savedScroll !== null) {{
            window.sessionStorage.removeItem(scrollStorageKey);
            window.requestAnimationFrame(() => window.scrollTo(0, Number(savedScroll) || 0));
          }}
          teacherStatusForm.addEventListener('submit', () => {{
            window.sessionStorage.setItem(scrollStorageKey, String(window.scrollY));
            dirtyTeacherRow = null;
          }});
          function confirmTeacherRowSwitch(target) {{
            const targetRow = target.closest('tr[data-teacher-name]');
            if (!dirtyTeacherRow || !targetRow || targetRow === dirtyTeacherRow) return true;
            const teacherName = dirtyTeacherRow.dataset.teacherName || 'cette personne';
            const shouldSave = window.confirm('Les modifications de ' + teacherName + ' ne sont pas enregistrees. Voulez-vous les enregistrer avant de modifier une autre personne ?');
            if (!shouldSave) {{
              dirtyTeacherRow.scrollIntoView({{ behavior: 'smooth', block: 'center' }});
              return false;
            }}
            const saveButton = dirtyTeacherRow.querySelector('.teacher-row-save');
            if (saveButton) teacherStatusForm.requestSubmit(saveButton);
            return false;
          }}
          teacherStatusForm.addEventListener('pointerdown', event => {{
            const target = event.target;
            if (!(target instanceof Element)) return;
            const targetRow = target.closest('tr[data-teacher-name]');
            if (!dirtyTeacherRow || !targetRow || targetRow === dirtyTeacherRow) return;
            event.preventDefault();
            if (confirmTeacherRowSwitch(target) && target instanceof HTMLElement) target.focus({{ preventScroll: true }});
          }});
          window.addEventListener('beforeunload', event => {{
            if (!dirtyTeacherRow) return;
            event.preventDefault();
            event.returnValue = '';
          }});
        }}
        setInterval(pollTeacherAttendance, 5000);
      }})();
    </script>
    """
    return html_page("Teacher Attendance", user, body)


def build_attendance_export_xlsx(user, selected_class, selected_date):
    try:
        selected_date = datetime.strptime(selected_date, "%Y-%m-%d").strftime("%Y-%m-%d")
    except ValueError:
        selected_date = today_text()
    with connect_db() as conn:
        rows = attendance_export_source_rows(conn, selected_date)
    export_rows = [
        [name, ROLE_LABELS.get(role, role), class_name, timestamp, EVENT_LABELS.get(event_type, event_type), operator_name or attendance_source_label(source), snapshot_path]
        for _person_id, name, role, class_name, timestamp, event_type, snapshot_path, source, operator_name, *_extra in rows
    ]
    summary_rows = build_presence_summary_rows(rows)
    workbook = [
        {
            "name": "Attendance Records",
            "headers": ["Name", "Role", "Class", "Time", "Type", "By", "Snapshot Photo"],
            "rows": export_rows,
        },
        {
            "name": "Résumé des présences",
            "headers": ["Date", "Time", "Children Present", "Class Counts"],
            "rows": summary_rows,
        },
    ]
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    export_path = DAILY_EXPORT_DIR / f"attendance_records_{stamp}.xlsx"
    write_xlsx_workbook(export_path, workbook)
    return export_path.read_bytes()


def render_closed_dates(user, query):
    if user["role"] not in MANAGE_CLOSED_DATES_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage closed dates.</div>')
    closed = load_closed_dates()
    rows = "".join(f"<tr><td class='closed-date-cell'>{html.escape(d)}</td><td class='closed-action-cell'><form method='post' action='/closed-dates/remove' onsubmit=\"return confirm('Remove this date?')\"><input type='hidden' name='date' value='{html.escape(d)}'><button class='btn red closed-action-btn' type='submit'>Supprimer</button></form></td></tr>" for d in closed)
    body = f"""
    <style>
      .closed-dates-table {{ width:auto; min-width:0; table-layout:fixed; }}
      .closed-dates-table th, .closed-dates-table td {{ padding:6px 8px; white-space:nowrap; }}
      .closed-date-cell {{ width:118px; }}
      .closed-action-cell {{ width:92px; padding-left:2px !important; }}
      .closed-action-cell form {{ margin:0; }}
      .closed-action-btn {{ min-height:30px; padding:4px 7px; width:auto; font-size:12px; line-height:1; }}
    </style>
    <div class="panel">
      <h2>Manage Closed Dates</h2>
      <form method="post" action="/closed-dates/add" class="toolbar">
        <div>
          <label>Date</label>
          <input type="date" name="date" required>
        </div>
        <div>
          <label>Reason</label>
          <input name="reason" placeholder="Holiday, power outage, etc.">
        </div>
        <div>
          <button class="btn amber" type="submit">Ajouter une date F</button>
        </div>
      </form>
    </div>
    <div class="panel" style="margin-top:16px">
      <h3>Current Closed Dates</h3>
      <div class="table-wrap">
        <table class="closed-dates-table">
          <thead><tr><th>Date</th><th>Action</th></tr></thead>
          <tbody>{rows or '<tr><td colspan=\"2\" class=\"muted\">No closed dates</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Closed Dates", user, body)


def render_users(user, query, account_only=False):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage users.</div>')
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        users = conn.execute(
            """
            SELECT web_users.*, persons.class_name AS linked_class_name
            FROM web_users
            LEFT JOIN persons ON persons.id = web_users.person_id
            WHERE web_users.is_active = 1
              AND web_users.project_id = ?
            """
            , (project_id,)
        ).fetchall()
        invite_people = conn.execute(
            """
            SELECT id, name, role, class_name
            FROM persons
            WHERE role IN ('children', 'teachers')
              AND project_id = ?
              AND id NOT IN (SELECT person_id FROM web_users WHERE person_id IS NOT NULL AND is_active = 1 AND project_id = ?)
              AND id NOT IN (SELECT person_id FROM deleted_user_archives WHERE person_id IS NOT NULL AND project_id = ?)
            ORDER BY role, class_name, name
            """
            , (project_id, project_id, project_id)
        ).fetchall()
        recent_invitations = conn.execute(
            """
            SELECT mobile_invitations.*, persons.name AS person_name
            FROM mobile_invitations
            JOIN persons ON persons.id = mobile_invitations.person_id
            WHERE mobile_invitations.project_id = ?
            ORDER BY mobile_invitations.id DESC
            LIMIT 5
            """
            , (project_id,)
        ).fetchall()
        invited_person_ids = {
            int(row["person_id"])
            for row in conn.execute(
                "SELECT DISTINCT person_id FROM mobile_invitations WHERE person_id IS NOT NULL AND project_id = ?",
                (project_id,),
            ).fetchall()
        }
        device_rows = conn.execute(
            """
            SELECT *
            FROM mobile_devices
            WHERE is_active = 1
              AND user_id IN (SELECT id FROM web_users WHERE project_id = ?)
            ORDER BY last_seen_at DESC, id DESC
            """
            , (project_id,)
        ).fetchall()
        hidden_groups = {
            row["name"]
            for row in conn.execute("SELECT name FROM hidden_class_names WHERE project_id = ?", (project_id,)).fetchall()
        }
        classes = get_classes(conn, user)
        top_group_names = [row["class_name"] for row in conn.execute(
            """
            SELECT DISTINCT class_name
            FROM persons
            WHERE role = 'children' AND class_name <> '' AND project_id = ?
            ORDER BY class_name COLLATE NOCASE
            """
            , (project_id,)
        ).fetchall()]
        group_names = []
        for name in classes + top_group_names:
            if name and name not in hidden_groups and name not in group_names:
                group_names.append(name)
    devices_by_user = {}
    total_users = len(users)
    for device in device_rows:
        devices_by_user.setdefault(device["user_id"], device)
    sort_key = query.get("sort", [""])[0]
    flash = None
    if query.get("created", [""])[0] == "1":
        flash = ("info", "User created successfully.")
    if query.get("invited", [""])[0] == "1":
        flash = ("info", "Invitation created successfully.")
    if query.get("deleted", [""])[0] == "1":
        flash = ("info", "Selected users deleted successfully.")
    if query.get("group_deleted", [""])[0] == "1":
        flash = ("info", "Group name removed from the dropdown.")
    if query.get("person_deleted", [""])[0] == "1":
        flash = ("info", "Personne supprimée de la liste.")
    if query.get("imported", [""])[0] == "1":
        flash = (
            "info",
            "Load list terminé. Créés: {}. Mis à jour: {}. Ignorés: {}.".format(
                query.get("created", ["0"])[0],
                query.get("updated", ["0"])[0],
                query.get("skipped", ["0"])[0],
            ),
        )
    if query.get("avatars", [""])[0] == "1":
        flash = (
            "info",
            "Avatars importés: {}. Ignorés: {}.".format(
                query.get("updated", ["0"])[0],
                query.get("skipped", ["0"])[0],
            ),
        )
    account_flash_token = query.get("account_flash", [""])[0].strip()
    if account_flash_token:
        account_flash = FLASH_MESSAGES.pop(account_flash_token, None)
        if account_flash:
            flash = account_flash
    pending_html = ""
    pending_token = query.get("pending_import", [""])[0].strip()
    if pending_token:
        pending_preview = get_pending_child_list_import(pending_token, user["id"])
        if pending_preview is None:
            flash = ("warn", "The import preview expired. Please upload the file again.")
        else:
            preview_rows = "".join(
                f"<tr><td>{html.escape(name)}</td><td>{html.escape(group)}</td></tr>"
                for name, group in pending_preview["entries"]
            )
            pending_html = f"""
            <div class="panel" style="margin-bottom:16px">
              <h3>Confirm child list import</h3>
              <div class="alert warn">File: {html.escape(pending_preview['filename'] or '')}. Rows detected: {len(pending_preview['entries'])}.</div>
              <div class="table-wrap" style="max-height:260px; overflow:auto">
                <table>
                  <thead><tr><th>Name</th><th>Groupe</th></tr></thead>
                  <tbody>{preview_rows}</tbody>
                </table>
              </div>
              <div class="btn-row" style="margin-top:12px">
                <form method="post" action="/children/load-list/confirm">
                  <input type="hidden" name="token" value="{html.escape(pending_token, quote=True)}">
                  <input type="hidden" name="return_to" value="/users">
                  <button class="btn primary" type="submit">Confirm and save</button>
                </form>
                <a class="btn gray" href="/users">Cancel</a>
              </div>
            </div>
            """
    created_token = query.get("created_invite", [""])[0].strip()
    created_invite_url = display_invite_url(created_token) if created_token else ""
    class_options = "".join(f'<option value="{html.escape(cls)}">{html.escape(cls)}</option>' for cls in group_names)
    def user_class_text(target):
        if target["role"] == "children":
            linked_class = (target["linked_class_name"] or "").strip()
            if linked_class:
                return linked_class
        classes_value = safe_json_list(target["allowed_classes_json"])
        return ", ".join(classes_value) if classes_value else "-"
    def user_sort_value(target):
        device = devices_by_user.get(target["id"])
        if sort_key == "name":
            return ((target["display_name"] or "").lower(), (target["username"] or "").lower())
        if sort_key == "role":
            return (ROLE_LABELS.get(target["role"], target["role"]).lower(), (target["display_name"] or "").lower())
        if sort_key == "classes":
            return (user_class_text(target).lower(), (target["display_name"] or "").lower())
        if sort_key == "device":
            return (0 if device else 1, (device["last_seen_at"] if device else ""), (target["display_name"] or "").lower())
        if sort_key == "username":
            return ((target["username"] or "").lower(), (target["display_name"] or "").lower())
        return (target["role"], (target["username"] or "").lower())
    users = sorted(users, key=user_sort_value)
    selected_invite_person_id = query.get("invite_person_id", [""])[0]
    selected_invite_user_id = query.get("invite_user_id", [""])[0]
    table_rows = []
    invite_user_options = []
    for target in users:
        if user["role"] == "principal" and target["role"] == "boss":
            continue
        can_invite_user = (
            target["id"] != user["id"]
            and can_manage_users(user, target)
            and target["role"] in MOBILE_INVITATION_ROLES
        )
        if can_invite_user:
            selected_attr = " selected" if str(target["id"]) == selected_invite_user_id else ""
            invited_style = ' style="color:#9ca3af"' if target["person_id"] and int(target["person_id"]) in invited_person_ids else ""
            invite_user_options.append(
                f'<option value="user:{target["id"]}"{selected_attr}{invited_style}>{html.escape(target["display_name"])} ({html.escape(ROLE_LABELS.get(target["role"], target["role"]))})</option>'
            )
        class_text = user_class_text(target)
        device = devices_by_user.get(target["id"])
        device_text = "-"
        if device:
            device_name = html.escape(device["device_name"] or "Mobile device")
            device_text = f"{device_name}<br><span class=\"small muted\">Last: {html.escape(device['last_seen_at'])}</span>"
        delete_button = ""
        if target["id"] != user["id"] and can_manage_users(user, target):
            delete_button = f"""
                <form method="post" action="/users/delete" style="display:inline" onsubmit="return confirm('Delete user {html.escape(target['username'], quote=True)}?')">
                  <input type="hidden" name="id" value="{target['id']}">
                  <button class="btn red" type="submit">Supprimer</button>
                </form>
            """
        reset_device_button = ""
        if target["role"] in {"teacher", "children"} and can_manage_users(user, target):
            reset_device_button = f"""
                <form method="post" action="/users/reset-mobile-device" style="display:inline" onsubmit="return confirm('Reset mobile device for {html.escape(target['username'], quote=True)}?')">
                  <input type="hidden" name="id" value="{target['id']}">
                  <button class="btn amber" type="submit">Reset appareil</button>
                </form>
            """
        edit_button = f'<a class="btn" href="/users/edit?id={target["id"]}">Modifier</a>' if can_manage_users(user, target) or can_reset_user_password(user, target) else ""
        invite_button = f'<a class="btn green" href="/users?invite_user_id={target["id"]}#invite-user">Inviter</a>' if can_invite_user else ""
        action_options = ['<option value="">...</option>']
        if edit_button:
            action_options.append(f'<option value="edit" data-href="/users/edit?id={target["id"]}">Modifier</option>')
        if can_invite_user:
            action_options.append(f'<option value="invite" data-href="/users?invite_user_id={target["id"]}#invite-user">Inviter</option>')
        if reset_device_button:
            action_options.append(f'<option value="reset_device" data-id="{target["id"]}" data-confirm="Reset mobile device for {html.escape(target["username"], quote=True)}?">Reset appareil</option>')
        if delete_button:
            action_options.append(f'<option value="delete" data-id="{target["id"]}" data-confirm="Delete user {html.escape(target["username"], quote=True)}?">Supprimer</option>')
        action_menu = f"""
                <select class="action-select" aria-label="Actions" onchange="handleUserAction(this)">
                  {''.join(action_options)}
                </select>
        """
        table_rows.append(
            f"""
            <tr>
              <td style="text-align:center"><input class="user-select" type="checkbox" value="{target['id']}" data-user-checkbox></td>
              <td>{html.escape(target['username'])}</td>
              <td>{html.escape(target['display_name'])}</td>
              <td>{html.escape(ROLE_LABELS.get(target['role'], target['role']))}</td>
              <td class="classes-cell" title="{html.escape(class_text, quote=True)}">{html.escape(class_text)}</td>
              <td>{device_text}</td>
              <td>{html.escape(target['password_changed_at'])}</td>
              <td>
                {action_menu}
              </td>
            </tr>
            """
        )
    invite_person_options = []
    invite_person_options.extend(invite_user_options)
    for person in invite_people:
        role_label = "Enfant" if person["role"] == "children" else "Employé"
        class_text = f" - {person['class_name']}" if person["class_name"] else ""
        selected_attr = " selected" if str(person["id"]) == selected_invite_person_id else ""
        invited_style = ' style="color:#9ca3af"' if int(person["id"]) in invited_person_ids else ""
        invite_person_options.append(
            f'<option value="person:{person["id"]}"{selected_attr}{invited_style}>{html.escape(person["name"])} ({role_label}{html.escape(class_text)})</option>'
        )
    invite_rows = []
    for invite in recent_invitations:
        invite_link = display_invite_url(invite["token"])
        status = "Acceptée" if invite["accepted_at"] else ("Expirée" if invitation_is_expired(invite) else "En attente")
        invite_rows.append(
            f"""
            <tr>
              <td>{html.escape(invite['person_name'])}</td>
              <td>{html.escape(invite['email'])}</td>
              <td>{html.escape(invite['created_at'])}</td>
              <td>{html.escape(status)}</td>
              <td><a class="btn ghost" href="{html.escape(invite_link)}" target="_blank">{html.escape(invite_link)}</a></td>
            </tr>
            """
        )
    created_invite_panel = ""
    if created_token:
        created_invite_panel = f"""
        <style>
          .invite-guide-overlay {{ position:fixed; inset:0; z-index:3100; display:flex; align-items:center; justify-content:center; padding:20px; background:rgba(15,35,42,.50); backdrop-filter:blur(3px); }}
          .invite-guide-dialog {{ width:min(650px,100%); max-height:calc(100vh - 40px); overflow-y:auto; position:relative; padding:26px; border:1px solid #c8dfe5; border-radius:18px; background:#fff; box-shadow:0 28px 80px rgba(15,35,42,.30); }}
          .invite-guide-close {{ position:absolute; top:12px; right:12px; width:34px; height:34px; padding:0; border:0; border-radius:50%; background:#eef4f5; color:#36565c; font-size:22px; line-height:1; cursor:pointer; }}
          .invite-guide-language {{ position:absolute; top:13px; right:54px; display:inline-flex; gap:3px; padding:3px; border:1px solid #d7e0e3; border-radius:999px; background:#f4f7f8; }}
          .invite-guide-language button {{ min-width:34px; padding:5px 7px; border:0; border-radius:999px; background:transparent; color:#52666b; font-size:11px; font-weight:900; cursor:pointer; }}
          .invite-guide-language button[aria-pressed="true"] {{ background:#2f80c2; color:#fff; }}
          .invite-guide-kicker {{ margin:0 128px 5px 0; color:#2f80c2; font-size:12px; font-weight:900; letter-spacing:.1em; text-transform:uppercase; }}
          .invite-guide-dialog h2 {{ margin:0 42px 9px 0; color:#173b3f; font-size:25px; }}
          .invite-guide-text {{ margin:0; color:#52666b; line-height:1.55; }}
          .invite-guide-link {{ margin:16px 0; padding:13px; border:1px solid #b9d9ee; border-radius:12px; background:#eef7fd; overflow-wrap:anywhere; }}
          .invite-guide-link a {{ color:#1f6fa9; font-weight:750; }}
          .invite-guide-actions {{ display:flex; flex-wrap:wrap; gap:9px; margin-top:18px; }}
          .invite-guide-actions .btn {{ text-align:center; }}
          .invite-guide-status {{ min-height:20px; margin-top:9px; color:#17824b; font-size:13px; font-weight:750; }}
          @media (max-width:640px) {{ .invite-guide-overlay {{ padding:12px; align-items:flex-end; }} .invite-guide-dialog {{ max-height:calc(100vh - 24px); padding:22px 17px 18px; border-radius:18px 18px 12px 12px; }} .invite-guide-dialog h2 {{ font-size:21px; }} .invite-guide-actions {{ display:grid; grid-template-columns:1fr; }} .invite-guide-actions .btn {{ width:100%; }} }}
        </style>
        <div class="invite-guide-overlay" id="invite-guide-overlay" role="dialog" aria-modal="true" aria-labelledby="invite-guide-title">
          <div class="invite-guide-dialog">
            <button class="invite-guide-close" type="button" data-invite-guide-close data-aria-fr="Fermer" data-aria-en="Close" aria-label="Fermer">&times;</button>
            <div class="invite-guide-language" role="group" aria-label="Language"><button type="button" data-invite-language="fr" aria-pressed="true">FR</button><button type="button" data-invite-language="en" aria-pressed="false">EN</button></div>
            <p class="invite-guide-kicker" data-fr="Invitation créée" data-en="Invitation created">Invitation créée</p>
            <h2 id="invite-guide-title" data-fr="Partagez cette invitation" data-en="Share this invitation">Partagez cette invitation</h2>
            <p class="invite-guide-text" data-fr="Vous pouvez copier ce lien d’invitation, ou cliquer dessus pour créer le nom d’utilisateur et le mot de passe temporaire." data-en="You can copy this invitation link, or click it to create the username and temporary password.">Vous pouvez copier ce lien d’invitation, ou cliquer dessus pour créer le nom d’utilisateur et le mot de passe temporaire.</p>
            <div class="invite-guide-link"><a id="created-invite-link" href="{html.escape(created_invite_url)}" target="_blank" rel="noopener">{html.escape(created_invite_url)}</a></div>
            <p class="invite-guide-text" data-fr="Envoyez ensuite le lien ou les informations de connexion à votre employé ou au parent en dehors de l’application." data-en="Then send the link or login information to your employee or the parent outside the app.">Envoyez ensuite le lien ou les informations de connexion à votre employé ou au parent en dehors de l’application.</p>
            <div class="invite-guide-actions">
              <button class="btn primary" id="copy-created-invite" type="button" data-fr="Copier l’invitation" data-en="Copy invitation">Copier l’invitation</button>
              <a class="btn green" href="{html.escape(created_invite_url)}" target="_blank" rel="noopener" data-fr="Ouvrir l’invitation" data-en="Open invitation">Ouvrir l’invitation</a>
              <button class="btn gray" type="button" data-invite-guide-close data-fr="Fermer" data-en="Close">Fermer</button>
            </div>
            <div class="invite-guide-status" id="invite-guide-status" aria-live="polite" data-fr="" data-en=""></div>
          </div>
        </div>
        <script>
        (function() {{
          const overlay = document.getElementById('invite-guide-overlay');
          if (!overlay) return;
          let currentLanguage = 'fr';
          function setLanguage(language) {{
            currentLanguage = language === 'en' ? 'en' : 'fr';
            overlay.querySelectorAll('[data-fr][data-en]').forEach(function(element) {{
              element.textContent = element.getAttribute('data-' + currentLanguage) || '';
            }});
            overlay.querySelectorAll('[data-aria-fr][data-aria-en]').forEach(function(element) {{
              element.setAttribute('aria-label', element.getAttribute('data-aria-' + currentLanguage) || '');
            }});
            overlay.querySelectorAll('[data-invite-language]').forEach(function(button) {{
              button.setAttribute('aria-pressed', button.getAttribute('data-invite-language') === currentLanguage ? 'true' : 'false');
            }});
            document.documentElement.lang = currentLanguage;
            try {{ window.localStorage.setItem('pititpas-language', currentLanguage); }} catch (_error) {{}}
          }}
          function closeGuide() {{ overlay.remove(); }}
          function copyFallback(text) {{
            const input = document.createElement('textarea');
            input.value = text;
            input.style.position = 'fixed';
            input.style.opacity = '0';
            document.body.appendChild(input);
            input.select();
            const copied = document.execCommand('copy');
            input.remove();
            return copied;
          }}
          function showCopyResult(success) {{
            const status = document.getElementById('invite-guide-status');
            if (!status) return;
            status.textContent = success ? (currentLanguage === 'en' ? 'Invitation copied.' : 'Invitation copiée.') : (currentLanguage === 'en' ? 'Copy failed. Select and copy the link above.' : 'La copie a échoué. Sélectionnez et copiez le lien ci-dessus.');
          }}
          overlay.querySelectorAll('[data-invite-language]').forEach(function(button) {{
            button.addEventListener('click', function() {{ setLanguage(button.getAttribute('data-invite-language')); }});
          }});
          overlay.querySelectorAll('[data-invite-guide-close]').forEach(function(button) {{ button.addEventListener('click', closeGuide); }});
          overlay.addEventListener('click', function(event) {{ if (event.target === overlay) closeGuide(); }});
          document.addEventListener('keydown', function(event) {{ if (event.key === 'Escape' && document.getElementById('invite-guide-overlay')) closeGuide(); }});
          const copyButton = document.getElementById('copy-created-invite');
          const inviteLink = document.getElementById('created-invite-link');
          if (copyButton && inviteLink) {{
            copyButton.addEventListener('click', function() {{
              const text = inviteLink.href;
              if (navigator.clipboard && window.isSecureContext) {{
                navigator.clipboard.writeText(text).then(function() {{ showCopyResult(true); }}).catch(function() {{ showCopyResult(copyFallback(text)); }});
              }} else {{
                showCopyResult(copyFallback(text));
              }}
            }});
          }}
          let savedLanguage = '';
          try {{ savedLanguage = window.localStorage.getItem('pititpas-language') || ''; }} catch (_error) {{}}
          setLanguage(savedLanguage === 'en' ? 'en' : 'fr');
          if (copyButton) window.setTimeout(function() {{ copyButton.focus(); }}, 0);
        }})();
        </script>
        """
    add_person_panel_html = f"""
    <div class="panel">
      <h3>Ajouter utilisateur</h3>
      <div class="muted small" style="margin-bottom:8px">Ajouter génère automatiquement une invitation mobile pour terminer l'inscription.</div>
      <form method="post" action="/children/create" class="user-grid children-add-group">
        <input type="hidden" name="return_to" value="/users">
        <div><label>Name</label><input name="name" required></div>
        <div>
          <label>Role</label>
          <select name="role" required>
            {"".join(f'<option value="{html.escape(role)}" {"selected" if role == "children" else ""}>{html.escape(ROLE_LABELS.get(role, role))}</option>' for role in creatable_roles_for_user(user))}
          </select>
        </div>
        <div>
          <label>Groupe</label>
          <div class="group-field-action">
            <input name="class_name" list="account-child-group-options" placeholder="Select or type a new group">
            <button class="group-action-btn" type="button" data-delete-selected-group aria-label="Supprimer groupe">⋯</button>
          </div>
        </div>
        <div><label>E-MAIL invitation</label><input name="email" type="email" placeholder="nom@example.com"></div>
        <datalist id="account-child-group-options">{class_options}</datalist>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Ajouter</button></div>
      </form>
    </div>
    """
    upload_panel_html = f"""
    <div class="panel" style="margin-top:16px">
      <div style="display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap">
        <form method="post" action="/children/load-list" enctype="multipart/form-data" class="btn-row children-load-list-form" style="align-items:end">
          <input type="hidden" name="return_to" value="/users">
          <div>
            <label>Load list</label>
            <input type="file" name="child_list_file" accept="{schedule_file_accept_types()}" required>
          </div>
          <button class="btn primary children-load-list-btn" type="submit">Load list</button>
        </form>
        <form method="post" action="/children/import-avatars" enctype="multipart/form-data" class="btn-row children-avatar-form" style="align-items:end">
          <input type="hidden" name="return_to" value="/users">
          <div>
            <label>Avatars cartes</label>
            <input type="file" name="avatar_files" accept="image/*" multiple required>
            <div class="small muted">Nom du fichier = nom de l'enfant. Seul le visage détecté est enregistré.</div>
          </div>
          <button class="btn amber children-avatar-btn" type="submit">Ajouter avatars</button>
        </form>
      </div>
    </div>
    """
    users_panel_html = f"""
    <div class="panel" style="margin-top:16px">
      <h2>ACCOUNT</h2>
      <div class="muted">Modifier et supprimer des utilisateurs.</div>
      <div class="muted small" style="margin-top:8px">Total users: {total_users}</div>
      <div class="btn-row" style="margin-top:10px">
        <button class="btn red" type="button" id="users-bulk-delete-btn">Supprimer sélection</button>
        <a class="btn ghost" href="/users/export.xlsx">Exporter account list</a>
        {"<a class='btn ghost' href='/deleted-users'>Archive supprimés</a>" if user["role"] == "boss" else ""}
      </div>
      <form id="users-bulk-delete-form" method="post" action="/users/delete" style="display:none" onsubmit="return confirm('Delete the selected users?')"></form>
      <div class="table-wrap users-records-scroll" style="margin-top:12px">
        <table class="users-compact-table">
          <colgroup>
            <col class="account-col-select">
            <col class="account-col-username">
            <col class="account-col-name">
            <col class="account-col-role">
            <col class="account-col-classes">
            <col class="account-col-device">
            <col class="account-col-password">
            <col class="account-col-action">
          </colgroup>
          <thead><tr>
            <th style="width:34px;text-align:center"><input type="checkbox" id="users-select-all" aria-label="Select all users"></th>
            <th class="sortable-head"><a href="/account?sort=username">Username</a></th>
            <th class="sortable-head"><a href="/account?sort=name">Name</a></th>
            <th class="sortable-head"><a href="/account?sort=role">Role</a></th>
            <th class="sortable-head"><a href="/account?sort=classes">Classes</a></th>
            <th class="sortable-head"><a href="/account?sort=device">Mobile device</a></th>
            <th>Password changed</th>
            <th>Action</th>
          </tr></thead>
          <tbody>{''.join(table_rows) or '<tr><td colspan="8" class="muted">No users</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    invite_person_delete_button = ""
    invite_person_action_class = "invite-person-action"
    if user["role"] == "boss":
        invite_person_action_class = "invite-person-action has-delete"
        invite_person_delete_button = '<button class="person-action-btn" type="button" data-delete-invite-person aria-label="Supprimer personne">⋯</button>'
    invite_panel_html = f"""
    <div class="panel" id="invite-user">
      <h3>Inviter utilisateur mobile</h3>
      {created_invite_panel}
      <form method="post" action="/mobile-invitations/create" class="user-grid">
        <input type="hidden" name="return_to" value="/users">
        <div>
          <label>Personne</label>
          <div class="{invite_person_action_class}">
            <select name="invite_target" id="invite-target-select" required>{''.join(invite_person_options)}</select>
            {invite_person_delete_button}
          </div>
        </div>
        <div><label>MESSAGE</label><input name="email" type="email" required placeholder="nom@example.com"></div>
        <div><label>Valide pendant</label>
          <select name="days">
            <option value="7">7 jours</option>
            <option value="14">14 jours</option>
            <option value="30">30 jours</option>
          </select>
        </div>
        <div style="display:flex;align-items:end"><button class="btn green" type="submit">Inviter</button></div>
      </form>
      <div class="table-wrap invite-records-scroll" style="margin-top:12px">
        <table>
          <thead><tr><th>Nom</th><th>MESSAGE</th><th>Créée</th><th>Statut</th><th>Lien</th></tr></thead>
          <tbody>{''.join(invite_rows) or '<tr><td colspan="5" class="muted">Aucune invitation</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    pending_page_html = "" if account_only else pending_html
    add_person_page_html = "" if account_only else add_person_panel_html
    invite_page_html = "" if account_only else invite_panel_html
    users_page_html = users_panel_html if account_only else ""
    upload_page_html = "" if account_only else upload_panel_html
    body = f"""
    <style>
      .action-select {{ width:46px; min-width:46px; height:32px; padding:3px 6px; border:1px solid var(--line-strong); border-radius:6px; background:#fff; color:var(--text); font-weight:700; cursor:pointer; }}
      .action-select:focus {{ width:150px; }}
      .sortable-head a {{ color:inherit; font-weight:700; text-decoration:none; }}
      .sortable-head a:hover {{ text-decoration:underline; }}
      .user-select {{ width: 16px; height: 16px; }}
      .invite-records-scroll {{ max-height: 150px; overflow-y: auto; }}
      .users-records-scroll {{ max-height:376px; overflow:auto; }}
      .invite-records-scroll table {{ margin: 0; }}
      .users-records-scroll table {{ margin:0; width:min(100%, 1040px); min-width:880px; table-layout:fixed; }}
      .invite-records-scroll thead th,
      .users-records-scroll thead th {{ position: sticky; top: 0; z-index: 1; }}
      .invite-records-scroll th, .invite-records-scroll td,
      .users-compact-table th, .users-compact-table td {{ padding-top:0; padding-bottom:0; line-height:1.1; }}
      .users-compact-table th, .users-compact-table td {{ padding-left:5px; padding-right:5px; vertical-align:middle; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; box-sizing:border-box; }}
      .users-compact-table thead tr {{ height:36px; }}
      .users-compact-table tbody tr {{ height:34px; }}
      .account-col-select {{ width:4%; }}
      .account-col-username {{ width:15%; }}
      .account-col-name {{ width:17%; }}
      .account-col-role {{ width:11%; }}
      .account-col-classes {{ width:12%; }}
      .account-col-device {{ width:18%; }}
      .account-col-password {{ width:17%; }}
      .account-col-action {{ width:6%; }}
      .invite-records-scroll .btn {{ min-height:0; padding:0 6px; line-height:1.1; }}
      .classes-cell {{ white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}
      .group-field-action, .invite-person-action.has-delete {{ display:grid; grid-template-columns:minmax(0,1fr) 34px; gap:6px; align-items:center; }}
      .children-add-group input[name="class_name"] {{ min-height:40px; height:40px; line-height:1.2; }}
      .group-action-btn, .person-action-btn {{ width:30px; height:30px; border:1px solid #d6dee9; border-radius:50%; background:#f6f9fc; color:#30465c; font-size:20px; line-height:1; cursor:pointer; display:inline-flex; align-items:center; justify-content:center; padding:0; }}
      .group-action-btn:hover, .person-action-btn:hover {{ background:#eef4fb; }}
    </style>
    {pending_page_html}
    {add_person_page_html}
    {invite_page_html}
    {users_page_html}
    {upload_page_html}
    <script>
    (function() {{
      const checkboxes = Array.from(document.querySelectorAll('[data-user-checkbox]'));
      const selectAll = document.getElementById('users-select-all');
      const bulkDeleteBtn = document.getElementById('users-bulk-delete-btn');
      const bulkDeleteForm = document.getElementById('users-bulk-delete-form');
      let lastCheckedIndex = null;
      function syncSelectAll() {{
        if (!selectAll) return;
        const total = checkboxes.length;
        const checked = checkboxes.filter(function(box) {{ return box.checked; }}).length;
        selectAll.checked = total > 0 && checked === total;
        selectAll.indeterminate = checked > 0 && checked < total;
      }}
      function selectRange(start, end, checked) {{
        const from = Math.min(start, end);
        const to = Math.max(start, end);
        for (let i = from; i <= to; i += 1) {{
          checkboxes[i].checked = checked;
        }}
      }}
      checkboxes.forEach(function(box, index) {{
        box.addEventListener('click', function(event) {{
          if (event.shiftKey && lastCheckedIndex !== null) {{
            selectRange(lastCheckedIndex, index, box.checked);
          }}
          lastCheckedIndex = index;
          syncSelectAll();
        }});
      }});
      if (selectAll) {{
        selectAll.addEventListener('change', function() {{
          checkboxes.forEach(function(box) {{ box.checked = selectAll.checked; }});
          syncSelectAll();
        }});
      }}
      if (bulkDeleteBtn && bulkDeleteForm) {{
        bulkDeleteBtn.addEventListener('click', function() {{
          const selected = checkboxes.filter(function(box) {{ return box.checked; }}).map(function(box) {{ return box.value; }});
          if (!selected.length) {{
            alert('Select at least one user.');
            return;
          }}
          bulkDeleteForm.innerHTML = '';
          selected.forEach(function(id) {{
            const input = document.createElement('input');
            input.type = 'hidden';
            input.name = 'ids';
            input.value = id;
            bulkDeleteForm.appendChild(input);
          }});
          bulkDeleteForm.submit();
        }});
      }}
      syncSelectAll();
      document.querySelectorAll('[data-delete-selected-group]').forEach(function(button) {{
        button.addEventListener('click', function() {{
          const wrap = button.closest('.group-field-action');
          const input = wrap ? wrap.querySelector('input[name="class_name"]') : null;
          const groupName = input ? input.value.trim() : '';
          if (!groupName) {{
            alert('Sélectionnez un groupe à supprimer.');
            return;
          }}
          if (!window.confirm('Supprimer ce groupe de la liste ? ' + groupName)) return;
          const form = document.createElement('form');
          form.method = 'post';
          form.action = '/children/group/delete';
          const groupInput = document.createElement('input');
          groupInput.type = 'hidden';
          groupInput.name = 'group_name';
          groupInput.value = groupName;
          const returnInput = document.createElement('input');
          returnInput.type = 'hidden';
          returnInput.name = 'return_to';
          returnInput.value = '/users';
          form.appendChild(groupInput);
          form.appendChild(returnInput);
          document.body.appendChild(form);
          form.submit();
        }});
      }});
      document.querySelectorAll('[data-delete-invite-person]').forEach(function(button) {{
        button.addEventListener('click', function() {{
          const select = document.getElementById('invite-target-select');
          if (!select || !select.value) {{
            alert('Sélectionnez une personne à supprimer.');
            return;
          }}
          if (!select.value.startsWith('person:')) {{
            alert('Ce bouton supprime seulement les personnes sans compte actif.');
            return;
          }}
          const option = select.options[select.selectedIndex];
          const label = option ? option.text : '';
          if (!window.confirm('Supprimer cette personne de la liste ? ' + label)) return;
          const form = document.createElement('form');
          form.method = 'post';
          form.action = '/invite-person/delete';
          const input = document.createElement('input');
          input.type = 'hidden';
          input.name = 'person_id';
          input.value = select.value.split(':')[1] || '';
          form.appendChild(input);
          document.body.appendChild(form);
          form.submit();
        }});
      }});
    }})();
    function postUserAction(action, id) {{
      var form = document.createElement('form');
      form.method = 'post';
      form.action = action;
      var input = document.createElement('input');
      input.type = 'hidden';
      input.name = 'id';
      input.value = id;
      form.appendChild(input);
      document.body.appendChild(form);
      form.submit();
    }}
    function handleUserAction(select) {{
      var option = select.options[select.selectedIndex];
      var value = option ? option.value : '';
      if (!value) return;
      var href = option.getAttribute('data-href');
      var id = option.getAttribute('data-id');
      var message = option.getAttribute('data-confirm') || '';
      select.selectedIndex = 0;
      if (href) {{
        window.location.href = href;
        return;
      }}
      if (message && !window.confirm(message)) return;
      if (value === 'reset_device' && id) {{
        postUserAction('/users/reset-mobile-device', id);
        return;
      }}
      if (value === 'delete' && id) {{
        postUserAction('/users/delete', id);
      }}
    }}
    </script>
    """
    return html_page("ACCOUNT" if account_only else "INVITATIONS", user, body, flash=flash)


def render_children_admin(user, query):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage children.</div>')
    flash = None
    if query.get("imported", [""])[0] == "1":
        flash = (
            "info",
            "Load list terminé. Créés: {}. Mis à jour: {}. Ignorés: {}.".format(
                query.get("created", ["0"])[0],
                query.get("updated", ["0"])[0],
                query.get("skipped", ["0"])[0],
            ),
        )
    if query.get("deleted", [""])[0] == "1":
        flash = ("info", "Selected children deleted successfully.")
    if query.get("group_deleted", [""])[0] == "1":
        flash = ("info", "Group name removed from the dropdown.")
    if query.get("group_changed", [""])[0] == "1":
        flash = ("info", "Child group updated successfully.")
    if query.get("avatars", [""])[0] == "1":
        flash = (
            "info",
            "Avatars importés: {}. Ignorés: {}.".format(
                query.get("updated", ["0"])[0],
                query.get("skipped", ["0"])[0],
            ),
        )
    account_flash_token = query.get("account_flash", [""])[0].strip()
    if account_flash_token:
        account_flash = FLASH_MESSAGES.pop(account_flash_token, None)
        if account_flash:
            flash = account_flash
    pending_preview = None
    pending_token = query.get("pending_import", [""])[0].strip()
    sort_key = query.get("sort", ["name"])[0].strip().lower()
    if sort_key not in {"name", "group"}:
        sort_key = "name"
    if pending_token:
        pending_preview = get_pending_child_list_import(pending_token, user["id"])
        if pending_preview is None:
            flash = ("warn", "The import preview expired. Please upload the file again.")
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        hidden_groups = {
            row["name"]
            for row in conn.execute("SELECT name FROM hidden_class_names WHERE project_id = ?", (project_id,)).fetchall()
        }
        classes = get_classes(conn, user)
        top_group_names = [row["class_name"] for row in conn.execute(
            """
            SELECT DISTINCT class_name
            FROM persons
            WHERE role = 'children' AND class_name <> '' AND project_id = ?
            ORDER BY class_name COLLATE NOCASE
            """
            , (project_id,)
        ).fetchall()]
        group_names = []
        for name in classes + top_group_names:
            if name and name not in hidden_groups and name not in group_names:
                group_names.append(name)
        order_clause = "ORDER BY persons.name COLLATE NOCASE, persons.class_name COLLATE NOCASE" if sort_key == "name" else "ORDER BY persons.class_name COLLATE NOCASE, persons.name COLLATE NOCASE"
        children = conn.execute(
            """
            SELECT id, name, role, class_name, photo_path, created_at
            FROM persons
            WHERE role IN ('children', 'teachers')
              AND project_id = ?
              AND id NOT IN (
                SELECT person_id
                FROM deleted_user_archives
                WHERE person_id IS NOT NULL
                  AND project_id = ?
              )
            """
            + order_clause
            , (project_id, project_id)
        ).fetchall()
    total_children = len(children)
    rows = "".join(
        f"""
        <tr>
          <td style="text-align:center">
            <input class="child-select" type="checkbox" name="ids" value="{child['id']}" data-child-checkbox>
          </td>
          <td>{html.escape(child['name'])}</td>
          <td>{html.escape('Enfant' if child['role'] == 'children' else 'Employé')}</td>
          <td>{html.escape(child['class_name'] or '')}</td>
          <td>{html.escape(child['photo_path'] or '')}</td>
          <td>{html.escape(child['created_at'])}</td>
          <td class="nowrap">
            <div class="child-action-wrap" data-child-action-wrap>
              <button type="button" class="child-action-trigger" data-child-action-trigger="{child['id']}" aria-label="Actions">⋯</button>
              <div class="child-action-menu" data-child-action-menu="{child['id']}" aria-hidden="true">
                {f'<a href="/children/edit?id={child["id"]}">Modifier</a>' if child["role"] == "children" else ""}
                <a href="/users?invite_person_id={child['id']}#invite-user">Inviter</a>
                <form method="post" action="/children/delete" onsubmit="return confirm('Delete this person and attendance records?')">
                  <input type="hidden" name="id" value="{child['id']}">
                  <button type="submit">Supprimer</button>
                </form>
              </div>
            </div>
          </td>
        </tr>
        """
            for child in children
    )
    class_options = "".join(f'<option value="{html.escape(cls)}">{html.escape(cls)}</option>' for cls in group_names)
    group_manager_rows = "".join(
        f"""
        <tr data-group-row="{html.escape(group, quote=True)}">
          <td>{html.escape(group)}</td>
          <td class="right">
            <form method="post" action="/children/group/delete" class="group-hide-form" data-group-name="{html.escape(group, quote=True)}">
              <input type="hidden" name="group_name" value="{html.escape(group, quote=True)}">
              <button class="group-action-btn" type="submit" aria-label="Hide group">⋯</button>
            </form>
          </td>
        </tr>
        """
        for group in group_names
    )
    pending_html = ""
    if pending_preview:
        preview_rows = "".join(
            f"<tr><td>{html.escape(name)}</td><td>{html.escape(group)}</td></tr>"
            for name, group in pending_preview["entries"]
        )
        pending_html = f"""
        <div class="panel" style="margin-bottom:16px">
          <h3>Confirm child list import</h3>
          <div class="alert warn">File: {html.escape(pending_preview['filename'] or '')}. Rows detected: {len(pending_preview['entries'])}.</div>
          <div class="table-wrap" style="max-height:260px; overflow:auto">
            <table>
              <thead><tr><th>Name</th><th>Groupe</th></tr></thead>
              <tbody>{preview_rows}</tbody>
            </table>
          </div>
          <div class="btn-row" style="margin-top:12px">
            <form method="post" action="/children/load-list/confirm">
              <input type="hidden" name="token" value="{html.escape(pending_token, quote=True)}">
              <button class="btn primary" type="submit">Confirm and save</button>
            </form>
            <a class="btn gray" href="/children">Cancel</a>
          </div>
        </div>
        """
    body = f"""
    {pending_html}
    <div class="panel">
      <div style="display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap">
        <form method="post" action="/children/load-list" enctype="multipart/form-data" class="btn-row children-load-list-form" style="align-items:end">
          <div>
            <label>Load list</label>
            <input type="file" name="child_list_file" accept="{schedule_file_accept_types()}" required>
          </div>
          <button class="btn primary children-load-list-btn" type="submit">Load list</button>
        </form>
        <form method="post" action="/children/import-avatars" enctype="multipart/form-data" class="btn-row children-avatar-form" style="align-items:end">
          <div>
            <label>Avatars cartes</label>
            <input type="file" name="avatar_files" accept="image/*" multiple required>
            <div class="small muted">Nom du fichier = nom de l'enfant. Seul le visage détecté est enregistré.</div>
          </div>
          <button class="btn amber children-avatar-btn" type="submit">Ajouter avatars</button>
        </form>
        <div class="btn-row" style="align-items:center">
          <button class="btn red" type="button" id="children-bulk-delete-btn">Supprimer sélection</button>
          <a class="btn primary" href="/children/cards" target="_blank">Cartes à imprimer</a>
        </div>
      </div>
      <div class="muted small" style="margin-top:10px">Total records: {total_children}</div>
      <form id="children-bulk-delete-form" method="post" action="/children/delete" style="display:none" onsubmit="return confirm('Delete the selected people and attendance records?')"></form>
      <div class="table-wrap" style="margin-top:12px;max-height:420px;overflow:auto">
        <table>
          <thead><tr><th style="width:34px;text-align:center"><input type="checkbox" id="children-select-all" aria-label="Select all people"></th><th class="sortable-head"><a href="/children?sort=name">Name</a></th><th>Type</th><th class="sortable-head"><a href="/children?sort=group">Groupe</a></th><th>Photo path</th><th>Created</th><th>Action</th></tr></thead>
          <tbody>{rows or '<tr><td colspan="7" class="muted">No people found</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <div class="panel" style="margin-top:16px">
      <div class="table-wrap" style="margin-bottom:12px;max-height:92px;overflow:auto">
        <table>
          <thead><tr><th>Groupe</th><th class="right">Action</th></tr></thead>
          <tbody>{group_manager_rows or '<tr><td colspan="2" class="muted">No groups found</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <style>
      .child-action-wrap {{ position: relative; display: inline-block; }}
      .child-action-trigger {{
        width: 34px;
        height: 34px;
        border: 1px solid #d6dee9;
        border-radius: 50%;
        background: #f6f9fc;
        color: #30465c;
        font-size: 24px;
        line-height: 1;
        cursor: pointer;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        padding: 0;
      }}
      .children-add-group input[name="class_name"] {{
        min-height: 40px;
        height: 40px;
        line-height: 1.2;
      }}
      @media (max-width:720px) {{
        .children-load-list-form {{ display:grid; grid-template-columns:1fr; width:100%; gap:8px; }}
        .children-load-list-btn {{ width:100%; min-height:40px; }}
        .children-avatar-form {{ display:grid; grid-template-columns:1fr; width:100%; gap:8px; }}
        .children-avatar-btn {{ width:100%; min-height:40px; }}
        .children-avatar-form + .btn-row {{ display:grid; grid-template-columns:1fr; width:100%; gap:8px; }}
        .children-avatar-form + .btn-row .btn {{ width:100%; min-height:40px; }}
      }}
      .child-action-trigger:hover {{ background: #eef4fb; }}
      .child-action-menu {{
        position: absolute;
        top: calc(100% + 6px);
        right: 0;
        z-index: 30;
        display: none;
        min-width: 128px;
        padding: 6px;
        border: 1px solid #d8e1eb;
        border-radius: 8px;
        background: #fff;
        box-shadow: 0 16px 32px rgba(21, 34, 56, 0.18);
      }}
      .child-action-menu.show {{ display: block; }}
      .child-action-menu a,
      .child-action-menu button {{
        display: block;
        width: 100%;
        border: 0;
        background: transparent;
        color: #1f2d3d;
        text-align: left;
        padding: 8px 10px;
        border-radius: 6px;
        cursor: pointer;
        font: inherit;
        text-decoration: none;
      }}
      .child-action-menu a:hover,
      .child-action-menu button:hover {{ background: #eef6ff; text-decoration: none; }}
      .child-action-menu form {{ margin: 0; }}
      .child-action-menu form button {{ color: #8a2430; }}
      .child-action-menu form button:hover {{ background: #fff1f3; }}
      .group-action-btn {{
        width: 34px;
        height: 34px;
        border: 1px solid #d6dee9;
        border-radius: 50%;
        background: #f6f9fc;
        color: #30465c;
        font-size: 24px;
        line-height: 1;
        cursor: pointer;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        padding: 0;
      }}
      .group-action-btn:hover {{ background: #eef4fb; }}
      .sortable-head a {{ color: inherit; font-weight: 700; text-decoration: none; }}
      .sortable-head a:hover {{ text-decoration: underline; }}
    </style>
    <script>
    (function() {{
      document.querySelectorAll('.group-hide-form').forEach(function(form) {{
        form.addEventListener('submit', async function(event) {{
          event.preventDefault();
          const groupName = form.getAttribute('data-group-name') || '';
          if (!groupName) return;
          if (!window.confirm('Hide this group from the dropdown?')) return;
          try {{
            const response = await fetch(form.action, {{
              method: 'POST',
              body: new FormData(form),
              credentials: 'same-origin',
            }});
            if (!response.ok) throw new Error('Request failed');
            const row = form.closest('tr[data-group-row]');
            if (row) row.remove();
          }} catch (error) {{
            alert('Unable to hide this group right now.');
          }}
        }});
      }});
      const checkboxes = Array.from(document.querySelectorAll('[data-child-checkbox]'));
      const selectAll = document.getElementById('children-select-all');
      const bulkDeleteBtn = document.getElementById('children-bulk-delete-btn');
      const bulkDeleteForm = document.getElementById('children-bulk-delete-form');
      let lastCheckedIndex = null;
      function syncSelectAll() {{
        if (!selectAll) return;
        const total = checkboxes.length;
        const checked = checkboxes.filter(function(box) {{ return box.checked; }}).length;
        selectAll.checked = total > 0 && checked === total;
        selectAll.indeterminate = checked > 0 && checked < total;
      }}
      function selectRange(start, end, checked) {{
        const from = Math.min(start, end);
        const to = Math.max(start, end);
        for (let i = from; i <= to; i += 1) {{
          checkboxes[i].checked = checked;
        }}
      }}
      checkboxes.forEach(function(box, index) {{
        box.addEventListener('click', function(event) {{
          if (event.shiftKey && lastCheckedIndex !== null) {{
            selectRange(lastCheckedIndex, index, box.checked);
          }}
          lastCheckedIndex = index;
          syncSelectAll();
        }});
      }});
      if (selectAll) {{
        selectAll.addEventListener('change', function() {{
          checkboxes.forEach(function(box) {{ box.checked = selectAll.checked; }});
          syncSelectAll();
        }});
      }}
      if (bulkDeleteBtn && bulkDeleteForm) {{
        bulkDeleteBtn.addEventListener('click', function() {{
          const selected = checkboxes.filter(function(box) {{ return box.checked; }}).map(function(box) {{ return box.value; }});
          if (!selected.length) {{
            alert('Select at least one child.');
            return;
          }}
          bulkDeleteForm.innerHTML = '';
          selected.forEach(function(id) {{
            const input = document.createElement('input');
            input.type = 'hidden';
            input.name = 'ids';
            input.value = id;
            bulkDeleteForm.appendChild(input);
          }});
          if (confirm('Delete ' + selected.length + ' selected child(ren) and attendance records?')) {{
            bulkDeleteForm.submit();
          }}
        }});
      }}
      const closeMenus = function() {{
        document.querySelectorAll('[data-child-action-menu].show').forEach(function(menu) {{
          menu.classList.remove('show');
          menu.setAttribute('aria-hidden', 'true');
        }});
      }};
      document.addEventListener('click', function(event) {{
        const trigger = event.target.closest('[data-child-action-trigger]');
        const menu = event.target.closest('[data-child-action-menu]');
        if (trigger) {{
          const targetId = trigger.getAttribute('data-child-action-trigger');
          const targetMenu = document.querySelector('[data-child-action-menu="' + targetId + '"]');
          if (!targetMenu) return;
          const willOpen = !targetMenu.classList.contains('show');
          closeMenus();
          if (willOpen) {{
            targetMenu.classList.add('show');
            targetMenu.setAttribute('aria-hidden', 'false');
          }}
          event.preventDefault();
          event.stopPropagation();
          return;
        }}
        if (menu) {{
          return;
        }}
        closeMenus();
      }});
      document.addEventListener('keydown', function(event) {{
        if (event.key === 'Escape') closeMenus();
      }});
      syncSelectAll();
    }})();
    </script>
    """
    return html_page("Children", user, body, flash=flash)


def render_children_cards_print(user):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage children.</div>')
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        children = conn.execute(
            """
            SELECT id, name, class_name, photo_path, qr_token
            FROM persons
            WHERE role = 'children'
              AND project_id = ?
            ORDER BY class_name, name
            """,
            (project_id,),
        ).fetchall()

    cards = []
    for child in children:
        photo_url = child_card_image_url(child["photo_path"])
        initials = "".join(part[:1] for part in (child["name"] or "").split()[:2]).upper() or "?"
        photo_html = (
            f'<img src="{html.escape(photo_url)}" alt="">'
            if photo_url
            else f'<div class="print-card-placeholder">{html.escape(initials)}</div>'
        )
        qr_token = child["qr_token"] or f"CHILD:{child['name']}"
        existing_qr_url = existing_child_qr_image_url(child["name"], qr_token)
        qr_url = qr_token_image_data_url(qr_token)
        qr_html = (
            f'<img src="{html.escape(existing_qr_url)}" alt="">'
            if existing_qr_url
            else f'<img src="{html.escape(qr_url)}" alt="">'
            if qr_url
            else f'<canvas class="qr-js" width="104" height="104" data-token="{html.escape(qr_token, quote=True)}"></canvas>'
        )
        name_parts = [part for part in (child["name"] or "").split() if part]
        first_name = name_parts[0] if name_parts else child["name"]
        last_name = name_parts[-1] if len(name_parts) > 1 else ""
        cards.append(
            f"""
            <article class="print-child-card">
              <div class="print-card-top">
                <div class="print-card-photo">{photo_html}</div>
                <div class="print-card-info">
                  <div class="print-card-first-name">{html.escape(first_name)}</div>
                  {f'<div class="print-card-last-name">{html.escape(last_name)}</div>' if last_name else ''}
                </div>
              </div>
              <div class="print-card-qr">{qr_html}</div>
            </article>
            """
        )

    body = f"""
    <style>
      .print-toolbar {{ display:flex; align-items:center; justify-content:space-between; gap:10px; margin-bottom:14px; }}
      .print-card-grid {{ display:grid; grid-template-columns:repeat(auto-fill, minmax(280px, 1fr)); gap:22px; }}
      .print-child-card {{ break-inside:avoid; page-break-inside:avoid; display:flex; flex-direction:column; gap:14px; min-height:248px; padding:16px; border:1px solid #9fb7d6; border-radius:8px; background:#fff; }}
      .print-card-top {{ display:grid; grid-template-columns:98px minmax(0, 1fr); gap:16px; align-items:center; }}
      .print-card-photo img, .print-card-placeholder {{ width:98px; height:98px; border-radius:8px; border:1px solid #c7d7ea; object-fit:cover; background:#edf6ff; }}
      .print-card-placeholder {{ display:flex; align-items:center; justify-content:center; color:#244463; font-size:28px; font-weight:700; }}
      .print-card-info {{ min-width:0; display:flex; flex-direction:column; justify-content:center; gap:8px; }}
      .print-card-first-name, .print-card-last-name {{ color:#0f2742; font-size:22px; font-weight:700; line-height:1.12; overflow-wrap:anywhere; }}
      .print-card-qr {{ display:flex; align-items:center; justify-content:center; min-width:0; padding-top:2px; }}
      .print-card-qr img {{ width:104px; height:104px; image-rendering:pixelated; }}
      .qr-js {{ width:104px; height:104px; display:block; }}
      .print-qr-svg {{ width:104px; height:104px; display:block; }}
      .print-qr-fallback {{ width:104px; min-height:104px; display:flex; align-items:center; justify-content:center; text-align:center; overflow-wrap:anywhere; border:1px solid #c7d7ea; border-radius:6px; padding:5px; color:#26384d; font-size:11px; line-height:1.15; background:#f8fbff; }}
      @media print {{
        @page {{ margin: 10mm; }}
        .print-toolbar {{ display:none !important; }}
        .print-card-grid {{ grid-template-columns:repeat(3, 1fr); gap:18px; }}
        .print-child-card {{ min-height:232px; padding:14px; border-color:#8aa7c8; }}
      }}
    </style>
    <div class="panel no-print print-toolbar">
      <div>
        <h2>Cartes des enfants</h2>
        <div class="muted small">{len(children)} enfants</div>
      </div>
      <div class="btn-row">
        <a class="btn" href="/children">Retour</a>
        <button class="btn primary" type="button" onclick="window.print()">Imprimer</button>
      </div>
    </div>
    <div class="panel">
      <div class="print-card-grid">
        {''.join(cards) if cards else '<div class="muted">Aucun enfant trouvé.</div>'}
      </div>
    </div>
    <script>
      (function() {{
        const canvases = Array.from(document.querySelectorAll("canvas.qr-js"));
        if (!canvases.length) return;
        function drawCodes() {{
          if (!window.QRCode || !window.QRCode.toCanvas) return;
          canvases.forEach(function(canvas) {{
            window.QRCode.toCanvas(canvas, canvas.dataset.token || "", {{
              width: 104,
              margin: 1,
              errorCorrectionLevel: "L"
            }});
          }});
        }}
        if (window.QRCode && window.QRCode.toCanvas) {{
          drawCodes();
          return;
        }}
        const script = document.createElement("script");
        script.src = "https://cdn.jsdelivr.net/npm/qrcode@1.5.3/build/qrcode.min.js";
        script.onload = drawCodes;
        script.onerror = function() {{
          canvases.forEach(function(canvas) {{
            const fallback = document.createElement("div");
            fallback.className = "print-qr-fallback";
            fallback.textContent = canvas.dataset.token || "";
            canvas.replaceWith(fallback);
          }});
        }};
        document.head.appendChild(script);
      }})();
    </script>
    """
    return html_page("Cartes des enfants", user, body)


def render_mobile_invitations(user, query):
    if user["role"] not in {"principal", "boss"}:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage mobile invitations.</div>')
    connection_sort = query.get("connection_sort", ["status"])[0].strip().lower()
    if connection_sort not in {"status", "user", "ip", "mac", "device"}:
        connection_sort = "status"
    with connect_db() as conn:
        project_id = effective_project_id(conn, user)
        project = current_project(conn, user)
        logo_url = project_logo_url(project)
        location_policy = attendance_location_payload(conn, user)
        face_reset_people = conn.execute(
            """
            SELECT persons.id, persons.name, web_users.display_name, web_users.username, web_users.role
            FROM persons
            JOIN web_users ON web_users.person_id = persons.id
            WHERE persons.role = 'teachers'
              AND persons.project_id = ?
              AND web_users.project_id = ?
              AND web_users.is_active = 1
              AND web_users.role IN ('teacher', 'principal', 'cook', 'boss')
            ORDER BY web_users.role, persons.name
            """
            , (project_id, project_id)
        ).fetchall()
        connection_approvals = []
        permanent_user_options = ""
        permanent_group_options = ""
        if user["role"] == "boss":
            permanent_user_rows = conn.execute(
                """
                SELECT id, username, display_name, role, is_active
                FROM web_users
                WHERE id <> ?
                  AND project_id = ?
                ORDER BY is_active DESC, role, display_name COLLATE NOCASE, username COLLATE NOCASE
                """,
                (user["id"], project_id),
            ).fetchall()
            permanent_user_options = "".join(
                f'<option value="{row["id"]}">{html.escape(row["display_name"] or row["username"])} ({html.escape(ROLE_LABELS.get(row["role"], row["role"]))}){" - inactive" if not row["is_active"] else ""}</option>'
                for row in permanent_user_rows
            )
            permanent_group_options = "".join(
                f'<option value="{html.escape(class_name)}">{html.escape(class_name)}</option>'
                for class_name in get_classes(conn, user)
            )
            connection_order_map = {
                "status": """
                  CASE user_connection_approvals.status WHEN 'pending' THEN 0 WHEN 'rejected' THEN 1 ELSE 2 END,
                  user_connection_approvals.last_seen_at DESC,
                  user_connection_approvals.id DESC
                """,
                "user": """
                  LOWER(COALESCE(NULLIF(web_users.display_name, ''), web_users.username, '')) ASC,
                  user_connection_approvals.last_seen_at DESC,
                  user_connection_approvals.id DESC
                """,
                "ip": """
                  user_connection_approvals.ip_address ASC,
                  user_connection_approvals.last_seen_at DESC,
                  user_connection_approvals.id DESC
                """,
                "mac": """
                  user_connection_approvals.mac_address ASC,
                  user_connection_approvals.last_seen_at DESC,
                  user_connection_approvals.id DESC
                """,
                "device": """
                  LOWER(COALESCE(user_connection_approvals.device_name, '')) ASC,
                  user_connection_approvals.last_seen_at DESC,
                  user_connection_approvals.id DESC
                """,
            }
            connection_order_clause = connection_order_map[connection_sort]
            connection_approvals = conn.execute(
                f"""
                SELECT user_connection_approvals.*, web_users.display_name, web_users.username, web_users.role
                FROM user_connection_approvals
                JOIN web_users ON web_users.id = user_connection_approvals.user_id
                WHERE web_users.project_id = ?
                ORDER BY {connection_order_clause}
                LIMIT 120
                """
                , (project_id,)
            ).fetchall()

    location_panel = ""
    if user["role"] == "boss":
        location_rows = []
        for index, location in enumerate(location_policy.get("locations") or [], start=1):
            location_rows.append(
                f"""
                <tr>
                  <td>{index}</td>
                  <td>{html.escape(f"{location['latitude']:.6f}")}</td>
                  <td>{html.escape(f"{location['longitude']:.6f}")}</td>
                  <td>{html.escape(str(location['radius_meters']))}</td>
                  <td>{html.escape(location.get('updated_at') or '')}</td>
                  <td>
                    <form method="post" action="/mobile-location/update" onsubmit="return confirm('Supprimer ce lieu de travail ?')" style="display:inline">
                      <input type="hidden" name="action" value="delete">
                      <input type="hidden" name="location_id" value="{html.escape(str(location['id']))}">
                      <button class="btn red" type="submit">Supprimer</button>
                    </form>
                  </td>
                </tr>
                """
            )
        face_reset_options = []
        for person in face_reset_people:
            face_count = len(reference_face_paths_for_person(person["name"]))
            label_name = person["display_name"] or person["name"] or person["username"]
            face_reset_options.append(
                f'<option value="{person["id"]}">{html.escape(label_name)} ({html.escape(ROLE_LABELS.get(person["role"], person["role"]))}) - {face_count}/5 photos</option>'
            )
        face_reset_panel = f"""
      <div class="mobile-face-reset">
        <h4 class="mobile-section-title face">Réinscription visage</h4>
        <form method="post" action="/mobile-face/reset" onsubmit="return confirm('Autoriser cet employé à réenregistrer 5 photos du visage ?')">
          <div>
            <label>Employé</label>
            <select name="person_id" required>{''.join(face_reset_options) or '<option value="">Aucun employé</option>'}</select>
          </div>
          <button class="btn" type="submit" {"disabled" if not face_reset_options else ""}>Autoriser 5 nouvelles photos</button>
        </form>
      </div>
        """
        permanent_delete_panel = f"""
      <div class="mobile-permanent-delete" style="margin-top:14px">
        <h4 class="mobile-section-title danger">Suppression définitive</h4>
        <div class="alert warn">Action réservée au patron. Ces opérations ne passent pas par l'archive.</div>
        <div class="user-grid" style="margin-top:10px">
          <form method="post" action="/permanent-delete/user" onsubmit="return confirm('Supprimer définitivement les comptes sélectionnés ? Cette action est irréversible.')">
            <label>Compte utilisateur</label>
            <select name="user_id" multiple size="5" required>{permanent_user_options or '<option value="">Aucun compte</option>'}</select>
            <button class="btn red" type="submit" {"disabled" if not permanent_user_options else ""}>Supprimer définitivement compte</button>
          </form>
          <form method="post" action="/permanent-delete/group" onsubmit="return confirm('Supprimer définitivement les GROUPES sélectionnés de toutes les listes ? Les enfants seront conservés sans groupe.')">
            <label>Groupe</label>
            <select name="group_name" multiple size="5" required>{permanent_group_options or '<option value="">Aucun groupe</option>'}</select>
            <button class="btn red" type="submit" {"disabled" if not permanent_group_options else ""}>Supprimer définitivement groupe</button>
          </form>
        </div>
      </div>
        """
        connection_rows = []
        now_for_connections = now_text()
        for item in connection_approvals:
            status = item["status"]
            if status == "pending" and now_for_connections > item["expires_at"]:
                status = "expired"
            status_class = "present" if status == "approved" else ("warn" if status in {"pending", "expired"} else "absent")
            action_html = ""
            if status != "approved":
                action_html = f"""
                    <form method="post" action="/connection-approval/update" style="display:inline">
                      <input type="hidden" name="id" value="{item['id']}">
                      <input type="hidden" name="action" value="approve">
                      <button class="btn green" type="submit">Confirmer</button>
                    </form>
                """
            if status != "rejected":
                action_html += f"""
                    <form method="post" action="/connection-approval/update" style="display:inline">
                      <input type="hidden" name="id" value="{item['id']}">
                      <input type="hidden" name="action" value="reject">
                      <button class="btn red" type="submit">Refuser</button>
                    </form>
                """
            mac_text = item["mac_address"] or ""
            mac_short = mac_text if len(mac_text) <= 24 else mac_text[:24] + "..."
            connection_rows.append(
                f"""
                <tr>
                  <td>{html.escape(item['display_name'] or item['username'] or '')}</td>
                  <td>{html.escape(ROLE_LABELS.get(item['role'], item['role']))}</td>
                  <td>{html.escape(item['ip_address'])}</td>
                  <td><code title="{html.escape(mac_text)}">{html.escape(mac_short)}</code></td>
                  <td>{html.escape(item['device_name'] or '')}</td>
                  <td>{html.escape(item['first_seen_at'])}</td>
                  <td>{html.escape(item['last_seen_at'])}</td>
                  <td>{html.escape(item['expires_at'])}</td>
                  <td><span class="badge {status_class}">{html.escape(status)}</span></td>
                  <td class="nowrap">{action_html}</td>
                </tr>
                """
            )
        def connection_sort_link(sort_key, label):
            active_class = " sorted" if connection_sort == sort_key else ""
            return (
                f'<a class="connection-sort-link{active_class}" '
                f'href="/mobile-invitations?connection_sort={quote(sort_key)}#work-location">{html.escape(label)}</a>'
            )

        connection_panel = f"""
      <div class="mobile-connection-approval" style="margin-top:14px">
        <style>
          .connection-sort-link {{ color: inherit; font-weight: 700; text-decoration: none; }}
          .connection-sort-link:hover {{ text-decoration: underline; }}
          .connection-sort-link.sorted::after {{ content: " ^"; font-size: 10px; }}
        </style>
        <h4 class="mobile-section-title connections">Historique connexions</h4>
        <div class="muted small">Le navigateur ne fournit pas la vraie adresse MAC; la colonne MAC contient l'identifiant sécurisé de l'appareil. Chaque utilisateur peut avoir plusieurs IP/appareils.</div>
        <div class="table-wrap" style="margin-top:8px;max-height:300px;overflow:auto">
          <table>
            <thead><tr><th>{connection_sort_link("user", "Utilisateur")}</th><th>Role</th><th>{connection_sort_link("ip", "IP")}</th><th>{connection_sort_link("mac", "MAC / appareil")}</th><th>{connection_sort_link("device", "Appareil")}</th><th>Premier</th><th>Dernier</th><th>Expire</th><th>Statut</th><th>Action</th></tr></thead>
            <tbody>{''.join(connection_rows) or '<tr><td colspan="10" class="muted">Aucune connexion.</td></tr>'}</tbody>
          </table>
        </div>
      </div>
        """
        location_panel = f"""
    <div class="panel" id="work-location" style="margin-top:16px">
      <h3 class="mobile-section-title location">Lieu de travail mobile</h3>
      <div class="muted">Les présences mobiles des éducatrices sont acceptées dans le rayon de n'importe quel lieu configuré.</div>
      {f'<div class="alert info" style="margin-top:12px">Logo enregistré.</div>' if query.get('logo', [''])[0] == 'updated' else ''}
      {f'<div class="alert error" style="margin-top:12px">{html.escape(query.get("logo_error", [""])[0])}</div>' if query.get('logo_error', [''])[0] else ''}
      <div class="project-logo-settings">
        {f'<img class="project-logo-preview" src="{html.escape(logo_url, quote=True)}" alt="Logo de la garderie">' if logo_url else '<div class="project-logo-placeholder" aria-hidden="true">LOGO</div>'}
        <form method="post" action="/project-logo/upload" enctype="multipart/form-data" class="project-logo-form">
          <div><label for="project-logo-file">Logo de la garderie</label><input id="project-logo-file" name="logo" type="file" accept="image/png,image/jpeg,image/webp,image/gif" required><div class="muted small">PNG, JPG, WEBP ou GIF · 5 Mo max. L'image sera recadrée pour remplir le cercle.</div></div>
          <button class="btn primary" type="submit">Téléverser le logo</button>
        </form>
      </div>
      <div class="table-wrap" style="margin-top:10px">
        <table>
          <thead><tr><th>#</th><th>Latitude</th><th>Longitude</th><th>Rayon metres</th><th>Mis à jour</th><th>Action</th></tr></thead>
          <tbody>{''.join(location_rows) or '<tr><td colspan="6" class="muted">Aucun lieu configuré.</td></tr>'}</tbody>
        </table>
      </div>
      <form method="post" action="/mobile-location/update" class="user-grid" style="margin-top:12px">
        <input type="hidden" name="action" value="add">
        <div><label>Latitude</label><input id="mobile-location-lat" name="latitude" required></div>
        <div><label>Longitude</label><input id="mobile-location-lon" name="longitude" required></div>
        <div><label>Rayon metres</label><input name="radius_meters" type="number" min="20" max="1000" value="{html.escape(str(location_policy.get('radius_meters') or 100))}"></div>
        <div style="display:flex;align-items:end;gap:8px;flex-wrap:wrap">
          <button class="btn" type="submit">Ajouter</button>
          <button class="btn" type="button" id="use-browser-location">Position actuelle</button>
        </div>
      </form>
      {face_reset_panel}
      {permanent_delete_panel}
      {connection_panel}
    </div>
        """

    body = f"""
    <style>
      .mobile-section-title.location {{ color: #f05a28; }}
      .mobile-section-title.face {{ color: #9333ea; }}
      .mobile-section-title.connections {{ color: #b45309; }}
      .mobile-section-title.danger {{ color: #b91c1c; }}
      .project-logo-settings {{ display:flex; align-items:center; gap:14px; margin-top:14px; padding:14px; border:1px solid #d8e2e9; border-radius:10px; background:#f8fbfc; }}
      .project-logo-preview, .project-logo-placeholder {{ width:76px; height:76px; flex:0 0 76px; border-radius:50%; border:2px solid #fff; box-shadow:0 2px 10px rgba(16,55,82,.18); background:#e6eef3; }}
      .project-logo-preview {{ display:block; object-fit:cover; }}
      .project-logo-placeholder {{ display:grid; place-items:center; color:#6b7d88; font-size:12px; font-weight:800; }}
      .project-logo-form {{ display:flex; align-items:end; gap:10px; flex:1; flex-wrap:wrap; }}
      .project-logo-form > div {{ flex:1 1 260px; }}
      @media (max-width:640px) {{ .project-logo-settings {{ align-items:flex-start; }} .project-logo-preview, .project-logo-placeholder {{ width:58px; height:58px; flex-basis:58px; }} .project-logo-form .btn {{ width:100%; }} }}
    </style>
    {location_panel}
    <script>
    (function() {{
      const locationButton = document.getElementById('use-browser-location');
      if (locationButton && navigator.geolocation) {{
        locationButton.addEventListener('click', function() {{
          navigator.geolocation.getCurrentPosition(function(position) {{
            document.getElementById('mobile-location-lat').value = position.coords.latitude.toFixed(6);
            document.getElementById('mobile-location-lon').value = position.coords.longitude.toFixed(6);
          }});
        }});
      }}
    }})();
    </script>
    """
    return html_page("Lieu travail mobile", user, body)


def render_child_edit(user, child_id):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to edit children.</div>')
    with connect_db() as conn:
        child = conn.execute(
            "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
            (child_id, effective_project_id(conn, user)),
        ).fetchone()
        if not child:
            return html_page("Not Found", user, '<div class="panel">Child not found.</div>')
        classes = get_classes(conn, user)
    body = f"""
    <div class="panel">
      <h2>Edit Child</h2>
      <form method="post" action="/children/update" class="user-grid">
        <input type="hidden" name="id" value="{child['id']}">
        <div><label>Name</label><input name="name" value="{html.escape(child['name'])}" required></div>
        <div><label>Groupe</label>
          <select name="class_name">
            {''.join(f'<option value="{html.escape(cls)}" {"selected" if cls == (child["class_name"] or "") else ""}>{html.escape(cls)}</option>' for cls in classes)}
          </select>
        </div>
        <div><label>Photo path</label><input name="photo_path" value="{html.escape(child['photo_path'] or '')}"></div>
        <div><label>Created at</label><input value="{html.escape(child['created_at'])}" disabled></div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Enregistrer</button></div>
      </form>
    </div>
    """
    return html_page(f"Edit {child['name']}", user, body)


def render_user_edit(user, target_id):
    with connect_db() as conn:
        target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_id,)).fetchone()
        if not target:
            return html_page("Not Found", user, '<div class="panel">User not found.</div>')
        self_edit = user["role"] == "principal" and target["id"] == user["id"]
        can_manage_target = can_manage_users(user, target)
        can_reset_password = can_reset_user_password(user, target)
        password_only = can_reset_password and not can_manage_target and not self_edit
        if not can_manage_target and not self_edit and not can_reset_password:
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to edit this user.</div>')
        username_value = str(target["username"] or "")
        display_name_value = str(target["display_name"] or "")
        role_value = str(target["role"] or "")
        person_id_value = str(target["person_id"] or "")
        classes = get_classes(conn, user)
        selected = set(safe_json_list(target["allowed_classes_json"]))
        child_group_options = ""
        child_group = ""
        if target["role"] == "children":
            if target["person_id"]:
                child_person = conn.execute(
                    "SELECT id, name, class_name, photo_path FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                    (target["person_id"], effective_project_id(conn, user)),
                ).fetchone()
                child_group = (child_person["class_name"] if child_person else "") or ""
            child_group_options = "".join(
                f'<option value="{html.escape(cls)}" {"selected" if cls == child_group else ""}>{html.escape(cls)}</option>'
                for cls in classes
            )
            child_name_value = html.escape((child_person["name"] if child_person else display_name_value))
            child_photo_value = html.escape((child_person["photo_path"] if child_person else ""))
            child_person_id_value = html.escape(person_id_value)
            child_password_html = ""
            if can_reset_password:
                child_password_html = f"""
    <div class="panel" style="margin-top:16px">
      <h3>Reset password</h3>
      <form method="post" action="/users/update" class="grid" style="gap:12px;max-width:520px">
        <input type="hidden" name="id" value="{target['id']}">
        <input type="hidden" name="password_reset_only" value="1">
        <div><label>New password</label><input name="password" type="password" minlength="8" autocomplete="new-password" required></div>
        <div><label>Confirm password</label><input name="password_confirm" type="password" minlength="8" autocomplete="new-password" required></div>
        <div><button class="btn primary" type="submit">Enregistrer le mot de passe</button></div>
      </form>
    </div>
                """
            body = f"""
    <div class="panel">
      <h2>Edit User</h2>
      <div class="muted small" style="margin-bottom:10px">Only the child group is editable here.</div>
      <form method="post" action="/children/update" class="user-grid">
        <input type="hidden" name="return_to" value="/account">
        <input type="hidden" name="id" value="{child_person_id_value}">
        <input type="hidden" name="name" value="{child_name_value}">
        <input type="hidden" name="photo_path" value="{child_photo_value}">
        <div><label>Groupe</label>
          <select name="class_name">
            {child_group_options}
          </select>
        </div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Enregistrer</button></div>
      </form>
    </div>
    {child_password_html}
    """
            return html_page(f"Edit {username_value}", user, body)
        checks = "".join(
            f'<label style="display:inline-flex;gap:6px;align-items:center;margin-right:12px"><input type="checkbox" name="classes" value="{html.escape(cls)}" {"checked" if cls in selected else ""}>{html.escape(cls)}</label>'
            for cls in classes
        )
        child_group_html = ""
        if target["role"] == "children":
            child_group_disabled = "disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit or password_only else ""
            if not child_group_options:
                child_group_options = "".join(
                    f'<option value="{html.escape(cls)}" {"selected" if cls == child_group else ""}>{html.escape(cls)}</option>'
                    for cls in classes
                )
            child_group_html = f"""
        <div><label>Groupe</label>
          <select name="class_name" {child_group_disabled}>
            {child_group_options}
          </select>
        </div>
        """
        role_options = editable_roles_for_user(user, target)
        if target["role"] not in role_options:
            role_options = [target["role"]] + role_options
        locked_attrs = "readonly disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit or password_only else "required"
        select_locked_attrs = "disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit or password_only else ""
        password_html = f'<div id="password-reset"><label>Reset password</label><input name="password" type="password" autocomplete="new-password" placeholder="Leave blank to keep current" {"required" if self_edit or password_only else ""}></div><div><label>Confirm password</label><input name="password_confirm" type="password" autocomplete="new-password" placeholder="Enter the same password again" {"required" if self_edit or password_only else ""}></div>' if can_reset_password else ""
        body = f"""
    <div class="panel">
      <h2>Edit User</h2>
      {f'<div class="muted small" style="margin-bottom:10px">You can only change your password here.</div>' if self_edit else ''}
      {f'<div class="muted small" style="margin-bottom:10px">You can reset this user password here.</div>' if password_only else ''}
      <form method="post" action="/users/update" class="user-grid">
        <input type="hidden" name="id" value="{target['id']}">
        <div><label>Username</label><input name="username" value="{html.escape(username_value)}" {locked_attrs}></div>
        <div><label>Display name</label><input name="display_name" value="{html.escape(display_name_value)}" {locked_attrs}></div>
        <div><label>Role</label>
          <select name="role" {select_locked_attrs}>
            {''.join(f'<option value="{role}" {"selected" if role == role_value else ""}>{ROLE_LABELS.get(role, role)}</option>' for role in role_options)}
          </select>
        </div>
        <div><label>Linked person ID</label><input name="person_id" value="{html.escape(person_id_value)}" placeholder="Optional teacher/child person id" {"readonly disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit else ""}></div>
        {child_group_html}
        {password_html}
        <div><label>Classes</label><div class="muted-box">{"<span class=\"muted\">Locked for your account.</span>" if self_edit else (checks or '<span class=\"muted\">No classes configured.</span>')}</div></div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Enregistrer</button></div>
      </form>
    </div>
    """
    return html_page(f"Edit {username_value}", user, body)


def render_audit(user, query):
    if user["role"] != "boss":
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view logs.</div>')
    sort_key = query.get("sort", ["time"])[0].strip().lower()
    if sort_key not in {"time", "actor", "device", "ip", "action", "type", "object", "details"}:
        sort_key = "time"
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT audit_log.*, COALESCE(web_users.username, '') AS actor_username, COALESCE(web_users.display_name, '') AS actor_name
            FROM audit_log
            LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
            """
        ).fetchall()
    def audit_sort_value(row):
        try:
          details = json.loads(row["details_json"] or "{}")
        except json.JSONDecodeError:
          details = {}
        actor = row["actor_name"] or row["actor_username"] or ""
        device = details.get("device_name", "") or ""
        ip_address = row["ip_address"] or ""
        object_id = row["object_id"] or ""
        details_json = row["details_json"] or ""
        if sort_key == "time":
            return (0, -int(row["id"]))
        if sort_key == "actor":
            return (1 if not actor else 0, actor.lower(), -int(row["id"]))
        if sort_key == "device":
            return (1 if not device else 0, device.lower(), -int(row["id"]))
        if sort_key == "ip":
            return (1 if not ip_address else 0, ip_address.lower(), -int(row["id"]))
        if sort_key == "action":
            return (0, (row["action"] or "").lower(), -int(row["id"]))
        if sort_key == "type":
            return (0, (row["object_type"] or "").lower(), -int(row["id"]))
        if sort_key == "object":
            return (1 if not object_id else 0, object_id.lower(), -int(row["id"]))
        return (1 if not details_json else 0, details_json.lower(), -int(row["id"]))
    rows = sorted(rows, key=audit_sort_value)[:200]
    body_rows = []
    for r in rows:
        try:
            details = json.loads(r["details_json"] or "{}")
        except json.JSONDecodeError:
            details = {}
        device_name = details.get("device_name", "")
        body_rows.append(
            f"<tr><td>{html.escape(r['created_at'])}</td>"
            f"<td>{html.escape(r['actor_name'] or r['actor_username'] or '')}</td>"
            f"<td>{html.escape(device_name)}</td>"
            f"<td>{html.escape(r['ip_address'] or '')}</td>"
            f"<td>{html.escape(r['action'])}</td>"
            f"<td>{html.escape(r['object_type'])}</td>"
            f"<td>{html.escape(r['object_id'] or '')}</td>"
            f"<td><code>{html.escape(r['details_json'])}</code></td></tr>"
        )
    def sort_link(label, key):
        return f'<a href="/audit?sort={html.escape(key)}">{label}</a>'
    body = f"""
    <style>
      .audit-floating-panel {{ position: sticky; top: 74px; z-index: 5; }}
      .audit-floating-panel .table-wrap {{ max-height: calc(100vh - 190px); overflow: auto; }}
      .audit-floating-panel thead th {{ position: sticky; top: 0; z-index: 2; }}
      @media (max-width: 720px) {{
        .audit-floating-panel {{ position: static; }}
        .audit-floating-panel .table-wrap {{ max-height: none; }}
      }}
    </style>
    <div class="panel audit-floating-panel">
      <h2>Journaux</h2>
      <div class="table-wrap">
        <table>
          <thead><tr><th class="sortable-head">{sort_link("Time", "time")}</th><th class="sortable-head">{sort_link("Actor", "actor")}</th><th class="sortable-head">{sort_link("Device", "device")}</th><th class="sortable-head">{sort_link("IP Address", "ip")}</th><th class="sortable-head">{sort_link("Action", "action")}</th><th class="sortable-head">{sort_link("Type", "type")}</th><th class="sortable-head">{sort_link("Object", "object")}</th><th class="sortable-head">{sort_link("Details", "details")}</th></tr></thead>
          <tbody>{''.join(body_rows) or '<tr><td colspan=\"8\" class=\"muted\">No logs yet</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Journaux", user, body)


def render_deleted_user_archive(user, query):
    if user["role"] != "boss":
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to view deleted user archives.</div>')
    selected_user_id = query.get("user_id", [""])[0].strip()
    with connect_db() as conn:
        archive_rows = conn.execute(
            """
            SELECT *
            FROM deleted_user_archives
            ORDER BY deleted_at DESC, id DESC
            """
        ).fetchall()
        selected_archive = None
        if selected_user_id.isdigit():
            selected_archive = conn.execute(
                "SELECT * FROM deleted_user_archives WHERE user_id = ?",
                (int(selected_user_id),),
            ).fetchone()
        if not selected_archive and archive_rows:
            selected_archive = archive_rows[0]

        def related_counts(target_user_id):
            return {
                "audit": conn.execute(
                    """
                    SELECT COUNT(*)
                    FROM audit_log
                    WHERE actor_user_id = ?
                       OR (object_type = 'user' AND object_id = ?)
                       OR details_json LIKE ?
                    """,
                    (target_user_id, str(target_user_id), f'%"user_id": {target_user_id}%'),
                ).fetchone()[0],
                "files": conn.execute(
                    """
                    SELECT COUNT(*)
                    FROM user_files
                    WHERE owner_user_id = ? OR uploader_user_id = ?
                    """,
                    (target_user_id, target_user_id),
                ).fetchone()[0],
                "messages": conn.execute(
                    """
                    SELECT COUNT(*)
                    FROM internal_messages
                    WHERE sender_user_id = ? OR recipient_user_id = ?
                    """,
                    (target_user_id, target_user_id),
                ).fetchone()[0],
                "devices": conn.execute(
                    "SELECT COUNT(*) FROM mobile_devices WHERE user_id = ?",
                    (target_user_id,),
                ).fetchone()[0],
            }

        archive_rows_html = []
        for row in archive_rows:
            counts = related_counts(row["user_id"])
            archive_rows_html.append(
                f"""
                <tr>
                  <td><a href="/deleted-users?user_id={row['user_id']}">{html.escape(row['username'])}</a></td>
                  <td>{html.escape(row['display_name'])}</td>
                  <td>{html.escape(ROLE_LABELS.get(row['role'], row['role']))}</td>
                  <td>{html.escape(str(row['person_id'] or ''))}</td>
                  <td>{html.escape(row['deleted_at'])}</td>
                  <td>{html.escape(row['deleted_by_username'] or row['deleted_by_display_name'] or '')}</td>
                  <td>{counts['audit']}</td>
                  <td>{counts['files']}</td>
                  <td>{counts['messages']}</td>
                  <td>{counts['devices']}</td>
                </tr>
                """
            )

        related_rows_html = ""
        archive_detail_html = '<div class="muted">Select a deleted user to view related records.</div>'
        if selected_archive:
            target_user_id = int(selected_archive["user_id"])
            audit_rows = conn.execute(
                """
                SELECT audit_log.*, COALESCE(actor.display_name, actor.username, 'System') AS actor_name
                FROM audit_log
                LEFT JOIN web_users AS actor ON actor.id = audit_log.actor_user_id
                WHERE audit_log.actor_user_id = ?
                   OR (audit_log.object_type = 'user' AND audit_log.object_id = ?)
                   OR audit_log.details_json LIKE ?
                ORDER BY audit_log.created_at DESC, audit_log.id DESC
                LIMIT 200
                """,
                (target_user_id, str(target_user_id), f'%"user_id": {target_user_id}%'),
            ).fetchall()
            archive_counts = related_counts(target_user_id)
            related_rows_html = "".join(
                f"<tr><td>{html.escape(r['created_at'])}</td><td>{html.escape(r['actor_name'] or '')}</td><td>{html.escape(r['action'])}</td><td>{html.escape(r['object_type'])}</td><td>{html.escape(r['object_id'] or '')}</td><td><code>{html.escape(r['details_json'])}</code></td></tr>"
                for r in audit_rows
            )
            archive_detail_html = f"""
            <div class="panel">
              <h3>Archive detail</h3>
              <div class="stats" style="grid-template-columns:repeat(auto-fit,minmax(160px,220px))">
                <div class="stat"><div class="muted">Audit logs</div><div class="value">{archive_counts['audit']}</div></div>
                <div class="stat"><div class="muted">Files</div><div class="value">{archive_counts['files']}</div></div>
                <div class="stat"><div class="muted">Messages</div><div class="value">{archive_counts['messages']}</div></div>
                <div class="stat"><div class="muted">Devices</div><div class="value">{archive_counts['devices']}</div></div>
              </div>
              <div class="table-wrap">
                <table>
                  <thead><tr><th>When</th><th>Actor</th><th>Action</th><th>Type</th><th>Object</th><th>Details</th></tr></thead>
                  <tbody>{related_rows_html or '<tr><td colspan="6" class="muted">No related audit rows.</td></tr>'}</tbody>
                </table>
              </div>
            </div>
            """

    body = f"""
    <style>
      .archive-layout {{ display:grid; grid-template-columns:minmax(0, 1.05fr) minmax(0, 1.4fr); gap:16px; align-items:start; }}
      .archive-summary .table-wrap {{ max-height: 64vh; overflow:auto; }}
      .archive-summary thead th {{ position: sticky; top: 0; z-index: 1; }}
      .archive-summary a {{ color: inherit; font-weight: 700; }}
      @media (max-width: 1180px) {{
        .archive-layout {{ grid-template-columns:1fr; }}
      }}
    </style>
    <div class="panel">
      <h2>Deleted users archive</h2>
      <div class="muted">Boss only. Deleted accounts stay in the archive, and their history remains available here.</div>
    </div>
    <div class="archive-layout" style="margin-top:16px">
      <div class="panel archive-summary">
        <h3>Archived accounts</h3>
        <div class="table-wrap">
          <table>
            <thead><tr><th>Username</th><th>Name</th><th>Role</th><th>Person ID</th><th>Deleted at</th><th>Deleted by</th><th>Audit</th><th>Files</th><th>Messages</th><th>Devices</th></tr></thead>
            <tbody>{''.join(archive_rows_html) or '<tr><td colspan="10" class="muted">No deleted users yet.</td></tr>'}</tbody>
          </table>
        </div>
      </div>
      <div>
        {archive_detail_html}
      </div>
    </div>
    """
    return html_page("Deleted users archive", user, body)


def redirect(handler, location, extra_headers=None):
    handler.send_response(302)
    handler.send_header("Location", location)
    if extra_headers:
        for key, value in extra_headers.items():
            if isinstance(value, (list, tuple)):
                for item in value:
                    handler.send_header(key, item)
            else:
                handler.send_header(key, value)
    handler.end_headers()


def parse_post_data(handler):
    length = int(handler.headers.get("Content-Length", "0") or 0)
    raw = handler.rfile.read(length).decode("utf-8")
    return parse_qs(raw, keep_blank_values=True)


def parse_json_post_data(handler, max_bytes=64 * 1024):
    length = int(handler.headers.get("Content-Length", "0") or 0)
    if length <= 0 or length > max_bytes:
        raise ValueError("Invalid request size")
    raw = handler.rfile.read(length).decode("utf-8")
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError("JSON body must be an object")
    return data


def safe_json_list(value, default=None):
    if default is None:
        default = []
    if value is None:
        return list(default)
    if isinstance(value, (list, tuple)):
        return [str(item) for item in value if str(item).strip()]
    try:
        parsed = json.loads(value or "[]")
    except (TypeError, ValueError, json.JSONDecodeError):
        return list(default)
    if not isinstance(parsed, list):
        return list(default)
    return [str(item) for item in parsed if str(item).strip()]


def desktop_sync_authorized(handler):
    expected = configured_desktop_sync_token()
    supplied = handler.headers.get("X-TimeRecord-Token", "").strip()
    return bool(expected and supplied and hmac.compare_digest(expected, supplied))


def json_response(handler, payload, status=200, extra_headers=None):
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Content-Length", str(len(body)))
    if extra_headers:
        for key, value in extra_headers.items():
            if isinstance(value, (list, tuple)):
                for item in value:
                    handler.send_header(key, item)
            else:
                handler.send_header(key, value)
    handler.end_headers()
    handler.wfile.write(body)


def sync_desktop_attendance(payload, ip_address=None):
    name = str(payload.get("name", "")).strip()
    role = str(payload.get("role", "")).strip()
    event_type = str(payload.get("event_type", "")).strip()
    timestamp = str(payload.get("timestamp", "")).strip()
    source = str(payload.get("source", "desktop")).strip() or "desktop"
    operator_name = str(payload.get("operator_name", "")).strip() or name
    remote_person_id = payload.get("person_id")

    if not name or role not in {"children", "teachers"} or event_type not in {"checkin", "checkout"}:
        raise ValueError("Invalid attendance payload")
    try:
        timestamp = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S").strftime("%Y-%m-%d %H:%M:%S")
    except ValueError as exc:
        raise ValueError("Invalid timestamp") from exc

    with connect_db() as conn:
        person = None
        if isinstance(remote_person_id, int) or (isinstance(remote_person_id, str) and remote_person_id.isdigit()):
            person = conn.execute(
                "SELECT * FROM persons WHERE id = ? AND role = ? AND lower(name) = lower(?)",
                (int(remote_person_id), role, name),
            ).fetchone()
        if not person:
            person = conn.execute(
                "SELECT * FROM persons WHERE lower(name) = lower(?) AND role = ? ORDER BY id LIMIT 1",
                (name, role),
            ).fetchone()
        if not person:
            conn.execute(
                """
                INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at)
                VALUES (?, ?, '', '', ?, ?)
                """,
                (name, role, f"CHILD:{name}" if role == "children" else None, now_text()),
            )
            person_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
        else:
            person_id = person["id"]

        duplicate = conn.execute(
            """
            SELECT id FROM attendance
            WHERE (person_id = ? OR lower(name) = lower(?)) AND role = ? AND event_type = ? AND timestamp = ?
            LIMIT 1
            """,
            (person_id, name, role, event_type, timestamp),
        ).fetchone()
        if duplicate:
            conn.commit()
            return {"ok": True, "duplicate": True, "attendance_id": duplicate["id"], "person_id": person_id}

        conn.execute(
            """
            INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path)
            VALUES (?, ?, ?, ?, ?, NULL)
            """,
            (person_id, name, role, event_type, timestamp),
        )
        attendance_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
        audit(
            conn,
            None,
            "desktop_attendance_sync",
            "attendance",
            object_id=person_id,
            details={"person_id": person_id, "name": name, "role": role, "event_type": event_type, "timestamp": timestamp, "source": source, "operator_name": operator_name, "device_name": "Desktop Sync"},
            ip_address=ip_address,
        )
        conn.commit()
    return {"ok": True, "duplicate": False, "attendance_id": attendance_id, "person_id": person_id}


def desktop_attendance_payload(query):
    date_text = query.get("date", [today_text()])[0]
    try:
        date_text = datetime.strptime(date_text, "%Y-%m-%d").strftime("%Y-%m-%d")
    except ValueError:
        raise ValueError("Invalid date")
    limit_text = query.get("limit", ["500"])[0]
    try:
        limit = max(1, min(int(limit_text), 2000))
    except ValueError as exc:
        raise ValueError("Invalid limit") from exc
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT attendance.id, attendance.person_id, attendance.name, attendance.role,
                   attendance.event_type, attendance.timestamp, COALESCE(persons.class_name, '') AS class_name,
                   CASE
                     WHEN COALESCE((
                       SELECT audit_log.details_json
                       FROM audit_log
                       WHERE audit_log.object_type = 'attendance'
                         AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                         AND (
                           audit_log.action LIKE '%' || attendance.event_type
                           OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                         )
                         AND (
                           audit_log.created_at <= attendance.timestamp
                           OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                         )
                       ORDER BY audit_log.created_at DESC, audit_log.id DESC
                       LIMIT 1
                     ), '') LIKE '%"source": "desktop"%'
                     THEN 'desktop'
                     ELSE 'system'
                   END AS source,
                   COALESCE((
                     SELECT
                       CASE
                         WHEN audit_log.details_json LIKE '%"source": "desktop"%'
                         THEN attendance.name
                         ELSE COALESCE(NULLIF(web_users.display_name, ''), NULLIF(web_users.username, ''), 'System')
                       END
                     FROM audit_log
                     LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                     WHERE audit_log.object_type = 'attendance'
                       AND (audit_log.object_id = attendance.person_id OR audit_log.object_id = attendance.id)
                       AND (
                         audit_log.action LIKE '%' || attendance.event_type
                         OR audit_log.details_json LIKE '%"event_type": "' || attendance.event_type || '"%'
                       )
                       AND (
                         audit_log.created_at <= attendance.timestamp
                         OR audit_log.details_json LIKE '%' || attendance.timestamp || '%'
                       )
                     ORDER BY audit_log.created_at DESC, audit_log.id DESC
                     LIMIT 1
                   ), 'System') AS operator_name
            FROM attendance
            LEFT JOIN persons ON persons.id = attendance.person_id
            WHERE attendance.timestamp LIKE ?
            ORDER BY attendance.id DESC
            LIMIT ?
            """,
            (f"{date_text}%", limit),
        ).fetchall()
    records = [
        {
            "id": row["id"],
            "person_id": row["person_id"],
            "name": row["name"],
            "role": row["role"],
            "event_type": row["event_type"],
            "timestamp": row["timestamp"],
            "class_name": row["class_name"],
            "source": row["source"],
            "operator_name": row["operator_name"],
        }
        for row in rows
    ]
    return {"ok": True, "date": date_text, "records": records}


def get_session_user(handler):
    cookie = parse_cookie(handler.headers.get("Cookie"))
    token = cookie.get("session")
    if not token:
        return None
    token_value = token.value
    with connect_db() as conn:
        row = conn.execute(
            """
            SELECT web_users.*
            FROM sessions
            JOIN web_users ON web_users.id = sessions.user_id
            WHERE sessions.token = ? AND sessions.expires_at > ?
            """,
            (token_value, now_text()),
        ).fetchone()
        if not row:
            return None
        user = dict(row)
        person_project_id = linked_person_project_id(conn, user)
        if person_project_id and person_project_id != user_project_id(user):
            user["project_id"] = person_project_id
            conn.execute(
                "UPDATE web_users SET project_id = ?, updated_at = ? WHERE id = ?",
                (person_project_id, now_text(), user["id"]),
            )
            conn.commit()
        user["_home_project_id"] = int(user.get("project_id") or 1)
        if is_super_admin(user):
            project_cookie = cookie.get(PROJECT_CONTEXT_COOKIE)
            if project_cookie and str(project_cookie.value).isdigit():
                project_id = int(project_cookie.value)
                project = conn.execute(
                    "SELECT id FROM projects WHERE id = ? AND status <> 'deleted'",
                    (project_id,),
                ).fetchone()
                if project:
                    user["project_id"] = project["id"]
            user["_super_admin"] = True
        return user


def create_session(conn, user_id):
    token = secrets.token_urlsafe(32)
    expires_at = (datetime.now() + timedelta(days=SESSION_TTL_DAYS)).strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "INSERT INTO sessions(token, user_id, expires_at, created_at) VALUES (?, ?, ?, ?)",
        (token, user_id, expires_at, now_text()),
    )
    return token


def delete_session(conn, token):
    conn.execute("DELETE FROM sessions WHERE token = ?", (token,))


def configured_public_url():
    settings = load_settings()
    return (
        os.environ.get(PUBLIC_URL_ENV, "").strip().rstrip("/")
        or setting_text(settings, "public_url").rstrip("/")
        or setting_text(settings, "webapp_url").rstrip("/")
    )


def configured_privacy_contact():
    settings = load_settings()
    contact_name = os.environ.get(PRIVACY_CONTACT_ENV, "").strip() or setting_text(settings, "privacy_contact")
    contact_email = os.environ.get(PRIVACY_EMAIL_ENV, "").strip() or setting_text(settings, "privacy_email")
    return contact_name, contact_email


def request_base_url(handler):
    public_url = configured_public_url()
    if public_url:
        return public_url
    proto = handler.headers.get("X-Forwarded-Proto", "").split(",", 1)[0].strip()
    if not proto:
        proto = "https" if handler.headers.get("X-Forwarded-Ssl", "").lower() == "on" else "http"
    host = handler.headers.get("X-Forwarded-Host", "").split(",", 1)[0].strip() or handler.headers.get("Host", "").strip()
    return f"{proto}://{host}" if host else ""


def mobile_invite_url(handler, token):
    base = request_base_url(handler)
    return f"{base}/invite/accept?token={quote(token)}" if base else f"/invite/accept?token={quote(token)}"


def display_invite_url(token):
    base = configured_public_url() or "https://pititpas.com"
    return f"{base}/invite/accept?token={quote(token)}"


def setting_text(settings, key):
    value = settings.get(key, "")
    return value.strip() if isinstance(value, str) else ""


def smtp_config():
    settings = load_settings()
    host = os.environ.get(SMTP_HOST_ENV, "").strip() or setting_text(settings, "smtp_host")
    username = os.environ.get(SMTP_USERNAME_ENV, "").strip() or setting_text(settings, "smtp_username")
    password = os.environ.get(SMTP_PASSWORD_ENV, "") or setting_text(settings, "smtp_password")
    from_address = os.environ.get(SMTP_FROM_ENV, "").strip() or setting_text(settings, "smtp_from") or username
    if not host or not from_address:
        return None
    try:
        port = int(os.environ.get(SMTP_PORT_ENV, "").strip() or setting_text(settings, "smtp_port") or "587")
    except ValueError:
        port = 587
    tls_value = (os.environ.get(SMTP_TLS_ENV, "").strip() or setting_text(settings, "smtp_tls") or "1").lower()
    return {
        "host": host,
        "port": port,
        "username": username,
        "password": password,
        "from_address": from_address,
        "use_tls": tls_value not in {"0", "false", "no", "off"},
    }


def email_provider():
    settings = load_settings()
    provider = (os.environ.get(EMAIL_PROVIDER_ENV, "").strip() or setting_text(settings, "email_provider") or "smtp").lower()
    return provider if provider in {"smtp", "ses"} else "smtp"


def ses_config():
    settings = load_settings()
    from_address = (
        os.environ.get(SES_FROM_ENV, "").strip()
        or setting_text(settings, "ses_from")
        or os.environ.get(SMTP_FROM_ENV, "").strip()
        or setting_text(settings, "smtp_from")
    )
    region = (
        os.environ.get(SES_REGION_ENV, "").strip()
        or setting_text(settings, "ses_region")
        or os.environ.get("AWS_DEFAULT_REGION", "").strip()
        or os.environ.get("AWS_REGION", "").strip()
    )
    if not from_address or not region:
        return None
    return {"from_address": from_address, "region": region}


def email_config():
    return ses_config() if email_provider() == "ses" else smtp_config()


def email_configured():
    return bool(email_config())


def send_smtp_email(to_address, subject, body):
    config = smtp_config()
    if not config:
        raise RuntimeError("SMTP is not configured")
    message = EmailMessage()
    message["From"] = config["from_address"]
    message["To"] = to_address
    message["Subject"] = subject
    message.set_content(body)
    with smtplib.SMTP(config["host"], config["port"], timeout=20) as smtp:
        smtp.ehlo()
        if config["use_tls"]:
            smtp.starttls()
            smtp.ehlo()
        if config["username"]:
            smtp.login(config["username"], config["password"])
        smtp.send_message(message)


def send_ses_email(to_address, subject, body):
    config = ses_config()
    if not config:
        raise RuntimeError("Amazon SES API is not configured")
    try:
        import boto3
    except ImportError as exc:
        raise RuntimeError("boto3 is not installed. Run: pip install boto3") from exc
    client = boto3.client("ses", region_name=config["region"])
    client.send_email(
        Source=config["from_address"],
        Destination={"ToAddresses": [to_address]},
        Message={
            "Subject": {"Data": subject, "Charset": "UTF-8"},
            "Body": {"Text": {"Data": body, "Charset": "UTF-8"}},
        },
    )


def send_email(to_address, subject, body):
    if email_provider() == "ses":
        send_ses_email(to_address, subject, body)
        return
    send_smtp_email(to_address, subject, body)


def send_mobile_invitation_email(to_address, person_name, invite_url, expires_at):
    subject = "Invitation mobile - PITIT PAS SYSTEM"
    body = f"""Bonjour,

Vous avez reçu une invitation pour créer votre compte mobile PITIT PAS SYSTEM.

Nom: {person_name}
Lien d'inscription:
{invite_url}

Ce lien expire le {expires_at}.

Si vous n'avez pas demandé cette invitation, ignorez ce message.
"""
    send_email(to_address, subject, body)


def deliver_mobile_invitation_email(conn, handler, actor, token):
    invitation = invitation_row(conn, token)
    if not invitation:
        return {"configured": email_configured(), "sent": False, "error": "Invitation not found"}
    if not email_configured():
        provider_label = "Amazon SES API" if email_provider() == "ses" else "SMTP"
        error_message = f"{provider_label} is not configured"
        conn.execute(
            "UPDATE mobile_invitations SET email_error = ? WHERE id = ?",
            (error_message, invitation["id"]),
        )
        return {"configured": False, "sent": False, "error": error_message}
    invite_url = mobile_invite_url(handler, token)
    try:
        send_mobile_invitation_email(invitation["email"], invitation["person_name"], invite_url, invitation["expires_at"])
    except Exception as exc:
        error = str(exc)[:500]
        conn.execute(
            "UPDATE mobile_invitations SET email_error = ? WHERE id = ?",
            (error, invitation["id"]),
        )
        audit_request(
            handler,
            conn,
            actor["id"] if actor else None,
            "send_mobile_invitation_email_failed",
            "mobile_invitation",
            object_id=invitation["id"],
            details={"email": invitation["email"], "error": error},
        )
        return {"configured": True, "sent": False, "error": error}
    sent_at = now_text()
    conn.execute(
        "UPDATE mobile_invitations SET email_sent_at = ?, email_error = '' WHERE id = ?",
        (sent_at, invitation["id"]),
    )
    audit_request(
        handler,
        conn,
        actor["id"] if actor else None,
        "send_mobile_invitation_email",
        "mobile_invitation",
        object_id=invitation["id"],
        details={"email": invitation["email"]},
    )
    return {"configured": True, "sent": True, "sent_at": sent_at}


def mobile_role_for_person(person_role):
    if person_role == "teachers":
        return "teacher"
    if person_role == "children":
        return "children"
    raise ValueError("Mobile invitations are only for children and teachers")


MOBILE_INVITATION_ROLES = {"boss", "principal", "teacher", "cook", "children"}


def ensure_mobile_person_for_user(conn, target_user):
    if target_user["person_id"]:
        person = conn.execute("SELECT * FROM persons WHERE id = ? AND project_id = ?", (target_user["person_id"], user_project_id(target_user))).fetchone()
        if person:
            return person["id"]
    if target_user["role"] == "children":
        raise ValueError("Child accounts must be linked to a child record before invitation")
    if target_user["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES:
        raise ValueError("This user role cannot use mobile attendance")
    name = (target_user["display_name"] or target_user["username"] or "").strip()
    if not name:
        raise ValueError("User display name is required")
    existing = conn.execute(
        "SELECT * FROM persons WHERE lower(name) = lower(?) AND role = 'teachers' AND project_id = ? ORDER BY id LIMIT 1",
        (name, user_project_id(target_user)),
    ).fetchone()
    if existing:
        person_id = existing["id"]
    else:
        conn.execute(
            """
            INSERT INTO persons(project_id, name, role, class_name, photo_path, qr_token, created_at)
            VALUES (?, ?, 'teachers', '', '', ?, ?)
            """,
            (user_project_id(target_user), name, f"STAFF:{secrets.token_urlsafe(16)}", now_text()),
        )
        person_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    conn.execute(
        "UPDATE web_users SET person_id = ?, updated_at = ? WHERE id = ?",
        (person_id, now_text(), target_user["id"]),
    )
    return person_id


def invitation_row(conn, token):
    return conn.execute(
        """
        SELECT mobile_invitations.*, persons.name AS person_name, persons.role AS person_role,
               persons.class_name AS class_name
        FROM mobile_invitations
        JOIN persons ON persons.id = mobile_invitations.person_id
        WHERE mobile_invitations.token = ?
        """,
        (token,),
    ).fetchone()


def invitation_is_expired(invitation):
    try:
        expires_at = datetime.strptime(invitation["expires_at"], "%Y-%m-%d %H:%M:%S")
    except (TypeError, ValueError):
        return True
    return expires_at < datetime.now()


def create_mobile_invitation(conn, actor, person_id, email, days=7, role_override=None):
    email = (email or "").strip()
    if not email or "@" not in email:
        raise ValueError("A valid email is required")
    person = conn.execute("SELECT * FROM persons WHERE id = ?", (person_id,)).fetchone()
    if not person:
        raise ValueError("Person not found")
    actor_project_id = effective_project_id(conn, actor) if actor else int(person["project_id"] or 1)
    project_id = int(person["project_id"] or actor_project_id)
    if actor and project_id != actor_project_id:
        raise ValueError("Person is not in this project")
    role = role_override or mobile_role_for_person(person["role"])
    if role not in MOBILE_INVITATION_ROLES:
        raise ValueError("This role cannot receive a mobile invitation")
    token = secrets.token_urlsafe(32)
    expires_at = (datetime.now() + timedelta(days=max(1, min(int(days or 7), 30)))).strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        """
        INSERT INTO mobile_invitations(project_id, token, person_id, role, email, invited_by_user_id, expires_at, accepted_at, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, NULL, ?)
        """,
        (project_id, token, person_id, role, email, actor["id"] if actor else None, expires_at, now_text()),
    )
    audit(
        conn,
        actor["id"] if actor else None,
        "create_mobile_invitation",
        "mobile_invitation",
        object_id=person_id,
        details={"person_name": person["name"], "role": role, "email": email, "expires_at": expires_at},
    )
    return token, expires_at


def unique_project_slug(conn, project_name):
    base = slugify(project_name) or "project"
    slug = base
    suffix = 2
    while conn.execute("SELECT 1 FROM projects WHERE slug = ?", (slug,)).fetchone():
        slug = f"{base}-{suffix}"
        suffix += 1
    return slug


def create_project_owner_invitation(conn, project_name, owner_name, email):
    project_name = (project_name or "").strip()
    owner_name = (owner_name or "").strip()
    email = (email or "").strip()
    if not project_name or not owner_name or "@" not in email:
        raise ValueError("Project name, owner name and valid email are required")
    now = now_text()
    slug = unique_project_slug(conn, project_name)
    cursor = conn.execute(
        """
        INSERT INTO projects(name, slug, status, owner_user_id, created_at, updated_at)
        VALUES (?, ?, 'pending_owner', NULL, ?, ?)
        """,
        (project_name, slug, now, now),
    )
    project_id = cursor.lastrowid
    conn.execute(
        """
        INSERT INTO persons(project_id, name, role, class_name, photo_path, qr_token, created_at)
        VALUES (?, ?, 'teachers', '', '', ?, ?)
        """,
        (project_id, owner_name, f"OWNER:{secrets.token_urlsafe(16)}", now),
    )
    person_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
    token, expires_at = create_mobile_invitation(
        conn,
        None,
        person_id,
        email,
        days=30,
        role_override="boss",
    )
    audit(
        conn,
        None,
        "create_project_owner_invitation",
        "project",
        object_id=project_id,
        details={"project_name": project_name, "owner_name": owner_name, "email": email, "expires_at": expires_at},
    )
    return token, project_id


def accept_mobile_invitation(conn, token, username, password):
    token = (token or "").strip()
    username = (username or "").strip()
    password = password or ""
    if not username or len(password) < 8:
        raise ValueError("Username and password of at least 8 characters are required")
    invitation = invitation_row(conn, token)
    if not invitation:
        raise ValueError("Invitation not found")
    if invitation["accepted_at"]:
        raise ValueError("Invitation has already been used")
    if invitation_is_expired(invitation):
        raise ValueError("Invitation has expired")
    existing = conn.execute("SELECT * FROM web_users WHERE lower(username) = lower(?)", (username,)).fetchone()
    if existing:
        if existing["role"] != invitation["role"]:
            raise ValueError("Username already exists")
        if int(existing["project_id"] or 1) != int(invitation["project_id"] or 1):
            raise ValueError("Username already exists")
        if existing["person_id"] and existing["person_id"] != invitation["person_id"]:
            raise ValueError("Username already exists")
        update_user_password(conn, existing["id"], password)
        conn.execute(
            "UPDATE web_users SET person_id = ?, project_id = ?, updated_at = ? WHERE id = ?",
            (invitation["person_id"], invitation["project_id"], now_text(), existing["id"]),
        )
        user_id = existing["id"]
    else:
        class_names = get_classes(conn, project_id=invitation["project_id"]) if invitation["role"] in {"teacher", "principal"} else []
        user_id = create_user(
            conn,
            username=username,
            display_name=invitation["person_name"],
            role=invitation["role"],
            password=password,
            person_id=invitation["person_id"],
            allowed_classes=class_names,
            project_id=invitation["project_id"],
        )
    conn.execute(
        "UPDATE mobile_invitations SET accepted_at = ? WHERE id = ?",
        (now_text(), invitation["id"]),
    )
    if invitation["role"] == "boss":
        project = conn.execute("SELECT * FROM projects WHERE id = ?", (invitation["project_id"],)).fetchone()
        if project and not project["owner_user_id"]:
            conn.execute(
                "UPDATE projects SET owner_user_id = ?, status = 'active', updated_at = ? WHERE id = ?",
                (user_id, now_text(), invitation["project_id"]),
            )
    audit(
        conn,
        user_id,
        "accept_mobile_invitation",
        "mobile_invitation",
        object_id=invitation["id"],
        details={"person_id": invitation["person_id"], "person_name": invitation["person_name"], "role": invitation["role"]},
    )
    return get_user_by_id(conn, user_id)


def get_bearer_session_user(handler):
    header = handler.headers.get("Authorization", "")
    if not header.lower().startswith("bearer "):
        return None
    token = header.split(" ", 1)[1].strip()
    if not token:
        return None
    with connect_db() as conn:
        return conn.execute(
            """
            SELECT web_users.*
            FROM sessions
            JOIN web_users ON web_users.id = sessions.user_id
            WHERE sessions.token = ? AND sessions.expires_at > ? AND web_users.is_active = 1
            """,
            (token, now_text()),
        ).fetchone()


def mobile_user_payload(user):
    return {
        "id": user["id"],
        "username": user["username"],
        "display_name": user["display_name"],
        "role": user["role"],
        "person_id": user["person_id"],
    }


def validate_mobile_device(conn, actor, device_id, request_handler=None, device_name=""):
    device_id = (device_id or "").strip()
    device_name = (device_name or "").strip()[:120]
    if len(device_id) < 16 or len(device_id) > 160:
        raise ValueError("Valid mobile device id is required")
    existing = conn.execute(
        "SELECT * FROM mobile_devices WHERE user_id = ? AND device_id = ?",
        (actor["id"], device_id),
    ).fetchone()
    if existing:
        conn.execute(
            "UPDATE mobile_devices SET last_seen_at = ?, device_name = COALESCE(NULLIF(?, ''), device_name), is_active = 1 WHERE id = ?",
            (now_text(), device_name, existing["id"]),
        )
        return conn.execute("SELECT * FROM mobile_devices WHERE id = ?", (existing["id"],)).fetchone()
    conn.execute(
        """
        INSERT INTO mobile_devices(user_id, device_id, device_name, first_seen_at, last_seen_at, is_active)
        VALUES (?, ?, ?, ?, ?, 1)
        """,
        (actor["id"], device_id, device_name, now_text(), now_text()),
    )
    device = conn.execute(
        "SELECT * FROM mobile_devices WHERE user_id = ? AND device_id = ?",
        (actor["id"], device_id),
    ).fetchone()
    audit_request(
        request_handler,
        conn,
        actor["id"],
        "mobile_device_bound",
        "mobile_device",
        object_id=device["id"] if device else actor["id"],
        details={"device_name": device_name, "binding_enforced": False},
    )
    return device


def mobile_person_status(conn, user):
    if not user["person_id"]:
        return None
    person = conn.execute(
        "SELECT id, name, role, class_name FROM persons WHERE id = ? AND project_id = ?",
        (user["person_id"], effective_project_id(conn, user)),
    ).fetchone()
    if not person:
        return None
    last = conn.execute(
        """
        SELECT event_type, timestamp
        FROM attendance
        WHERE person_id = ?
        ORDER BY timestamp DESC, id DESC
        LIMIT 1
        """,
        (person["id"],),
    ).fetchone()
    return {
        "person_id": person["id"],
        "name": person["name"],
        "role": person["role"],
        "class_name": person["class_name"],
        "status": "in" if last and last["event_type"] == "checkin" else "out",
        "last_event_type": last["event_type"] if last else None,
        "last_event_time": last["timestamp"] if last else None,
    }


def attendance_location_payload(conn, user=None, project_id=None):
    scoped_project_id = project_id if project_id is not None else (effective_project_id(conn, user) if user else 1)
    rows = conn.execute(
        """
        SELECT * FROM attendance_locations
        WHERE latitude IS NOT NULL AND longitude IS NOT NULL
          AND project_id = ?
        ORDER BY id
        """,
        (scoped_project_id,),
    ).fetchall()
    locations = [
        {
            "id": row["id"],
            "latitude": row["latitude"],
            "longitude": row["longitude"],
            "radius_meters": row["radius_meters"],
            "updated_at": row["updated_at"],
        }
        for row in rows
    ]
    if not locations:
        return {"configured": False, "latitude": None, "longitude": None, "radius_meters": 100, "locations": []}
    primary = locations[0]
    return {
        "configured": True,
        "latitude": primary["latitude"],
        "longitude": primary["longitude"],
        "radius_meters": primary["radius_meters"],
        "updated_at": primary["updated_at"],
        "locations": locations,
    }


def distance_meters(lat1, lon1, lat2, lon2):
    radius = 6371000.0
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    delta_phi = math.radians(lat2 - lat1)
    delta_lambda = math.radians(lon2 - lon1)
    a = math.sin(delta_phi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(delta_lambda / 2) ** 2
    return radius * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def validate_mobile_teacher_location(conn, latitude, longitude, user=None):
    policy = attendance_location_payload(conn, user)
    if not policy.get("configured"):
        raise ValueError("Work location is not configured")
    matches = []
    distances = []
    for location in policy.get("locations") or []:
        distance = distance_meters(latitude, longitude, location["latitude"], location["longitude"])
        distances.append(distance)
        if distance <= location["radius_meters"]:
            matches.append((distance, location))
    if not matches:
        nearest = min(distances) if distances else 0
        raise ValueError(f"Outside work location radius ({int(nearest)} m)")
    distance, location = min(matches, key=lambda item: item[0])
    return {"distance_meters": round(distance, 1), "radius_meters": location["radius_meters"], "location_id": location["id"]}


def save_mobile_face_snapshot(person_id, event_type, face_image_base64):
    cleaned = (face_image_base64 or "").strip()
    if "," in cleaned and cleaned.lower().startswith("data:"):
        cleaned = cleaned.split(",", 1)[1]
    try:
        payload = base64.b64decode(cleaned, validate=True)
    except (ValueError, binascii.Error) as exc:
        raise ValueError("Invalid face image") from exc
    if len(payload) < 1024:
        raise ValueError("Face image is too small")
    if len(payload) > 1500 * 1024:
        raise ValueError("Face image is too large")
    day_dir = MOBILE_FACE_SNAPSHOT_DIR / today_text()
    day_dir.mkdir(parents=True, exist_ok=True)
    stamp = local_now().strftime("%H%M%S_%f")
    filename = f"teacher_{int(person_id)}_{event_type}_{stamp}.jpg"
    path = day_dir / filename
    path.write_bytes(payload)
    return str(path)


def decode_base64_image_payload(image_base64):
    cleaned = (image_base64 or "").strip()
    if "," in cleaned and cleaned.lower().startswith("data:"):
        cleaned = cleaned.split(",", 1)[1]
    try:
        payload = base64.b64decode(cleaned, validate=True)
    except (ValueError, binascii.Error) as exc:
        raise ValueError("Invalid face image") from exc
    if len(payload) < 1024:
        raise ValueError("Face image is too small")
    if len(payload) > 1500 * 1024:
        raise ValueError("Face image is too large")
    return payload


def normalized_face_name(value):
    text = unicodedata.normalize("NFKD", value or "")
    text = "".join(ch for ch in text if not unicodedata.combining(ch)).lower()
    return re.sub(r"[^a-z0-9]+", "", text)


def reference_face_paths_for_person(person_name):
    if not FACE_DIR.exists():
        return []
    tokens = [normalized_face_name(part) for part in re.split(r"\s+", person_name or "") if len(part.strip()) >= 2]
    tokens = [token for token in tokens if token]
    if not tokens:
        return []
    candidates = []
    for path in FACE_DIR.iterdir():
        if path.suffix.lower() not in {".jpg", ".jpeg", ".png", ".bmp"}:
            continue
        file_key = normalized_face_name(path.stem)
        score = sum(1 for token in tokens if token in file_key)
        if score:
            candidates.append((score, path))
    candidates.sort(key=lambda item: (-item[0], item[1].name.lower()))
    return [path for _score, path in candidates[:8]]


def reference_face_filename_prefix(person_name):
    prefix = normalized_face_name(person_name) or "staff"
    return prefix[:48]


def face_detectors():
    global FACE_DETECTOR_CACHE
    if cv2 is None or np is None:
        raise ValueError("Server face verification requires OpenCV")
    if FACE_DETECTOR_CACHE is not None:
        return FACE_DETECTOR_CACHE
    cascade_factory = getattr(cv2, "CascadeClassifier", None)
    if cascade_factory is None and hasattr(cv2, "objdetect"):
        cascade_factory = getattr(cv2.objdetect, "CascadeClassifier", None)
    if cascade_factory is None:
        raise ValueError("Server OpenCV does not include CascadeClassifier")
    cascade_names = [
        "haarcascade_frontalface_default.xml",
        "haarcascade_frontalface_alt2.xml",
        "haarcascade_frontalface_alt.xml",
    ]
    detectors = []
    for cascade_name in cascade_names:
        cascade_path = Path(cv2.data.haarcascades) / cascade_name
        if cascade_path.exists():
            detector = cascade_factory(str(cascade_path))
            if not getattr(detector, "empty", lambda: False)():
                detectors.append(detector)
    if not detectors:
        raise ValueError("Server OpenCV face detector data is missing")
    FACE_DETECTOR_CACHE = detectors
    return detectors


def face_feature_from_bytes(payload, allow_rotation=False):
    if cv2 is None or np is None:
        raise ValueError("Server face verification requires OpenCV")
    buffer = np.frombuffer(payload, dtype=np.uint8)
    image = cv2.imdecode(buffer, cv2.IMREAD_COLOR)
    if image is None:
        raise ValueError("Invalid face image")
    detectors = face_detectors()
    def image_variants(source):
        yield source
        if allow_rotation:
            yield cv2.rotate(source, cv2.ROTATE_180)
            yield cv2.rotate(source, cv2.ROTATE_90_CLOCKWISE)
            yield cv2.rotate(source, cv2.ROTATE_90_COUNTERCLOCKWISE)

    best = None
    for variant in image_variants(image):
        height, width = variant.shape[:2]
        scale = min(1.0, 640.0 / max(width, height))
        if scale < 1.0:
            variant = cv2.resize(variant, (int(width * scale), int(height * scale)), interpolation=cv2.INTER_AREA)
        gray = cv2.cvtColor(variant, cv2.COLOR_BGR2GRAY)
        gray = cv2.equalizeHist(gray)
        min_side = min(gray.shape[:2])
        min_size = max(36, int(min_side * 0.08))
        for detector in detectors:
            for neighbors in (4, 3):
                faces = detector.detectMultiScale(gray, scaleFactor=1.05, minNeighbors=neighbors, minSize=(min_size, min_size))
                if len(faces) == 0:
                    continue
                face = max(faces, key=lambda item: item[2] * item[3])
                area = face[2] * face[3]
                if best is None or area > best[0]:
                    best = (area, gray, face)
    if best is None:
        raise ValueError("No face detected. Keep the face centered, remove mask/glasses glare, and use better light.")
    _area, gray, face = best
    x, y, w, h = face
    pad = int(max(w, h) * 0.22)
    x1 = max(0, x - pad)
    y1 = max(0, y - pad)
    x2 = min(gray.shape[1], x + w + pad)
    y2 = min(gray.shape[0], y + h + pad)
    crop = gray[y1:y2, x1:x2]
    if crop.size == 0:
        raise ValueError("No face detected")
    crop = cv2.resize(crop, (96, 96), interpolation=cv2.INTER_AREA)
    crop = cv2.equalizeHist(crop)
    hist = cv2.calcHist([crop], [0], None, [64], [0, 256])
    cv2.normalize(hist, hist)
    return crop.astype("float32"), hist


def face_similarity(feature_a, feature_b):
    crop_a, hist_a = feature_a
    crop_b, hist_b = feature_b
    hist_score = float(cv2.compareHist(hist_a, hist_b, cv2.HISTCMP_CORREL))
    corr = np.corrcoef(crop_a.reshape(-1), crop_b.reshape(-1))[0, 1]
    if np.isnan(corr):
        corr = 0.0
    pixel_score = max(0.0, min(1.0, (float(corr) + 1.0) / 2.0))
    hist_score = max(0.0, min(1.0, hist_score))
    return 0.65 * hist_score + 0.35 * pixel_score


def reference_face_feature(path):
    try:
        stat = path.stat()
    except OSError as exc:
        raise ValueError("Reference face photo not readable") from exc
    key = str(path.resolve())
    cache_value = FACE_FEATURE_CACHE.get(key)
    cache_signature = (stat.st_mtime_ns, stat.st_size)
    if cache_value and cache_value[0] == cache_signature:
        return cache_value[1]
    feature = face_feature_from_bytes(path.read_bytes(), allow_rotation=False)
    FACE_FEATURE_CACHE[key] = (cache_signature, feature)
    if len(FACE_FEATURE_CACHE) > 300:
        FACE_FEATURE_CACHE.clear()
    return feature


def verify_mobile_face_for_person(person, face_image_base64):
    payload = decode_base64_image_payload(face_image_base64)
    probe_feature = face_feature_from_bytes(payload, allow_rotation=True)
    reference_paths = reference_face_paths_for_person(person["name"])
    if not reference_paths:
        raise ValueError(f"No reference face photos found for {person['name']}")
    best_score = 0.0
    checked = 0
    for path in reference_paths:
        try:
            reference_feature = reference_face_feature(path)
        except ValueError:
            continue
        checked += 1
        best_score = max(best_score, face_similarity(probe_feature, reference_feature))
    if checked == 0:
        raise ValueError(f"No usable reference face photos found for {person['name']}")
    threshold = FACE_MATCH_THRESHOLD
    if best_score < threshold:
        raise ValueError(f"Face verification failed ({best_score:.2f})")
    return {"score": round(best_score, 3), "references_checked": checked}


def save_mobile_reference_faces(person, face_images_base64, min_photos=5):
    if not isinstance(face_images_base64, list):
        raise ValueError("Face photos are required")
    images = [str(value or "").strip() for value in face_images_base64 if str(value or "").strip()]
    if len(images) < min_photos:
        raise ValueError(f"Please capture at least {min_photos} face photo{'s' if min_photos != 1 else ''}")
    FACE_DIR.mkdir(parents=True, exist_ok=True)
    prefix = reference_face_filename_prefix(person["name"])
    existing = reference_face_paths_for_person(person["name"])
    start_index = len(existing) + 1
    saved_paths = []
    for offset, image_base64 in enumerate(images[:10], start=start_index):
        payload = decode_base64_image_payload(image_base64)
        face_feature_from_bytes(payload, allow_rotation=True)
        path = FACE_DIR / f"{prefix}_face_{offset}.jpg"
        path.write_bytes(payload)
        saved_paths.append(str(path))
    return saved_paths


def reset_mobile_reference_faces_for_person(person):
    paths = reference_face_paths_for_person(person["name"])
    deleted = 0
    face_root = FACE_DIR.resolve()
    for path in paths:
        try:
            resolved = path.resolve()
            if face_root not in (resolved, *resolved.parents):
                continue
            resolved.unlink(missing_ok=True)
            deleted += 1
        except OSError:
            continue
    return deleted


def render_mobile_invitation_accept(token, error=None):
    token = (token or "").strip()
    with connect_db() as conn:
        invitation = invitation_row(conn, token) if token else None
    if not invitation:
        body = '<div class="panel"><h2>Invitation mobile</h2><p class="error">Invitation introuvable.</p></div>'
        return html_page("Invitation mobile", None, body)
    if invitation["accepted_at"]:
        body = '<div class="panel"><h2>Invitation mobile</h2><p class="error">Cette invitation a déjà été utilisée.</p></div>'
        return html_page("Invitation mobile", None, body)
    if invitation_is_expired(invitation):
        body = '<div class="panel"><h2>Invitation mobile</h2><p class="error">Cette invitation a expiré.</p></div>'
        return html_page("Invitation mobile", None, body)
    error_html = f'<p class="error">{html.escape(error)}</p>' if error else ""
    body = f"""
    <div class="panel" style="max-width:520px;margin:0 auto">
      <h2>Invitation mobile</h2>
      <p><strong>{html.escape(invitation["person_name"])}</strong> &middot; {html.escape(ROLE_LABELS.get(invitation["role"], invitation["role"]))}</p>
      {error_html}
      <form method="post" action="/invite/accept">
        <input type="hidden" name="token" value="{html.escape(token)}">
        <label>Nom d'utilisateur<br><input name="username" required autocomplete="username"></label>
        <label>Mot de passe<br><input name="password" type="password" required minlength="8" autocomplete="new-password"></label>
        <label>Confirmer le mot de passe<br><input name="password_confirm" type="password" required minlength="8" autocomplete="new-password"></label>
        <button type="submit">Créer le compte</button>
      </form>
    </div>
    """
    return html_page("Invitation mobile", None, body)


def pwa_manifest():
    return {
        "id": f"/pititpas-system-{PWA_MANIFEST_VERSION}",
        "name": "",
        "short_name": "",
        "start_url": "/dashboard",
        "scope": "/",
        "display": "standalone",
        "background_color": "#eef6fb",
        "theme_color": "#dff1ff",
        "icons": [
            {"src": "/app-icon.svg", "sizes": "any", "type": "image/svg+xml", "purpose": "any maskable"}
        ],
    }


def app_icon_svg():
    return """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512">
<rect width="512" height="512" rx="96" fill="#dff1ff"/>
<circle cx="162" cy="188" r="64" fill="#f8c7cf"/>
<circle cx="350" cy="188" r="64" fill="#bfead2"/>
<path d="M104 372c18-72 82-118 152-118s134 46 152 118" fill="#cfe3ff"/>
<path d="M128 390h256" stroke="#24476f" stroke-width="34" stroke-linecap="round"/>
<text x="256" y="455" text-anchor="middle" font-family="Arial, sans-serif" font-size="54" font-weight="800" fill="#24476f">PP</text>
</svg>"""


def service_worker_js():
    return """self.addEventListener('install', function(event) {
  self.skipWaiting();
});
self.addEventListener('activate', function(event) {
  event.waitUntil(self.clients.claim());
});
self.addEventListener('fetch', function(event) {
  event.respondWith(fetch(event.request));
});
"""


def health_payload():
    with connect_db() as conn:
        tables = {
            row["name"]
            for row in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name IN ('web_users','attendance','mobile_invitations','mobile_devices','attendance_locations')"
            ).fetchall()
        }
        counts = {}
        for table_name in sorted(tables):
            counts[table_name] = conn.execute(f"SELECT COUNT(*) FROM {table_name}").fetchone()[0]
        location = attendance_location_payload(conn) if "attendance_locations" in tables else {"configured": False}
    return {
        "ok": True,
        "time": now_text(),
        "database": str(DB_PATH),
        "tables": sorted(tables),
        "counts": counts,
        "email_provider": email_provider(),
        "email_configured": email_configured(),
        "smtp_configured": email_configured(),
        "public_url_configured": bool(configured_public_url()),
        "work_location": location,
    }


def render_mobile_install(user):
    continue_href = "/mobile" if user and user["role"] == "children" else "/dashboard"
    continue_label = "Continuer vers Tableau"
    body = f"""
    <div class="panel" style="max-width:640px;margin:0 auto">
      <h2>Installer PITIT PAS SYSTEM</h2>
      <p class="muted">Ajoutez cette application à l'écran d'accueil du téléphone. La prochaine fois, ouvrez l'icône PITIT PAS SYSTEM sans saisir l'adresse du serveur.</p>
      <div class="grid" style="gap:10px;margin-top:12px">
        <button class="btn primary" type="button" id="install-app">Installer</button>
        <div class="muted-box">
          <strong>iPhone / Safari</strong><br>
          Touchez Partager, puis Ajouter à l'écran d'accueil.
        </div>
        <div class="muted-box">
          <strong>Android / Chrome</strong><br>
          Touchez Installer. Si le bouton ne s'affiche pas, ouvrez le menu Chrome puis Ajouter à l'écran d'accueil.
        </div>
        <a class="btn" href="{html.escape(continue_href)}">{html.escape(continue_label)}</a>
      </div>
    </div>
    <script>
    (function() {{
      if ('serviceWorker' in navigator) {{
        navigator.serviceWorker.register('/sw.js').catch(function() {{}});
      }}
      let deferredPrompt = null;
      const installButton = document.getElementById('install-app');
      window.addEventListener('beforeinstallprompt', function(event) {{
        event.preventDefault();
        deferredPrompt = event;
        installButton.disabled = false;
      }});
      installButton.addEventListener('click', async function() {{
        if (!deferredPrompt) {{
          alert("Si le bouton d'installation du navigateur ne s'affiche pas, utilisez le menu du navigateur et choisissez Ajouter à l'écran d'accueil.");
          return;
        }}
        deferredPrompt.prompt();
        await deferredPrompt.userChoice;
        deferredPrompt = null;
      }});
    }})();
    </script>
    """
    return html_page("Installer", user, body)


class Handler(BaseHTTPRequestHandler):
    server_version = "KindergartenAttendanceWeb/1.0"

    def log_message(self, format, *args):
        return

    def send_html(self, content, status=200, extra_headers=None):
        body = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        self.send_header("Content-Length", str(len(body)))
        if extra_headers:
            for key, value in extra_headers.items():
                self.send_header(key, value)
        self.end_headers()
        self.wfile.write(body)

    def send_text(self, content, status=200, content_type="text/plain; charset=utf-8"):
        body = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_file(self, path):
        try:
            data = path.read_bytes()
        except OSError:
            self.send_error(404)
            return
        mime = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        self.send_response(200)
        self.send_header("Content-Type", mime)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        user = get_session_user(self)
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)
        if path == "/manifest.webmanifest":
            manifest_body = json.dumps(pwa_manifest(), ensure_ascii=False).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/manifest+json; charset=utf-8")
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
            self.send_header("Content-Length", str(len(manifest_body)))
            self.end_headers()
            self.wfile.write(manifest_body)
            return
        if path == "/app-icon.svg":
            self.send_text(app_icon_svg(), content_type="image/svg+xml; charset=utf-8")
            return
        if path == "/sw.js":
            self.send_text(service_worker_js(), content_type="application/javascript; charset=utf-8")
            return
        if path == "/invite/accept":
            token = query.get("token", [""])[0]
            self.send_html(render_mobile_invitation_accept(token))
            return
        if path == "/privacy":
            self.send_html(render_privacy_policy())
            return
        if path == "/project/register":
            self.send_html(render_project_register())
            return
        if path == "/password-reset":
            self.send_html(render_password_reset())
            return
        if path == "/api/desktop/attendance":
            if not desktop_sync_authorized(self):
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            try:
                json_response(self, desktop_attendance_payload(query))
            except ValueError as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
            return
        if path.startswith("/media/"):
            path_token = path.split("/media/", 1)[1]
            file_path = safe_resolve_media(path_token)
            if not file_path or not file_path.exists():
                self.send_error(404)
                return
            self.send_file(file_path)
            return
        if path == "/api/mobile/me":
            mobile_user = get_bearer_session_user(self)
            if not mobile_user:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            with connect_db() as conn:
                status = mobile_person_status(conn, mobile_user)
            json_response(self, {"ok": True, "user": mobile_user_payload(mobile_user), "status": status})
            return
        if path == "/api/mobile/location-policy":
            mobile_user = get_bearer_session_user(self)
            if not mobile_user:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            with connect_db() as conn:
                payload = attendance_location_payload(conn, mobile_user)
            json_response(self, {"ok": True, "location": payload})
            return
        if not user:
            cookie = parse_cookie(self.headers.get("Cookie"))
            hide_project_register = (
                query.get("invited", ["0"])[0] == "1"
                or query.get("hide_project", ["0"])[0] == "1"
                or bool(cookie.get(INVITED_LOGIN_COOKIE))
            )
            if path == "/":
                self.send_html(login_page(show_project_register=not hide_project_register, contact_sent=query.get("contact", [""])[0] == "sent"))
                return
            self.send_html(login_page(show_project_register=not hide_project_register, contact_sent=query.get("contact", [""])[0] == "sent"))
            return
        if path not in {"/password-change", "/logout"} and password_is_expired(user):
            redirect(self, "/password-change")
            return
        if path == "/":
            if user["role"] == "children" or (user["role"] in STAFF_MOBILE_ATTENDANCE_ROLES and user["role"] != "boss"):
                redirect(self, "/mobile")
            else:
                redirect(self, "/dashboard")
            return
        if path == "/api/messages/unread":
            json_response(self, {"ok": True, "unread": unread_message_count(user)})
            return
        if path == "/projects":
            self.send_html(render_projects_admin(user, query))
            return
        if path == "/login-page-content":
            if not is_main_project_boss(user):
                self.send_error(403)
                return
            self.send_html(render_login_page_content_editor(user, query))
            return
        if path == "/projects/diagnostics":
            self.send_html(render_project_diagnostics(user))
            return
        if path == "/projects/delete":
            if not is_super_admin(user):
                self.send_error(403)
                return
            project_id_text = query.get("project_id", [""])[0]
            if not project_id_text.isdigit():
                self.send_error(400)
                return
            self.send_html(render_project_delete_confirm(user, int(project_id_text)))
            return
        if user["role"] == "children" and path in {"/reports", "/statistics", "/statistics/15min", "/teacher-attendance", "/export.xlsx", "/contacts", "/contacts.xlsx", "/users/export.xlsx", "/closed-dates", "/users", "/account", "/children", "/children/cards", "/mobile-invitations", "/audit", "/calendar", "/allergic-children"}:
            redirect(self, "/dashboard")
            return
        if path == "/dashboard":
            if user["role"] == "children":
                redirect(self, "/mobile")
                return
            self.send_html(render_dashboard(user, query))
            return
        if path == "/mobile":
            self.send_html(render_mobile_dashboard(user, query))
            return
        if path == "/mobile-install":
            self.send_html(render_mobile_install(user))
            return
        if path == "/me":
            self.send_html(render_me(user, query))
            return
        if path == "/profile":
            self.send_html(render_profile(user, query))
            return
        if path == "/agenda":
            if user["role"] == "cook":
                self.send_error(403)
                return
            if user["role"] == "children":
                self.send_html(render_child_agenda(user))
            else:
                self.send_html(render_staff_agenda(user, query))
            return
        if path == "/calendar":
            self.send_html(render_staff_calendar(user, query))
            return
        if path == "/allergic-children":
            self.send_html(render_allergic_children(user, query))
            return
        if path == "/contacts":
            self.send_html(render_contacts(user, query))
            return
        if path == "/contacts.xlsx":
            if user["role"] not in {"principal", "boss", "teacher", "cook"}:
                self.send_error(403)
                return
            payload = build_contacts_xlsx(user)
            filename = "contacts.xlsx"
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if path == "/users/export.xlsx":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            payload = build_users_xlsx(user)
            filename = "account_list.xlsx"
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if path == "/files":
            self.send_html(render_files(user, query))
            return
        if path == "/mail":
            self.send_html(render_mail(user, query))
            return
        if path.startswith("/child/") and path.count("/") == 2:
            self.send_error(404)
            return
        if path == "/reports":
            generate = query.get("generate", ["0"])[0] == "1"
            if generate:
                if user["role"] not in {"principal", "boss"}:
                    self.send_error(403)
                    return
                selected_date = query.get("date", [today_text()])[0]
                selected_format = query.get("format", ["detailed"])[0]
                try:
                    chosen_date = datetime.strptime(selected_date, "%Y-%m-%d").date()
                except ValueError:
                    chosen_date = datetime.now().date()
                if selected_format == "summary":
                    with connect_db() as conn:
                        report_project_id = effective_project_id(conn, user)
                    payload = generate_acceo_summary_attendance_pdf(chosen_date, report_project_id)
                    filename = f"Fiche_assiduite_summary_{chosen_date.strftime('%Y%m%d')}.pdf"
                else:
                    with connect_db() as conn:
                        report_project_id = effective_project_id(conn, user)
                    payload = generate_acceo_detail_attendance_pdf(chosen_date, report_project_id)
                    filename = f"Fiche_assiduite_detaillee_4_week_{chosen_date.strftime('%Y%m%d')}.pdf"
                download_token = query.get("download_token", [""])[0]
                self.send_response(200)
                self.send_header("Content-Type", "application/pdf")
                self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
                if download_token and download_token.replace(".", "").isalnum():
                    self.send_header("Set-Cookie", f"download_done={download_token}; Path=/; SameSite=Lax")
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            else:
                self.send_html(render_reports(user, query))
            return
        if path in {"/statistics", "/statistics/15min"}:
            self.send_html(render_statistics_15min(user, query))
            return
        if path == "/teacher-attendance":
            self.send_html(render_teacher_attendance(user, query))
            return
        if path == "/export.xlsx":
            if user["role"] not in {"principal", "boss"}:
                self.send_error(403)
                return
            selected_class = query.get("class", ["all"])[0]
            selected_date = query.get("date", [today_text()])[0]
            payload = build_attendance_export_xlsx(user, selected_class, selected_date)
            filename = f"attendance_{selected_date.replace('-', '')}.xlsx"
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if path == "/closed-dates":
            self.send_html(render_closed_dates(user, query))
            return
        if path == "/users":
            self.send_html(render_users(user, query))
            return
        if path == "/account":
            self.send_html(render_users(user, query, account_only=True))
            return
        if path == "/deleted-users":
            if user["role"] != "boss":
                self.send_error(403)
                return
            self.send_html(render_deleted_user_archive(user, query))
            return
        if path == "/children":
            self.send_html(render_children_admin(user, query))
            return
        if path == "/children/cards":
            self.send_html(render_children_cards_print(user))
            return
        if path == "/mobile-invitations":
            self.send_html(render_mobile_invitations(user, query))
            return
        if path == "/users/edit":
            target_id = query.get("id", [""])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            self.send_html(render_user_edit(user, int(target_id)))
            return
        if path == "/children/edit":
            target_id = query.get("id", [""])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            self.send_html(render_child_edit(user, int(target_id)))
            return
        if path == "/audit":
            if not can_view_audit_logs(user):
                self.send_error(403)
                return
            self.send_html(render_audit(user, query))
            return
        if path == "/api/dashboard-version":
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                classes = classes_for_user(user, conn)
                selected_class = query.get("class", ["all"])[0]
                selected_date = query.get("date", [today_text()])[0]
                if selected_class not in classes and selected_class != "all":
                    selected_class = classes[0] if classes else "all"
                children = get_children(conn, user, selected_class)
                payload = {"version": dashboard_version(conn, children, selected_date)}
            data = json.dumps(payload, ensure_ascii=False)
            self.send_text(data, content_type="application/json; charset=utf-8")
            return
        if path == "/api/teacher-attendance-version":
            if user["role"] not in {"principal", "boss"}:
                self.send_error(403)
                return
            selected_date = query.get("date", [today_text()])[0]
            try:
                selected_date = datetime.strptime(selected_date, "%Y-%m-%d").strftime("%Y-%m-%d")
            except ValueError:
                selected_date = today_text()
            with connect_db() as conn:
                payload = {"version": teacher_attendance_version(conn, selected_date)}
            data = json.dumps(payload, ensure_ascii=False)
            self.send_text(data, content_type="application/json; charset=utf-8")
            return
        if path == "/api/health":
            if user["role"] not in {"principal", "boss"}:
                self.send_error(403)
                return
            json_response(self, health_payload())
            return
        if path == "/password-change":
            self.send_html(render_password_change(user))
            return
        self.send_error(404)

    def do_POST(self):
        user = get_session_user(self)
        parsed = urlparse(self.path)
        path = parsed.path
        if path == "/api/desktop/attendance":
            if not desktop_sync_authorized(self):
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            try:
                payload = parse_json_post_data(self)
                result = sync_desktop_attendance(payload, ip_address=self.client_address[0] if self.client_address else None)
            except (json.JSONDecodeError, ValueError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            except sqlite3.Error as exc:
                json_response(self, {"ok": False, "error": f"Database error: {exc}"}, status=500)
                return
            json_response(self, result)
            return
        if path == "/api/mobile/login":
            try:
                payload = parse_json_post_data(self)
                username = str(payload.get("username", "")).strip()
                password = str(payload.get("password", ""))
            except (json.JSONDecodeError, ValueError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            with connect_db() as conn:
                target = login_user(conn, username, password)
                if not target:
                    json_response(self, {"ok": False, "error": "Invalid username or password"}, status=401)
                    return
                device_id = str(payload.get("device_id", "")).strip()
                device_name = str(payload.get("device_name", "")).strip()
                approval = check_login_connection_approval(conn, self, target, supplied_device_id=device_id, device_name=device_name)
                if not approval["ok"]:
                    conn.commit()
                    headers = {"Set-Cookie": connection_device_cookie_header(approval["device_key"])} if approval.get("set_cookie") else None
                    json_response(self, {"ok": False, "error": approval["error"]}, status=403, extra_headers=headers)
                    return
                token = create_session(conn, target["id"])
                status = mobile_person_status(conn, target)
                audit_request(self, conn, target["id"], "mobile_login", "session", object_id=target["id"], details={"username": target["username"]})
                conn.commit()
            headers = {"Set-Cookie": connection_device_cookie_header(approval["device_key"])} if approval.get("set_cookie") else None
            json_response(self, {"ok": True, "token": token, "user": mobile_user_payload(target), "status": status}, extra_headers=headers)
            return
        if path == "/contact":
            form = parse_post_data(self)
            if form.get("website", [""])[0].strip():
                redirect(self, "/?contact=sent")
                return
            name = form.get("name", [""])[0].strip()
            contact_detail = form.get("contact", [""])[0].strip()
            requirements = form.get("requirements", [""])[0].strip()
            language = form.get("language", ["fr"])[0].strip().lower()
            language = "en" if language == "en" else "fr"
            contact_values = {
                "name": name,
                "contact": contact_detail,
                "requirements": requirements,
            }
            if not name or not contact_detail or not requirements:
                self.send_html(login_page(contact_error="required", contact_values=contact_values), status=400)
                return
            if len(name) > 120 or len(contact_detail) > 200 or len(requirements) > 4000:
                self.send_html(login_page(contact_error="too_long", contact_values=contact_values), status=400)
                return
            client_ip = self.client_address[0] if self.client_address else "unknown"
            submitted_at = datetime.now(timezone.utc).timestamp()
            with PUBLIC_CONTACT_LOCK:
                last_submission = PUBLIC_CONTACT_LAST_SUBMISSION.get(client_ip, 0)
            if submitted_at - last_submission < 20:
                self.send_html(login_page(contact_error="rate", contact_values=contact_values), status=429)
                return
            try:
                with connect_db() as conn:
                    recipient = main_project_owner(conn)
                    if not recipient:
                        raise ValueError("Main project owner unavailable")
                    subject = ("Public contact - " if language == "en" else "Contact public - ") + name
                    message_body = f"""Nom / Name: {name}
Contact: {contact_detail}
Langue / Language: {language.upper()}

Demande / Requirements:
{requirements}"""
                    conn.execute(
                        """
                        INSERT INTO internal_messages(
                            sender_user_id, recipient_user_id, subject, body,
                            external_sender_name, external_sender_contact, created_at
                        )
                        VALUES (?, ?, ?, ?, ?, ?, ?)
                        """,
                        (
                            recipient["id"],
                            recipient["id"],
                            subject,
                            message_body,
                            name,
                            contact_detail,
                            now_text(),
                        ),
                    )
                    conn.commit()
            except (ValueError, sqlite3.Error):
                self.send_html(login_page(contact_error="unavailable", contact_values=contact_values), status=503)
                return
            with PUBLIC_CONTACT_LOCK:
                PUBLIC_CONTACT_LAST_SUBMISSION[client_ip] = submitted_at
                if len(PUBLIC_CONTACT_LAST_SUBMISSION) > 1000:
                    cutoff = submitted_at - 3600
                    stale_keys = [key for key, value in PUBLIC_CONTACT_LAST_SUBMISSION.items() if value < cutoff]
                    for key in stale_keys:
                        PUBLIC_CONTACT_LAST_SUBMISSION.pop(key, None)
            redirect(self, "/?contact=sent")
            return
        if path == "/invite/accept":
            form = parse_post_data(self)
            token_value = form.get("token", [""])[0]
            username = form.get("username", [""])[0]
            password = form.get("password", [""])[0]
            password_confirm = form.get("password_confirm", [""])[0]
            if password != password_confirm:
                self.send_html(render_mobile_invitation_accept(token_value, "Passwords do not match"))
                return
            try:
                with connect_db() as conn:
                    target = accept_mobile_invitation(conn, token_value, username, password)
                    session_token = create_session(conn, target["id"])
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                self.send_html(render_mobile_invitation_accept(token_value, str(exc)))
                return
            redirect(self, "/mobile-install", {"Set-Cookie": [session_cookie_header(session_token), invited_login_cookie_header()]})
            return
        if path == "/project/register":
            form = parse_post_data(self)
            project_name = form.get("project_name", [""])[0]
            owner_name = form.get("owner_name", [""])[0]
            email = form.get("email", [""])[0]
            try:
                with connect_db() as conn:
                    token_value, _project_id = create_project_owner_invitation(conn, project_name, owner_name, email)
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                self.send_html(render_project_register(error=str(exc)), status=200)
                return
            self.send_html(render_project_register(created_url=display_invite_url(token_value)), status=200)
            return
        if path == "/login":
            form = parse_post_data(self)
            username = form.get("username", [""])[0]
            password = form.get("password", [""])[0]
            with connect_db() as conn:
                target = login_user(conn, username, password)
                if not target:
                    self.send_html(login_page("Invalid username or password"))
                    return
                approval = check_login_connection_approval(conn, self, target)
                if not approval["ok"]:
                    conn.commit()
                    self.send_html(login_page(approval["error"]))
                    return
                token = create_session(conn, target["id"])
                audit_request(self, conn, target["id"], "login", "session", object_id=target["id"], details={"username": target["username"]})
                conn.commit()
            default_path = "/mobile" if target["role"] == "children" or (target["role"] in STAFF_MOBILE_ATTENDANCE_ROLES and target["role"] != "boss") else "/dashboard"
            next_path = "/password-change" if password_is_expired(target) else default_path
            cookie_headers = [session_cookie_header(token)]
            if approval.get("set_cookie"):
                cookie_headers.append(connection_device_cookie_header(approval["device_key"]))
            redirect(self, next_path, {"Set-Cookie": cookie_headers})
            return
        if path == "/password-reset":
            self.send_html(render_password_reset(), status=403)
            return
        if path == "/logout":
            if user:
                cookie = parse_cookie(self.headers.get("Cookie"))
                token = cookie.get("session")
                with connect_db() as conn:
                    if token:
                        delete_session(conn, token.value)
                    audit_request(self, conn, user["id"], "logout", "session", object_id=user["id"])
                    conn.commit()
            redirect(self, "/", {"Set-Cookie": [clear_session_cookie(), clear_project_context_cookie()]})
            return
        if path == "/projects/switch":
            if not user or not is_super_admin(user):
                self.send_error(403)
                return
            form = parse_post_data(self)
            project_id_text = form.get("project_id", [""])[0]
            if not project_id_text.isdigit():
                self.send_error(400)
                return
            project_id = int(project_id_text)
            with connect_db() as conn:
                project = conn.execute("SELECT id FROM projects WHERE id = ? AND status <> 'deleted'", (project_id,)).fetchone()
                if not project:
                    self.send_error(404)
                    return
            redirect(self, "/projects?switched=1", {"Set-Cookie": project_context_cookie_header(project_id)})
            return
        if path == "/login-page-content":
            if not is_main_project_boss(user):
                self.send_error(403)
                return
            form = parse_post_data(self)
            values = {key: form.get(key, [""])[0].strip() for key in LOGIN_PAGE_TEXT_DEFAULTS}
            if any(not value for value in values.values()):
                self.send_html(render_login_page_content_editor(user, values=values, error="All French and English fields are required."), status=400)
                return
            if any(len(value) > 500 for value in values.values()):
                self.send_html(render_login_page_content_editor(user, values=values, error="Each text must be 500 characters or fewer."), status=400)
                return
            with connect_db() as conn:
                if not is_main_project_boss(user, conn):
                    self.send_error(403)
                    return
                conn.execute(
                    """
                    INSERT INTO login_page_content(id, content_json, updated_by_user_id, updated_at)
                    VALUES (1, ?, ?, ?)
                    ON CONFLICT(id) DO UPDATE SET
                      content_json = excluded.content_json,
                      updated_by_user_id = excluded.updated_by_user_id,
                      updated_at = excluded.updated_at
                    """,
                    (json.dumps(values, ensure_ascii=False), user["id"], now_text()),
                )
                audit_request(self, conn, user["id"], "update_login_page_content", "login_page", object_id=1)
                conn.commit()
            redirect(self, "/login-page-content?saved=1")
            return
        if path == "/projects/delete":
            if not user or not is_super_admin(user):
                self.send_error(403)
                return
            form = parse_post_data(self)
            project_id_text = form.get("project_id", [""])[0]
            confirm_text = form.get("confirm", [""])[0]
            password = form.get("password", [""])[0]
            if not project_id_text.isdigit() or confirm_text != "DELETE":
                self.send_error(400)
                return
            project_id = int(project_id_text)
            try:
                with connect_db() as conn:
                    fresh_user = conn.execute("SELECT * FROM web_users WHERE id = ? AND is_active = 1", (user["id"],)).fetchone()
                    if not fresh_user or not verify_password(password, fresh_user["password_hash"]):
                        self.send_html(render_project_delete_confirm(user, project_id, "Mot de passe incorrect."), status=200)
                        return
                    delete_project_data(conn, project_id)
                    audit_request(self, conn, user["id"], "delete_project", "project", object_id=project_id)
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                self.send_html(html_page("Error", user, f'<div class="panel"><div class="alert error">{html.escape(str(exc))}</div><a class="btn" href="/projects">Retour</a></div>'), status=200)
                return
            headers = {}
            if user_project_id(user) == project_id:
                headers["Set-Cookie"] = project_context_cookie_header(1)
            redirect(self, "/projects?deleted=1", headers)
            return
        if path == "/api/mobile/invitations":
            actor = user or get_bearer_session_user(self)
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] not in {"boss", "principal"}:
                json_response(self, {"ok": False, "error": "Forbidden"}, status=403)
                return
            try:
                payload = parse_json_post_data(self)
                person_id = int(payload.get("person_id"))
                email = str(payload.get("email", "")).strip()
                days = int(payload.get("days", 7) or 7)
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            try:
                with connect_db() as conn:
                    token_value, expires_at = create_mobile_invitation(conn, actor, person_id, email, days)
                    delivery = deliver_mobile_invitation_email(conn, self, actor, token_value)
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            json_response(
                self,
                {
                    "ok": True,
                    "invite_url": mobile_invite_url(self, token_value),
                    "expires_at": expires_at,
                    "email_delivery": delivery,
                },
            )
            return
        if path == "/api/mobile/child-attendance":
            actor = get_bearer_session_user(self)
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] != "children" or not actor["person_id"]:
                json_response(self, {"ok": False, "error": "Child mobile account required"}, status=403)
                return
            try:
                payload = parse_json_post_data(self)
                event_type = str(payload.get("event_type", "")).strip()
                if event_type not in {"checkin", "checkout"}:
                    raise ValueError("Invalid event_type")
            except (json.JSONDecodeError, ValueError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            try:
                with connect_db() as conn:
                    record_attendance(conn, actor, actor["person_id"], event_type, source="mobile_manual", request_handler=self)
                    status = mobile_person_status(conn, actor)
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            json_response(self, {"ok": True, "status": status})
            return
        if path == "/api/mobile/teacher-schedule":
            actor = get_bearer_session_user(self) or user
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES or not actor["person_id"]:
                json_response(self, {"ok": False, "error": "Staff mobile account with linked person is required"}, status=403)
                return
            try:
                payload = parse_json_post_data(self)
                schedule_in = str(payload.get("schedule_in", "")).strip()
                schedule_out = str(payload.get("schedule_out", "")).strip()
                if not schedule_in or not schedule_out:
                    raise ValueError("SCHEDULE IN and SCHEDULE OUT are required")
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            day_text = today_text()
            try:
                with connect_db() as conn:
                    project_id = effective_project_id(conn, actor)
                    linked_person = conn.execute(
                        "SELECT id, name FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                        (actor["person_id"], project_id),
                    ).fetchone()
                    if not linked_person:
                        raise ValueError("This account is not linked to a staff person")
                    upsert_teacher_schedule_times(conn, actor, self, linked_person, day_text, schedule_in, schedule_out)
                    schedule = teacher_schedule_for_day(conn, linked_person["name"], day_text, project_id)
                    version = teacher_attendance_version(conn, day_text)
                    conn.commit()
            except ValueError as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            except sqlite3.Error as exc:
                json_response(self, {"ok": False, "error": f"Database error: {exc}"}, status=500)
                return
            json_response(self, {"ok": True, "schedule": schedule, "version": version})
            return
        if path == "/api/mobile/teacher-face-attendance":
            actor = get_bearer_session_user(self) or user
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES or not actor["person_id"]:
                json_response(self, {"ok": False, "error": "Staff mobile account with linked person is required"}, status=403)
                return
            try:
                payload = parse_json_post_data(self, max_bytes=2 * 1024 * 1024)
                event_type = str(payload.get("event_type", "")).strip()
                latitude = float(payload.get("latitude"))
                longitude = float(payload.get("longitude"))
                face_image = str(payload.get("face_image_base64", "")).strip()
                device_id = str(payload.get("device_id", "")).strip()
                device_name = str(payload.get("device_name", "")).strip()
                if event_type not in {"checkin", "checkout"}:
                    raise ValueError("Invalid event_type")
                if not (-90 <= latitude <= 90 and -180 <= longitude <= 180):
                    raise ValueError("Invalid coordinates")
                if len(face_image) < 200:
                    raise ValueError("Face image is required")
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            try:
                with connect_db() as conn:
                    project_id = effective_project_id(conn, actor)
                    linked_person = conn.execute(
                        "SELECT * FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                        (actor["person_id"], project_id),
                    ).fetchone()
                    if not linked_person:
                        raise ValueError("This account is not linked to a staff person")
                    device = validate_mobile_device(conn, actor, device_id, request_handler=self, device_name=device_name)
                    location_result = validate_mobile_teacher_location(conn, latitude, longitude, actor)
                    face_result = verify_mobile_face_for_person(linked_person, face_image)
                    snapshot_path = save_mobile_face_snapshot(actor["person_id"], event_type, face_image)
                    record_attendance(
                        conn,
                        actor,
                        actor["person_id"],
                        event_type,
                        source="mobile_face",
                        request_handler=self,
                        snapshot_path=snapshot_path,
                    )
                    status = mobile_person_status(conn, actor)
                    audit_request(
                        self,
                        conn,
                        actor["id"],
                        "mobile_teacher_face_verified",
                        "attendance",
                        object_id=actor["person_id"],
                        details={
                            "event_type": event_type,
                            "latitude": latitude,
                            "longitude": longitude,
                            "location_id": location_result.get("location_id"),
                            "distance_meters": location_result["distance_meters"],
                            "radius_meters": location_result["radius_meters"],
                            "face_score": face_result["score"],
                            "face_references_checked": face_result["references_checked"],
                            "snapshot_path": snapshot_path,
                            "mobile_device_id": device["id"] if device else None,
                            "mobile_device_name": device_name,
                        },
                    )
                    conn.commit()
            except ValueError as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=403)
                return
            except sqlite3.Error as exc:
                json_response(self, {"ok": False, "error": f"Database error: {exc}"}, status=500)
                return
            except Exception as exc:
                json_response(self, {"ok": False, "error": f"Face verification server error: {exc}"}, status=500)
                return
            json_response(self, {"ok": True, "status": status, "location": location_result})
            return
        if path == "/api/mobile/enroll-face":
            actor = get_bearer_session_user(self) or user
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] not in STAFF_MOBILE_ATTENDANCE_ROLES or not actor["person_id"]:
                json_response(self, {"ok": False, "error": "Staff mobile account with linked person is required"}, status=403)
                return
            try:
                payload = parse_json_post_data(self, max_bytes=8 * 1024 * 1024)
                face_images = payload.get("face_images_base64", [])
                if not face_images and payload.get("face_image_base64"):
                    face_images = [payload.get("face_image_base64")]
                device_id = str(payload.get("device_id", "")).strip()
                device_name = str(payload.get("device_name", "")).strip()
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            try:
                with connect_db() as conn:
                    project_id = effective_project_id(conn, actor)
                    linked_person = conn.execute(
                        "SELECT * FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                        (actor["person_id"], project_id),
                    ).fetchone()
                    if not linked_person:
                        raise ValueError("This account is not linked to a staff person")
                    device = validate_mobile_device(conn, actor, device_id, request_handler=self, device_name=device_name)
                    saved_paths = save_mobile_reference_faces(linked_person, face_images, min_photos=1)
                    audit_request(
                        self,
                        conn,
                        actor["id"],
                        "mobile_face_enrolled",
                        "person",
                        object_id=actor["person_id"],
                        details={
                            "saved_count": len(saved_paths),
                            "mobile_device_id": device["id"] if device else None,
                            "mobile_device_name": device_name,
                        },
                    )
                    conn.commit()
            except ValueError as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            except sqlite3.Error:
                json_response(self, {"ok": False, "error": "Database error"}, status=500)
                return
            except Exception as exc:
                json_response(self, {"ok": False, "error": f"Face enrollment server error: {exc}"}, status=500)
                return
            json_response(self, {"ok": True, "saved_count": len(saved_paths)})
            return
        if path == "/api/mobile/location-policy":
            actor = user or get_bearer_session_user(self)
            if not actor:
                json_response(self, {"ok": False, "error": "Unauthorized"}, status=401)
                return
            if actor["role"] != "boss":
                json_response(self, {"ok": False, "error": "Forbidden"}, status=403)
                return
            try:
                payload = parse_json_post_data(self)
                latitude = float(payload.get("latitude"))
                longitude = float(payload.get("longitude"))
                radius_meters = max(20, min(int(payload.get("radius_meters", 100) or 100), 1000))
                if not (-90 <= latitude <= 90 and -180 <= longitude <= 180):
                    raise ValueError("Invalid coordinates")
            except (TypeError, ValueError, json.JSONDecodeError) as exc:
                json_response(self, {"ok": False, "error": str(exc)}, status=400)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, actor)
                cursor = conn.execute(
                    """
                    INSERT INTO attendance_locations(project_id, latitude, longitude, radius_meters, updated_by_user_id, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?)
                    """,
                    (project_id, latitude, longitude, radius_meters, actor["id"], now_text()),
                )
                audit_request(
                    self,
                    conn,
                    actor["id"],
                    "update_mobile_location_policy",
                    "attendance_location",
                    object_id=cursor.lastrowid,
                    details={"latitude": latitude, "longitude": longitude, "radius_meters": radius_meters},
                )
                conn.commit()
                policy = attendance_location_payload(conn, actor)
            json_response(self, {"ok": True, "location": policy})
            return
        if not user:
            self.send_error(401)
            return

        content_type = self.headers.get("Content-Type", "")
        form = {} if "multipart/form-data" in content_type else parse_post_data(self)

        if path == "/mobile-invitations/create":
            if user["role"] not in {"boss", "principal"}:
                self.send_error(403)
                return
            try:
                invite_target = form.get("invite_target", [""])[0].strip()
                target_user_id = None
                if invite_target.startswith("user:"):
                    target_user_id = int(invite_target.split(":", 1)[1])
                    person_id = None
                elif invite_target.startswith("person:"):
                    person_id = int(invite_target.split(":", 1)[1])
                else:
                    person_id = int(form.get("person_id", [""])[0])
                email_value = form.get("email", [""])[0].strip()
                days = int(form.get("days", ["7"])[0] or "7")
                return_to = form.get("return_to", ["/mobile-invitations"])[0]
                if return_to not in {"/users", "/mobile-invitations"}:
                    return_to = "/mobile-invitations"
            except ValueError:
                self.send_error(400)
                return
            try:
                with connect_db() as conn:
                    project_id = effective_project_id(conn, user)
                    role_override = None
                    if target_user_id is not None:
                        target_user = conn.execute(
                            "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
                            (target_user_id, project_id),
                        ).fetchone()
                        if not target_user:
                            raise ValueError("User not found")
                        if not can_manage_users(user, target_user):
                            raise ValueError("You are not allowed to invite this user")
                        if target_user["role"] not in MOBILE_INVITATION_ROLES:
                            raise ValueError("This user role cannot receive a mobile invitation")
                        person_id = ensure_mobile_person_for_user(conn, target_user)
                        role_override = target_user["role"]
                    token_value, _expires_at = create_mobile_invitation(conn, user, person_id, email_value, days, role_override=role_override)
                    delivery = deliver_mobile_invitation_email(conn, self, user, token_value)
                    audit_request(
                        self,
                        conn,
                        user["id"],
                        "create_mobile_invitation_web",
                        "mobile_invitation",
                        object_id=person_id,
                        details={"email": email_value, "days": days},
                    )
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                self.send_html(html_page("Invitations mobiles", user, f'<div class="panel"><div class="alert error">{html.escape(str(exc))}</div><a class="btn" href="{html.escape(return_to)}">Retour</a></div>'))
                return
            if delivery.get("sent"):
                email_status = "sent"
            elif delivery.get("configured"):
                email_status = "error"
            else:
                email_status = "manual"
            if return_to == "/users":
                redirect(self, f"/users?invited=1&created_invite={quote(token_value)}#invite-user")
            else:
                redirect(self, f"/mobile-invitations?created={quote(token_value)}&person_id={person_id}&email={email_status}")
            return

        if path == "/project-logo/upload":
            if user["role"] != "boss":
                self.send_error(403)
                return
            try:
                multipart_form, files = parse_multipart_post_data(self)
                uploads = files.get("logo", [])
                if not uploads:
                    raise ValueError("Veuillez choisir une image.")
                with connect_db() as conn:
                    project_id = effective_project_id(conn, user)
                    stored_path = save_project_logo(project_id, uploads[0])
                    conn.execute("UPDATE projects SET logo_path = ?, updated_at = ? WHERE id = ?", (stored_path, now_text(), project_id))
                    audit_request(self, conn, user["id"], "upload_project_logo", "project", object_id=project_id, details={"filename": uploads[0].get("filename") or ""})
                    conn.commit()
            except (ValueError, sqlite3.Error) as exc:
                redirect(self, f"/mobile-invitations?logo_error={quote(str(exc))}#work-location")
                return
            redirect(self, "/mobile-invitations?logo=updated#work-location")
            return

        if path == "/mobile-location/update":
            if user["role"] != "boss":
                self.send_error(403)
                return
            action = form.get("action", ["add"])[0]
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                if action == "delete":
                    location_id = form.get("location_id", [""])[0]
                    if not location_id.isdigit():
                        self.send_error(400)
                        return
                    conn.execute("DELETE FROM attendance_locations WHERE id = ? AND project_id = ?", (int(location_id), project_id))
                    audit_request(
                        self,
                        conn,
                        user["id"],
                        "delete_mobile_location_policy_web",
                        "attendance_location",
                        object_id=int(location_id),
                    )
                else:
                    try:
                        latitude = float(form.get("latitude", [""])[0])
                        longitude = float(form.get("longitude", [""])[0])
                        radius_meters = max(20, min(int(form.get("radius_meters", ["100"])[0] or "100"), 1000))
                        if not (-90 <= latitude <= 90 and -180 <= longitude <= 180):
                            raise ValueError("Invalid coordinates")
                    except ValueError:
                        self.send_error(400)
                        return
                    cursor = conn.execute(
                        """
                        INSERT INTO attendance_locations(project_id, latitude, longitude, radius_meters, updated_by_user_id, updated_at)
                        VALUES (?, ?, ?, ?, ?, ?)
                        """,
                        (project_id, latitude, longitude, radius_meters, user["id"], now_text()),
                    )
                    audit_request(
                        self,
                        conn,
                        user["id"],
                        "add_mobile_location_policy_web",
                        "attendance_location",
                        object_id=cursor.lastrowid,
                        details={"latitude": latitude, "longitude": longitude, "radius_meters": radius_meters},
                    )
                conn.commit()
            redirect(self, "/mobile-invitations#work-location")
            return

        if path == "/mobile-face/reset":
            if user["role"] != "boss":
                self.send_error(403)
                return
            try:
                person_id = int(form.get("person_id", [""])[0])
            except ValueError:
                self.send_error(400)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                person = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'teachers' AND project_id = ?",
                    (person_id, project_id),
                ).fetchone()
                if not person:
                    self.send_error(404)
                    return
                deleted_count = reset_mobile_reference_faces_for_person(person)
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "reset_mobile_face_reference_photos",
                    "person",
                    object_id=person_id,
                    details={"person_name": person["name"], "deleted_count": deleted_count},
                )
                conn.commit()
            redirect(self, "/mobile-invitations#work-location")
            return

        if path == "/connection-approval/update":
            if user["role"] != "boss":
                self.send_error(403)
                return
            approval_id = form.get("id", [""])[0]
            action = form.get("action", [""])[0]
            if not approval_id.isdigit() or action not in {"approve", "reject"}:
                self.send_error(400)
                return
            status = "approved" if action == "approve" else "rejected"
            approved_at = now_text() if status == "approved" else ""
            with connect_db() as conn:
                row = conn.execute("SELECT * FROM user_connection_approvals WHERE id = ?", (int(approval_id),)).fetchone()
                if not row:
                    self.send_error(404)
                    return
                conn.execute(
                    """
                    UPDATE user_connection_approvals
                    SET status = ?, approved_at = ?, approved_by_user_id = ?
                    WHERE id = ?
                    """,
                    (status, approved_at, user["id"] if status == "approved" else None, int(approval_id)),
                )
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "connection_approval_update",
                    "connection_approval",
                    object_id=int(approval_id),
                    details={"status": status, "target_user_id": row["user_id"], "ip_address": row["ip_address"], "mac_address": row["mac_address"]},
                )
                conn.commit()
            redirect(self, "/mobile-invitations#work-location")
            return

        if path == "/teacher-attendance/load-schedule":
            if user["role"] != "boss":
                self.send_error(403)
                return
            form, files = parse_multipart_post_data(self)
            upload_values = files.get("schedule_file") or []
            upload = upload_values[0] if upload_values else None
            if not upload or not upload.get("content"):
                self.send_html(html_page("Error", user, '<div class="panel">Please choose a schedule file.</div>'), status=200)
                return
            try:
                source_filename = upload.get("filename") or "schedule.xlsx"
                schedule_rows = normalize_teacher_schedule(source_filename, upload["content"])
                output_name, output_path, payload, row_count = build_teacher_schedule_xlsx(source_filename, upload["content"])
            except Exception as exc:
                self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'), status=200)
                return
            with connect_db() as conn:
                saved_count, saved_dates = save_teacher_schedule_rows(conn, schedule_rows, source_filename)
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "load_teacher_schedule",
                    "teacher_schedule",
                    object_id=output_name,
                    details={
                        "source_filename": source_filename,
                        "output_path": str(output_path),
                        "row_count": row_count,
                        "saved_count": saved_count,
                        "dates": saved_dates,
                    },
                )
                conn.commit()
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            self.send_header("Content-Disposition", f'attachment; filename="{output_name}"')
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return

        if path == "/agenda/send":
            if user["role"] in {"children", "cook"}:
                self.send_error(403)
                return
            class_name = form.get("class_name", [""])[0].strip()
            day_text = form.get("day_text", [today_text()])[0].strip()
            title = "Rapport du jour"
            child_person_ids = []
            for value in form.get("child_person_ids", []):
                if value.isdigit() and int(value) not in child_person_ids:
                    child_person_ids.append(int(value))
            try:
                datetime.strptime(day_text, "%Y-%m-%d")
            except ValueError:
                self.send_error(400)
                return
            if not class_name:
                self.send_error(400)
                return
            with connect_db() as conn:
                classes = classes_for_user(user, conn)
                if class_name not in classes:
                    self.send_error(403)
                    return
                children = get_children(conn, user, class_name)
                allowed_person_ids = {int(child["id"]) for child in children}
                sent_count = 0
                skipped_count = 0
                for child_person_id in child_person_ids:
                    body_text = form.get(f"body_person_{child_person_id}", [""])[0].strip()
                    if not body_text:
                        skipped_count += 1
                        continue
                    if child_person_id not in allowed_person_ids:
                        skipped_count += 1
                        continue
                    if current_child_status(conn, child_person_id, day_text) != "P":
                        skipped_count += 1
                        continue
                    child_users = conn.execute(
                        """
                        SELECT web_users.*, persons.name AS child_name, persons.class_name AS child_class_name
                        FROM web_users
                        JOIN persons ON persons.id = web_users.person_id
                        WHERE web_users.person_id = ? AND web_users.role = 'children' AND web_users.is_active = 1
                          AND web_users.project_id = ?
                        """,
                        (child_person_id, project_id),
                    ).fetchall()
                    if not child_users:
                        skipped_count += 1
                        continue
                    for child_user in child_users:
                        conn.execute(
                            """
                            INSERT INTO child_agenda_entries(
                                child_user_id, child_person_id, class_name, day_text, title, body,
                                author_user_id, author_name, created_at
                            )
                            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                            """,
                            (
                                child_user["id"],
                                child_person_id,
                                class_name,
                                day_text,
                                title,
                                body_text,
                                user["id"],
                                user["display_name"],
                                now_text(),
                            ),
                        )
                        sent_count += 1
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "send_class_agenda",
                    "agenda",
                    object_id=class_name,
                    details={"class_name": class_name, "day_text": day_text, "sent": sent_count, "skipped": skipped_count},
                )
                conn.commit()
            redirect(self, f"/agenda?class={quote(class_name)}&date={quote(day_text)}&sent={sent_count}&skipped={skipped_count}")
            return

        if path == "/profile/update":
            target_id = form.get("target_user_id", [str(user["id"])])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                if not target:
                    self.send_error(404)
                    return
                if target_user_id != user["id"] and not can_manage_users(user, target):
                    self.send_error(403)
                    return
                phones = split_lines(form.get("phones", [""])[0])
                emails = split_lines(form.get("emails", [""])[0])
                notes = form.get("notes", [""])[0].strip()
                existing_profile = get_profile(conn, target_user_id)
                existing_allergies = existing_profile["allergies"] if "allergies" in existing_profile.keys() else ""
                allergies = form.get("allergies", [existing_allergies])[0].strip()
                folder = ensure_user_folder(target)
                conn.execute(
                    """
                    INSERT INTO user_profiles(user_id, phones_json, emails_json, folder_path, allergies, notes, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(user_id) DO UPDATE SET
                      phones_json = excluded.phones_json,
                      emails_json = excluded.emails_json,
                      folder_path = excluded.folder_path,
                      allergies = excluded.allergies,
                      notes = excluded.notes,
                      updated_at = excluded.updated_at
                    """,
                    (
                        target_user_id,
                        json.dumps(phones, ensure_ascii=False),
                        json.dumps(emails, ensure_ascii=False),
                        str(folder),
                        allergies,
                        notes,
                        now_text(),
                    ),
                )
                audit_request(self, conn, user["id"], "update_profile", "user", object_id=target_user_id)
                conn.commit()
            redirect(self, f"/profile?user_id={target_user_id}&saved=1")
            return

        if path == "/profile/avatar/upload":
            if user["role"] != "children":
                self.send_error(403)
                return
            form, files = parse_multipart_post_data(self)

            def redirect_profile_flash(kind, message):
                token = secrets.token_urlsafe(12)
                FLASH_MESSAGES[token] = (kind, message)
                redirect(self, f"/profile?profile_flash={quote(token)}")

            upload_values = files.get("avatar_file") or []
            upload = upload_values[0] if upload_values else None
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                target = conn.execute("SELECT * FROM web_users WHERE id = ? AND is_active = 1", (user["id"],)).fetchone()
                if not target or target["role"] != "children" or not target["person_id"]:
                    self.send_error(404)
                    return
                child = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                    (target["person_id"], project_id),
                ).fetchone()
                if not child:
                    self.send_error(404)
                    return
                expected_filename = expected_child_avatar_filename(child["name"])
                actual_filename = uploaded_filename_basename(upload.get("filename") if upload else "")
                if not child_avatar_filename_matches(actual_filename, child["name"]):
                    redirect_profile_flash("warn", f"Le fichier doit s'appeler exactement: {expected_filename}")
                    return
                try:
                    save_child_avatar_upload(conn, self, user, child, upload, "upload_child_avatar")
                    conn.commit()
                except ValueError as exc:
                    conn.rollback()
                    redirect_profile_flash("warn", str(exc))
                    return
            redirect_profile_flash("info", "Avatar enfant mis à jour.")
            return

        if path == "/profile/calendar/add":
            target_id = form.get("target_user_id", [str(user["id"])])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            event_type = form.get("event_type", [""])[0].strip().upper()
            calendar_month = form.get("calendar_month", [""])[0].strip()
            if event_type not in {"VACANCES", "MALADIE", "ABSENCE", "AUTRE"}:
                self.send_error(400)
                return
            note = form.get("note", [""])[0].strip()
            date_values = []
            for value in form.get("calendar_dates", []):
                if value not in date_values:
                    date_values.append(value)
            fallback_date = form.get("calendar_date", [""])[0].strip()
            if fallback_date and fallback_date not in date_values:
                date_values.append(fallback_date)
            valid_dates = []
            for value in date_values:
                try:
                    datetime.strptime(value, "%Y-%m-%d")
                except ValueError:
                    continue
                valid_dates.append(value)
            if not valid_dates:
                self.send_error(400)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                target = conn.execute(
                    "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
                    (target_user_id, project_id),
                ).fetchone()
                if not target or target["role"] != "children":
                    self.send_error(404)
                    return
                if target_user_id != user["id"] and not can_manage_users(user, target):
                    self.send_error(403)
                    return
                for day_text in valid_dates:
                    existing = conn.execute(
                        """
                        SELECT id FROM child_calendar_events
                        WHERE user_id = ? AND day_text = ? AND event_type = ? AND note = ?
                        LIMIT 1
                        """,
                        (target_user_id, day_text, event_type, note),
                    ).fetchone()
                    if existing:
                        continue
                    conn.execute(
                        """
                        INSERT INTO child_calendar_events(user_id, day_text, event_type, note, created_by_user_id, created_at)
                        VALUES (?, ?, ?, ?, ?, ?)
                        """,
                        (target_user_id, day_text, event_type, note, user["id"], now_text()),
                    )
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "add_child_calendar",
                    "user",
                    object_id=target_user_id,
                    details={"dates": valid_dates, "event_type": event_type, "note": note},
                )
                conn.commit()
            month_query = f"&calendar_month={quote(calendar_month)}" if re.match(r"^\d{4}-\d{2}$", calendar_month or "") else ""
            redirect(self, f"/profile?user_id={target_user_id}&saved=1{month_query}#child-calendar")
            return

        if path == "/profile/calendar/delete":
            target_id = form.get("target_user_id", [str(user["id"])])[0]
            event_id = form.get("event_id", [""])[0]
            calendar_month = form.get("calendar_month", [""])[0].strip()
            if not target_id.isdigit() or not event_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            event_id_int = int(event_id)
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                event = conn.execute(
                    "SELECT * FROM child_calendar_events WHERE id = ? AND user_id = ?",
                    (event_id_int, target_user_id),
                ).fetchone()
                if not target or target["role"] != "children" or not event:
                    self.send_error(404)
                    return
                if target_user_id != user["id"] and not can_manage_users(user, target):
                    self.send_error(403)
                    return
                deleted_count = conn.execute(
                    """
                    DELETE FROM child_calendar_events
                    WHERE user_id = ? AND day_text = ? AND event_type = ? AND note = ?
                    """,
                    (target_user_id, event["day_text"], event["event_type"], event["note"]),
                ).rowcount
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "delete_child_calendar",
                    "user",
                    object_id=target_user_id,
                    details={"event_id": event_id_int, "day_text": event["day_text"], "event_type": event["event_type"], "deleted_count": deleted_count},
                )
                conn.commit()
            month_query = f"&calendar_month={quote(calendar_month)}" if re.match(r"^\d{4}-\d{2}$", calendar_month or "") else ""
            redirect(self, f"/profile?user_id={target_user_id}&saved=1{month_query}#child-calendar")
            return

        if path == "/files/upload":
            form, files = parse_multipart_post_data(self)
            target_id = form.get("target_user_id", [str(user["id"])])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                if not target:
                    self.send_error(404)
                    return
                if not can_access_files(user, target):
                    self.send_error(403)
                    return
                upload_values = files.get("photo") or files.get("file") or []
                if isinstance(upload_values, dict):
                    upload_values = [upload_values]
                uploads = [item for item in upload_values if item.get("content")]
                if not uploads:
                    self.send_error(400)
                    return
                folder = ensure_user_folder(target)
                note = form.get("note", [""])[0].strip()
                uploaded_names = []
                for index, upload in enumerate(uploads, start=1):
                    original = safe_filename(upload.get("filename") or "upload.bin")
                    stored_name = f"{datetime.now().strftime('%Y%m%d_%H%M%S_%f')}_{safe_filename(user['username'])}_{index}_{original}"
                    stored_path = folder / stored_name
                    stored_path.write_bytes(upload["content"])
                    conn.execute(
                        """
                        INSERT INTO user_files(owner_user_id, uploader_user_id, original_name, stored_path, note, uploaded_at)
                        VALUES (?, ?, ?, ?, ?, ?)
                        """,
                        (target_user_id, user["id"], original, str(stored_path), note, now_text()),
                    )
                    uploaded_names.append(original)
                audit_request(self, conn, user["id"], "upload_file", "user_file", object_id=target_user_id, details={"filenames": uploaded_names})
                conn.commit()
            redirect(self, f"/files?user_id={target_user_id}")
            return

        if path == "/files/delete":
            target_id = form.get("target_user_id", [str(user["id"])])[0]
            file_id = form.get("file_id", [""])[0]
            file_token = form.get("file_token", [""])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                if not target:
                    self.send_error(404)
                    return
                if not can_access_files(user, target):
                    self.send_error(403)
                    return
                file_row = None
                file_path = None
                if file_id.isdigit():
                    file_row = conn.execute("SELECT * FROM user_files WHERE id = ? AND owner_user_id = ?", (int(file_id), target_user_id)).fetchone()
                    if not file_row:
                        self.send_error(404)
                        return
                    file_path = safe_resolve_user_file(file_path_token(file_row["stored_path"]), target)
                elif file_token:
                    file_path = safe_resolve_user_file(file_token, target)
                    if not file_path:
                        self.send_error(404)
                        return
                    file_row = conn.execute("SELECT * FROM user_files WHERE owner_user_id = ? AND stored_path = ?", (target_user_id, str(file_path))).fetchone()
                else:
                    self.send_error(400)
                    return
                deleted_name = file_row["original_name"] if file_row else (file_path.name if file_path else "")
                if file_row:
                    conn.execute("DELETE FROM user_files WHERE id = ?", (file_row["id"],))
                if file_path and file_path.exists():
                    try:
                        file_path.unlink()
                    except OSError:
                        self.send_error(500)
                        return
                audit_request(self, conn, user["id"], "delete_file", "user_file", object_id=file_id or target_user_id, details={"filename": deleted_name})
                conn.commit()
            redirect(self, f"/files?user_id={target_user_id}&deleted=1")
            return

        if path == "/mail/send":
            if "multipart/form-data" in content_type:
                form, files = parse_multipart_post_data(self)
            else:
                files = {}
            recipient_values = form.get("recipient_emails", [])
            subject = form.get("subject", [""])[0].strip()
            body_text = form.get("body", [""])[0].strip()
            photo_resize_mode = form.get("photo_resize_mode", [""])[0].strip()
            attachments = [item for item in files.get("attachments", []) if item.get("content")]
            folder_attachment_tokens = form.get("folder_attachments", [])
            if not recipient_values:
                self.send_html(render_mail(user, {}, error="MESSAGE recipient is required."), status=200)
                return
            with connect_db() as conn:
                allowed = {}
                for row in mail_recipients(conn, user):
                    try:
                        emails = json.loads(row["emails_json"] or "[]")
                    except json.JSONDecodeError:
                        emails = []
                    display_name = row["display_name"] or row["username"]
                    contact_label = emails[0] if emails else row["username"]
                    allowed[str(row["id"])] = (row["id"], contact_label)
                    for email_address in emails:
                        allowed[f"{row['id']}|{email_address}"] = (row["id"], email_address)
                valid = [allowed[value] for value in recipient_values if value in allowed]
                if not valid:
                    self.send_html(render_mail(user, {}, error="Please choose a valid MESSAGE recipient."), status=200)
                    return
                unique_recipient_ids = {recipient_id for recipient_id, _contact_label in valid}
                if not can_mail_multi_select(user) and len(unique_recipient_ids) > 1:
                    self.send_html(render_mail(user, {}, error="Please choose only one MESSAGE recipient."), status=200)
                    return
                folder_attachments = []
                seen_folder_paths = set()
                for token in folder_attachment_tokens:
                    source_path = safe_resolve_user_file(token, user)
                    if not source_path or not source_path.is_file():
                        self.send_html(render_mail(user, {}, error="Please choose valid files from your folder."), status=200)
                        return
                    path_key = str(source_path.resolve()).lower()
                    if path_key in seen_folder_paths:
                        continue
                    try:
                        content = source_path.read_bytes()
                    except OSError:
                        self.send_html(render_mail(user, {}, error="A selected folder file could not be opened."), status=200)
                        return
                    folder_attachments.append({"filename": source_path.name, "content": content})
                    seen_folder_paths.add(path_key)
                all_attachments = attachments + folder_attachments
                if mail_attachments_need_resize(all_attachments):
                    if photo_resize_mode not in MAIL_PHOTO_RESIZE_SIZES:
                        photo_resize_mode = "large"
                    all_attachments = [resize_mail_photo_attachment(upload, photo_resize_mode) for upload in all_attachments]
                saved_attachment_names = []
                for recipient_id, contact_label in sorted(set(valid)):
                    attachment_names = []
                    if all_attachments:
                        recipient = conn.execute(
                            "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
                            (recipient_id, effective_project_id(conn, user)),
                        ).fetchone()
                        if not recipient:
                            continue
                        folder = ensure_user_folder(recipient)
                        for index, upload in enumerate(all_attachments, start=1):
                            original = safe_filename(upload.get("filename") or "attachment.bin")
                            stored_name = f"{datetime.now().strftime('%Y%m%d_%H%M%S_%f')}_{safe_filename(user['username'])}_{index}_{original}"
                            stored_path = folder / stored_name
                            stored_path.write_bytes(upload["content"])
                            conn.execute(
                                """
                                INSERT INTO user_files(owner_user_id, uploader_user_id, original_name, stored_path, note, uploaded_at)
                                VALUES (?, ?, ?, ?, ?, ?)
                                """,
                                (recipient_id, user["id"], original, str(stored_path), f"MESSAGE attachment: {subject}", now_text()),
                            )
                            attachment_names.append(original)
                            saved_attachment_names.append(original)
                    message_body = f"To: {contact_label}\n\n{body_text}"
                    if attachment_names:
                        message_body += "\n\nAttachments:\n" + "\n".join(f"- {name}" for name in attachment_names)
                    conn.execute(
                        """
                        INSERT INTO internal_messages(sender_user_id, recipient_user_id, subject, body, created_at)
                        VALUES (?, ?, ?, ?, ?)
                        """,
                        (user["id"], recipient_id, subject, message_body, now_text()),
                    )
                audit_request(self, conn, user["id"], "send_message", "internal_message", details={"recipients": [contact for _rid, contact in valid], "subject": subject, "attachments": sorted(set(saved_attachment_names))})
                conn.commit()
            redirect(self, "/mail?sent=1")
            return

        if path == "/password-change":
            current_password = form.get("current_password", [""])[0]
            new_password = form.get("password", [""])[0]
            confirm = form.get("confirm", [""])[0]
            if len(new_password) < 8:
                self.send_html(render_password_change(user, "Password must be at least 8 characters."), status=200)
                return
            if new_password != confirm:
                self.send_html(render_password_change(user, "Passwords do not match."), status=200)
                return
            with connect_db() as conn:
                fresh_user = conn.execute("SELECT * FROM web_users WHERE id = ?", (user["id"],)).fetchone()
                if not fresh_user or not verify_password(current_password, fresh_user["password_hash"]):
                    self.send_html(render_password_change(user, "Current password is incorrect."), status=200)
                    return
                try:
                    update_user_password(conn, user["id"], new_password)
                    audit_request(self, conn, user["id"], "password_change", "user", object_id=user["id"])
                    conn.commit()
                except ValueError as exc:
                    self.send_html(render_password_change(user, str(exc)), status=200)
                    return
            redirect(self, "/dashboard")
            return

        if path == "/teacher-attendance/update-times":
            if user["role"] not in {"principal", "boss"}:
                self.send_error(403)
                return
            is_ajax = form.get("ajax", [""])[0] == "1" or self.headers.get("X-Requested-With") == "fetch"
            action_mode = form.get("action", [""])[0]
            pay_start = form.get("pay_start", [""])[0]
            pay_end = form.get("pay_end", [""])[0]
            try:
                with connect_db() as conn:
                    selected_date, _changed = update_teacher_status_times(conn, user, self, form)
                    conn.commit()
                    version = teacher_attendance_version(conn, selected_date)
            except ValueError as exc:
                if is_ajax:
                    json_response(self, {"ok": False, "error": str(exc)}, status=400)
                    return
                self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'), status=200)
                return
            if is_ajax:
                json_response(self, {"ok": True, "date": selected_date, "version": version})
                return
            query_parts = [f"date={quote(selected_date)}"]
            if action_mode:
                query_parts.append(f"action={quote(action_mode)}")
            if pay_start:
                query_parts.append(f"pay_start={quote(pay_start)}")
            if pay_end:
                query_parts.append(f"pay_end={quote(pay_end)}")
            redirect(self, f"/teacher-attendance?{'&'.join(query_parts)}")
            return

        if path == "/teacher-attendance/delete-day":
            if user["role"] != "boss":
                self.send_error(403)
                return
            teacher_id = form.get("delete_teacher_id", [""])[0].strip()
            selected_date = form.get("date", [today_text()])[0]
            action_mode = form.get("action", [""])[0]
            pay_start = form.get("pay_start", [""])[0]
            pay_end = form.get("pay_end", [""])[0]
            if not teacher_id.isdigit():
                self.send_error(400)
                return
            try:
                selected_date = datetime.strptime(selected_date, "%Y-%m-%d").strftime("%Y-%m-%d")
                with connect_db() as conn:
                    delete_teacher_day_attendance(conn, user, int(teacher_id), selected_date, request_handler=self)
                    conn.commit()
            except ValueError as exc:
                self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'), status=200)
                return
            query_parts = [f"date={quote(selected_date)}"]
            if action_mode:
                query_parts.append(f"action={quote(action_mode)}")
            if pay_start:
                query_parts.append(f"pay_start={quote(pay_start)}")
            if pay_end:
                query_parts.append(f"pay_end={quote(pay_end)}")
            redirect(self, f"/teacher-attendance?{'&'.join(query_parts)}")
            return

        if path.startswith("/child/") and path.endswith("/event"):
            child_id = path.split("/")[2]
            event_type = form.get("event_type", [""])[0]
            day_text = form.get("date", [today_text()])[0]
            return_to = form.get("return_to", [""])[0]
            if event_type not in {"checkin", "checkout"}:
                self.send_error(400)
                return
            with connect_db() as conn:
                child = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                    (child_id, effective_project_id(conn, user)),
                ).fetchone()
                if not child:
                    self.send_error(404)
                    return
                if user["role"] == "children":
                    if user["person_id"] != child["id"] or day_text != today_text():
                        self.send_error(403)
                        return
                elif not can_view_all_classes(user) and child["class_name"] not in classes_for_user(user, conn):
                    self.send_error(403)
                    return
                try:
                    if user["role"] == "teacher" and recent_teacher_event_block(conn, child["id"], event_type):
                        raise ValueError("Teacher attendance changes are locked for 30 minutes after the last record")
                    if day_text != today_text():
                        timestamp = f"{day_text} {local_now().strftime('%H:%M:%S')}"
                        conn.execute(
                            "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path) VALUES (?, ?, ?, ?, ?, NULL)",
                            (child["id"], child["name"], child["role"], event_type, timestamp),
                        )
                        audit_request(
                            self,
                            conn,
                            user["id"],
                            f"manual_{event_type}",
                            "attendance",
                            object_id=child["id"],
                            details={
                                "date": day_text,
                                "person_name": child["name"],
                                "role": child["role"],
                                "event_type": event_type,
                                "timestamp": timestamp,
                                "source": "manual",
                                "operator_name": user_display_name(user),
                            },
                        )
                    else:
                        record_attendance(conn, user, child["id"], event_type, source="manual", request_handler=self)
                    conn.commit()
                except ValueError as exc:
                    self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                    return
                except sqlite3.IntegrityError as exc:
                    self.send_html(html_page("Error", user, f'<div class="panel">Database error: {html.escape(str(exc))}</div>'))
                    return
                except Exception as exc:
                    self.send_html(html_page("Error", user, f'<div class="panel">Unexpected error: {html.escape(str(exc))}</div>'))
                    return
            if return_to == "mobile":
                redirect(self, f"/mobile?class={quote(child['class_name'] or 'all')}&date={quote(day_text)}&child_id={child['id']}")
            else:
                redirect(self, f"/dashboard?class={quote(child['class_name'] or 'all')}&date={quote(day_text)}&child_id={child['id']}")
            return

        if path.startswith("/child/") and path.endswith("/delete-day"):
            child_id = path.split("/")[2]
            day_text = form.get("date", [today_text()])[0]
            with connect_db() as conn:
                child = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                    (child_id, effective_project_id(conn, user)),
                ).fetchone()
                if not child:
                    self.send_error(404)
                    return
                if not can_edit_child(user):
                    self.send_error(403)
                    return
                delete_today_attendance(conn, user, child["id"], day_text, request_handler=self)
                conn.commit()
            redirect(self, f"/dashboard?class={quote(child['class_name'] or 'all')}&date={quote(day_text)}&child_id={child['id']}")
            return

        if path == "/me/event":
            if user["role"] != "teacher":
                self.send_error(403)
                return
            person_id = user["person_id"]
            event_type = form.get("event_type", [""])[0]
            if event_type not in {"checkin", "checkout"}:
                self.send_error(400)
                return
            with connect_db() as conn:
                person = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND project_id = ?",
                    (person_id, effective_project_id(conn, user)),
                ).fetchone()
                if not person or person["role"] != "teachers":
                    self.send_error(404)
                    return
                try:
                    record_attendance(conn, user, person_id, event_type, source="teacher_self", request_handler=self)
                    conn.commit()
                except ValueError as exc:
                    self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                    return
            redirect(self, "/me")
            return

        if path == "/closed-dates/add":
            if user["role"] not in MANAGE_CLOSED_DATES_ROLES:
                self.send_error(403)
                return
            day_text = form.get("date", [""])[0]
            reason = form.get("reason", [""])[0]
            closed = load_closed_dates()
            if day_text:
                closed.append(day_text)
                save_closed_dates(closed)
                with connect_db() as conn:
                    audit_request(self, conn, user["id"], "closed_date_add", "settings", object_id=day_text, details={"reason": reason})
                    conn.commit()
            redirect(self, "/closed-dates")
            return

        if path == "/closed-dates/remove":
            if user["role"] not in MANAGE_CLOSED_DATES_ROLES:
                self.send_error(403)
                return
            day_text = form.get("date", [""])[0]
            closed = [d for d in load_closed_dates() if d != day_text]
            save_closed_dates(closed)
            with connect_db() as conn:
                audit_request(self, conn, user["id"], "closed_date_remove", "settings", object_id=day_text)
                conn.commit()
            redirect(self, "/closed-dates")
            return

        if path == "/users/create":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            username = form.get("username", [""])[0].strip()
            display_name = form.get("display_name", [""])[0].strip()
            role = form.get("role", [""])[0].strip()
            password = form.get("password", [""])[0]
            classes = [part.strip() for part in form.get("classes", [""])[0].split(",") if part.strip()]
            class_name = form.get("class_name", [""])[0].strip()
            new_class_name = form.get("new_class_name", [""])[0].strip()
            if new_class_name:
                class_name = new_class_name
            photo_path = form.get("photo_path", [""])[0].strip()
            initial_status = form.get("initial_status", ["A"])[0]
            person_id_raw = form.get("person_id", [""])[0].strip()
            person_id = int(person_id_raw) if person_id_raw.isdigit() else None
            allowed_roles = creatable_roles_for_user(user)
            if not username or not display_name:
                self.send_html(html_page("Error", user, '<div class="panel"><div class="alert error">Username and display name are required.</div><a class="btn" href="/users">Retour</a></div>'), status=200)
                return
            if role not in allowed_roles:
                self.send_html(html_page("Forbidden", user, '<div class="panel"><div class="alert error">You are not allowed to create this role.</div><a class="btn" href="/users">Retour</a></div>'), status=200)
                return
            if len(password) < 8:
                self.send_html(html_page("Error", user, '<div class="panel"><div class="alert error">Initial password must be at least 8 characters.</div><a class="btn" href="/users">Retour</a></div>'), status=200)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                expected_person_role = person_role_for_user_role(role)
                if not expected_person_role:
                    person_id = None
                else:
                    if person_id:
                        person = conn.execute("SELECT * FROM persons WHERE id = ? AND role = ? AND project_id = ?", (person_id, expected_person_role, project_id)).fetchone()
                        if not person:
                            self.send_html(html_page("Error", user, '<div class="panel"><div class="alert error">Linked person does not match the selected role.</div><a class="btn" href="/users">Retour</a></div>'), status=200)
                            return
                        existing_link = conn.execute("SELECT username FROM web_users WHERE person_id = ? AND is_active = 1 AND project_id = ?", (person_id, project_id)).fetchone()
                        if existing_link and role != "children":
                            self.send_html(html_page("Error", user, f'<div class="panel"><div class="alert error">This person is already linked to user {html.escape(existing_link["username"])}.</div><a class="btn" href="/users">Retour</a></div>'), status=200)
                            return
                        if role == "children":
                            classes = [person["class_name"]] if person["class_name"] else classes
                        if not display_name:
                            display_name = person["name"]
                    else:
                        person_id = create_or_reuse_person_for_user_role(conn, role, display_name, class_name=class_name, photo_path=photo_path, project_id=project_id)
                        if role == "children" and class_name:
                            classes = [class_name]
                        if role == "children" and initial_status == "P" and person_id:
                            conn.execute(
                                "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path) VALUES (?, ?, 'children', 'checkin', ?, NULL)",
                                (person_id, display_name, now_text()),
                            )
                try:
                    create_user(conn, username, display_name, role, password, person_id=person_id, allowed_classes=classes, project_id=project_id)
                    audit_request(self, conn, user["id"], "create_user", "user", object_id=username, details={"role": role})
                    conn.commit()
                except sqlite3.IntegrityError:
                    self.send_html(html_page("Error", user, '<div class="panel">Username already exists.</div>'))
                    return
            redirect(self, "/users?created=1")
            return

        if path == "/users/delete":
            target_ids = []
            if form.get("ids"):
                target_ids = [value for value in form.get("ids", []) if value.isdigit()]
            else:
                target_id = form.get("id", [""])[0]
                if target_id.isdigit():
                    target_ids = [target_id]
            if not target_ids:
                self.send_error(400)
                return
            with connect_db() as conn:
                targets = []
                for target_id in target_ids:
                    target_user_id = int(target_id)
                    if target_user_id == user["id"]:
                        self.send_html(html_page("Error", user, '<div class="panel">You cannot delete your own account.</div>'))
                        return
                    target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                    if not target:
                        continue
                    if not can_manage_users(user, target):
                        self.send_error(403)
                        return
                    targets.append(target)
                if not targets:
                    self.send_error(404)
                    return
                for target in targets:
                    target_user_id = int(target["id"])
                    archive_deleted_user(conn, target, user)
                    conn.execute("DELETE FROM sessions WHERE user_id = ?", (target_user_id,))
                    conn.execute(
                        """
                        UPDATE web_users
                        SET is_active = 0,
                            person_id = NULL,
                            updated_at = ?
                        WHERE id = ?
                        """,
                        (now_text(), target_user_id),
                    )
                    conn.execute(
                        "UPDATE mobile_devices SET is_active = 0, last_seen_at = ? WHERE user_id = ? AND is_active = 1",
                        (now_text(), target_user_id),
                    )
                    audit_request(
                        self,
                        conn,
                        user["id"],
                        "delete_user",
                        "user",
                        object_id=target["id"],
                        details={"username": target["username"], "display_name": target["display_name"], "role": target["role"]},
                    )
                conn.commit()
            redirect(self, "/account?deleted=1")
            return

        if path == "/permanent-delete/user":
            if user["role"] != "boss":
                self.send_error(403)
                return
            target_ids = [value.strip() for value in form.get("user_id", []) if value.strip().isdigit()]
            if not target_ids:
                self.send_error(400)
                return
            if any(int(target_id) == user["id"] for target_id in target_ids):
                self.send_html(html_page("Error", user, '<div class="panel">You cannot permanently delete your own account.</div>'), status=200)
                return
            with connect_db() as conn:
                deleted_targets = []
                for target_id in target_ids:
                    target_user_id = int(target_id)
                    target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                    if not target:
                        continue
                    target_details = {"id": target_user_id, "username": target["username"], "display_name": target["display_name"], "role": target["role"]}
                    permanently_delete_user_account(conn, target_user_id)
                    deleted_targets.append(target_details)
                if not deleted_targets:
                    self.send_error(404)
                    return
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "permanent_delete_users",
                    "user",
                    object_id=",".join(str(item["id"]) for item in deleted_targets),
                    details={"targets": deleted_targets},
                )
                conn.commit()
            redirect(self, "/mobile-invitations#work-location")
            return

        if path == "/permanent-delete/group":
            if user["role"] != "boss":
                self.send_error(403)
                return
            group_names = [value.strip() for value in form.get("group_name", []) if value.strip()]
            if not group_names:
                self.send_error(400)
                return
            with connect_db() as conn:
                deleted_groups = []
                for group_name in group_names:
                    affected = permanently_delete_group(conn, group_name)
                    deleted_groups.append({"group_name": group_name, "children_unassigned": affected})
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "permanent_delete_groups",
                    "group",
                    object_id=", ".join(group_names),
                    details={"groups": deleted_groups},
                )
                conn.commit()
            redirect(self, "/mobile-invitations#work-location")
            return

        if path == "/users/reset-mobile-device":
            target_id = form.get("id", [""])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            target_user_id = int(target_id)
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (target_user_id,)).fetchone()
                if not target:
                    self.send_error(404)
                    return
                if not can_manage_users(user, target):
                    self.send_error(403)
                    return
                conn.execute("UPDATE mobile_devices SET is_active = 0, last_seen_at = ? WHERE user_id = ? AND is_active = 1", (now_text(), target_user_id))
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "reset_mobile_device",
                    "mobile_device",
                    object_id=target_user_id,
                    details={"username": target["username"], "role": target["role"]},
                )
                conn.commit()
            redirect(self, "/account")
            return

        if path == "/users/update":
            target_id = form.get("id", [""])[0]
            if not target_id.isdigit():
                self.send_error(400)
                return
            with connect_db() as conn:
                target = conn.execute("SELECT * FROM web_users WHERE id = ?", (int(target_id),)).fetchone()
                if not target:
                    self.send_error(404)
                    return
                self_edit = user["role"] == "principal" and target["id"] == user["id"]
                can_manage_target = can_manage_users(user, target)
                can_reset_password = can_reset_user_password(user, target)
                password_only = can_reset_password and not can_manage_target and not self_edit
                if not can_manage_target and not self_edit and not can_reset_password:
                    self.send_error(403)
                    return
                password = form.get("password", [""])[0]
                password_confirm = form.get("password_confirm", [""])[0]
                if (password.strip() or password_confirm.strip()) and password != password_confirm:
                    self.send_html(html_page("Error", user, '<div class="panel">Passwords do not match.</div>'))
                    return
                password_reset_only = form.get("password_reset_only", ["0"])[0] == "1"
                if password_reset_only:
                    if not can_reset_password:
                        self.send_error(403)
                        return
                    if not password.strip():
                        self.send_html(html_page("Error", user, '<div class="panel">Please enter and confirm the new password.</div>'))
                        return
                    if len(password) < 8:
                        self.send_html(html_page("Error", user, '<div class="panel">Password must be at least 8 characters.</div>'))
                        return
                    try:
                        update_user_password(conn, target["id"], password)
                    except ValueError as exc:
                        self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                        return
                    audit_request(self, conn, user["id"], "reset_user_password", "user", object_id=target["id"], details={"username": target["username"], "target_role": target["role"]})
                    conn.commit()
                    redirect(self, "/account")
                    return
                if self_edit or password_only:
                    if not password.strip():
                        self.send_html(html_page("Error", user, '<div class="panel">Please enter a new password.</div>'))
                        return
                    if len(password) < 8:
                        self.send_html(html_page("Error", user, '<div class="panel">Password must be at least 8 characters.</div>'))
                        return
                    try:
                        update_user_password(conn, target["id"], password)
                    except ValueError as exc:
                        self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                        return
                    audit_request(self, conn, user["id"], "reset_user_password", "user", object_id=target["id"], details={"username": target["username"], "target_role": target["role"]})
                    conn.commit()
                    redirect(self, "/account")
                    return
                username = form.get("username", [""])[0].strip()
                display_name = form.get("display_name", [""])[0].strip()
                role = form.get("role", [""])[0].strip()
                person_id_raw = form.get("person_id", [""])[0].strip()
                person_id = int(person_id_raw) if person_id_raw.isdigit() else None
                classes = form.get("classes", [])
                class_list = [part for part in classes if part in get_classes(conn, user)]
                class_name = form.get("class_name", [""])[0].strip()
                if not username or not display_name or role not in editable_roles_for_user(user, target):
                    self.send_error(400)
                    return
                conn.execute(
                    """
                    UPDATE web_users
                    SET username = ?, display_name = ?, role = ?, person_id = ?, allowed_classes_json = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (username, display_name, role, person_id, allowed_classes_value(class_list), now_text(), target["id"]),
                )
                if target["role"] == "children" and target["person_id"]:
                    child_class = class_name if class_name in get_classes(conn, user) else ""
                    conn.execute(
                        "UPDATE persons SET class_name = ?, updated_at = ? WHERE id = ? AND role = 'children' AND project_id = ?",
                        (child_class, now_text(), int(target["person_id"]), effective_project_id(conn, user)),
                    )
                if password.strip():
                    if not can_reset_password:
                        self.send_error(403)
                        return
                    if len(password) < 8:
                        self.send_html(html_page("Error", user, '<div class="panel">Password must be at least 8 characters.</div>'))
                        return
                    try:
                        update_user_password(conn, target["id"], password)
                    except ValueError as exc:
                        self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                        return
                    audit_request(self, conn, user["id"], "reset_user_password", "user", object_id=target["id"], details={"username": target["username"], "target_role": target["role"]})
                audit_request(self, conn, user["id"], "update_user", "user", object_id=target["id"], details={"username": username, "role": role})
                conn.commit()
            redirect(self, "/account")
            return

        if path == "/children/create":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            name = form.get("name", [""])[0].strip()
            role = form.get("role", ["children"])[0].strip()
            class_name = form.get("class_name", [""])[0].strip()
            new_class_name = form.get("new_class_name", [""])[0].strip()
            photo_path = form.get("photo_path", [""])[0].strip()
            invitation_email_input = form.get("email", [""])[0].strip()
            initial_status = form.get("initial_status", ["A"])[0]
            return_to = form.get("return_to", ["/children"])[0].strip()
            if return_to not in {"/children", "/users"}:
                return_to = "/children"
            if not name:
                self.send_html(render_children_admin(user, {}), status=200)
                return
            allowed_roles = set(creatable_roles_for_user(user))
            if role not in allowed_roles:
                self.send_html(html_page("Error", user, '<div class="panel"><div class="alert error">You are not allowed to create this role.</div><a class="btn" href="/children">Retour</a></div>'), status=200)
                return
            if new_class_name:
                class_name = new_class_name
            if role == "children" and not photo_path:
                photo_path = default_child_photo_path(name)
            if not class_name:
                class_name = ""
            try:
                with connect_db() as conn:
                    project_id = effective_project_id(conn, user)
                    if role == "children" and class_name:
                        ensure_class_name(conn, class_name, project_id=project_id)
                    person_id = create_or_reuse_person_with_role(conn, role, name, class_name=class_name, photo_path=photo_path, project_id=project_id)
                    if role == "children" and initial_status == "P":
                        conn.execute(
                            "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path) VALUES (?, ?, 'children', 'checkin', ?, NULL)",
                            (person_id, name, now_text()),
                        )
                    invitation_email = invitation_email_input or f"{slugify(name) or 'person'}-{person_id}@invitation.local"
                    token_value, _expires_at = create_mobile_invitation(
                        conn,
                        user,
                        person_id,
                        invitation_email,
                        days=30,
                        role_override=role,
                    )
                    delivery = None
                    if invitation_email_input:
                        delivery = deliver_mobile_invitation_email(conn, self, user, token_value)
                    audit_request(
                        self,
                        conn,
                        user["id"],
                        "create_person",
                        "person",
                        object_id=person_id,
                        details={"name": name, "class_name": class_name, "role": role},
                    )
                    conn.commit()
            except Exception as exc:
                self.send_html(html_page("Error", user, f'<div class="panel"><div class="alert error">{html.escape(str(exc))}</div><a class="btn" href="/children">Retour</a></div>'), status=200)
                return
            flash_token = secrets.token_urlsafe(12)
            invite_message = f"Invitation générée: {display_invite_url(token_value)}"
            if invitation_email_input and delivery:
                if delivery.get("sent"):
                    invite_message = f"Invitation envoyée à {invitation_email_input}: {display_invite_url(token_value)}"
                else:
                    invite_message = f"Invitation générée, mais l'e-mail n'a pas été envoyé: {delivery.get('error', '')}. Lien: {display_invite_url(token_value)}"
            FLASH_MESSAGES[flash_token] = ("info", invite_message)
            return_query = f"account_flash={quote(flash_token)}"
            if return_to == "/users":
                return_query += f"&created_invite={quote(token_value)}"
            redirect(self, f"{return_to}?{return_query}")
            return

        if path == "/children/group/delete":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            group_name = form.get("group_name", [""])[0].strip()
            return_to = form.get("return_to", ["/children"])[0].strip()
            if return_to not in {"/children", "/users"}:
                return_to = "/children"
            if not group_name:
                self.send_error(400)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                conn.execute("INSERT OR IGNORE INTO hidden_class_names(project_id, name) VALUES (?, ?)", (project_id, group_name))
                conn.execute("DELETE FROM class_names WHERE name = ? AND project_id = ?", (group_name, project_id))
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "hide_group_name",
                    "children",
                    object_id=group_name,
                    details={"group_name": group_name},
                )
                conn.commit()
            redirect(self, f"{return_to}?group_deleted=1")
            return

        if path == "/children/load-list":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            form, files = parse_multipart_post_data(self)
            return_to = form.get("return_to", ["/children"])[0].strip()
            if return_to not in {"/children", "/users"}:
                return_to = "/children"
            upload_values = files.get("child_list_file") or []
            if not upload_values:
                self.send_html(html_page("Error", user, '<div class="panel">Please choose a child list file.</div>'), status=200)
                return
            upload = upload_values[0]
            try:
                entries = child_list_entries_from_upload(upload.get("filename") or "", upload.get("content") or b"")
            except ValueError as exc:
                self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'), status=200)
                return
            if not entries:
                self.send_html(
                    html_page(
                        "Error",
                        user,
                        '<div class="panel">No child rows were detected in the uploaded file. Please upload the Excel version of the child list.</div>',
                    ),
                    status=200,
                )
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
            token = store_pending_child_list_import(user["id"], upload.get("filename") or "", entries, project_id=project_id)
            redirect(self, f"{return_to}?pending_import={quote(token)}")
            return

        if path == "/children/import-avatars":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            form, files = parse_multipart_post_data(self)
            return_to = form.get("return_to", ["/children"])[0].strip()
            if return_to not in {"/children", "/users"}:
                return_to = "/children"
            uploads = files.get("avatar_files") or []
            if not uploads:
                self.send_html(html_page("Error", user, '<div class="panel">Please choose avatar photo files.</div>'), status=200)
                return
            with connect_db() as conn:
                imported, skipped = import_child_avatar_uploads(conn, self, user, uploads)
                conn.commit()
            redirect(self, f"{return_to}?avatars=1&updated={imported}&skipped={skipped}")
            return

        if path == "/children/load-list/confirm":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            token = form.get("token", [""])[0].strip()
            return_to = form.get("return_to", ["/children"])[0].strip()
            if return_to not in {"/children", "/users"}:
                return_to = "/children"
            pending = get_pending_child_list_import(token, user["id"], pop=True)
            if not pending:
                self.send_html(html_page("Error", user, '<div class="panel">The import preview is no longer available. Please upload the file again.</div>'), status=200)
                return
            with connect_db() as conn:
                created, updated, skipped = apply_child_list_entries(
                    conn,
                    user["id"],
                    pending["filename"],
                    pending["entries"],
                    project_id=pending.get("project_id") or effective_project_id(conn, user),
                )
            redirect(self, f"{return_to}?imported=1&created={created}&updated={updated}&skipped={skipped}")
            return

        if path == "/children/update":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            return_to = form.get("return_to", ["/children"])[0]
            if return_to not in {"/children", "/account"}:
                return_to = "/children"
            child_id = form.get("id", [""])[0]
            if not child_id.isdigit():
                self.send_error(400)
                return
            name = form.get("name", [""])[0].strip()
            class_name = form.get("class_name", [""])[0].strip()
            photo_path = form.get("photo_path", [""])[0].strip()
            if not name:
                self.send_error(400)
                return
            if not photo_path:
                photo_path = default_child_photo_path(name)
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                ensure_class_name(conn, class_name, project_id=project_id)
                conn.execute(
                    """
                    UPDATE persons
                    SET name = ?, class_name = ?, photo_path = ?, qr_token = ?
                    WHERE id = ? AND role = 'children' AND project_id = ?
                    """,
                    (name, class_name, photo_path, f"CHILD:{name}", int(child_id), project_id),
                )
                conn.execute("UPDATE attendance SET name = ? WHERE person_id = ?", (name, int(child_id)))
                audit_request(self, conn, user["id"], "update_child", "child", object_id=child_id, details={"name": name, "class_name": class_name})
                conn.commit()
            redirect(self, return_to)
            return

        if path == "/children/update-group":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            child_id = form.get("id", [""])[0]
            if not child_id.isdigit():
                self.send_error(400)
                return
            class_name = form.get("class_name", [""])[0].strip()
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                child = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                    (int(child_id), project_id),
                ).fetchone()
                if not child:
                    self.send_error(404)
                    return
                ensure_class_name(conn, class_name, project_id=project_id)
                conn.execute(
                    "UPDATE persons SET class_name = ?, updated_at = ? WHERE id = ? AND role = 'children' AND project_id = ?",
                    (class_name, now_text(), int(child_id), project_id),
                )
                conn.execute("UPDATE web_users SET updated_at = ? WHERE person_id = ? AND project_id = ?", (now_text(), int(child_id), project_id))
                audit_request(self, conn, user["id"], "update_child_group", "child", object_id=child_id, details={"name": child["name"], "class_name": class_name})
                conn.commit()
            redirect(self, "/children?group_changed=1")
            return

        if path == "/invite-person/delete":
            if user["role"] != "boss":
                self.send_error(403)
                return
            person_id_text = form.get("person_id", [""])[0].strip()
            if not person_id_text.isdigit():
                self.send_error(400)
                return
            person_id = int(person_id_text)
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                person = conn.execute(
                    "SELECT * FROM persons WHERE id = ? AND role IN ('children', 'teachers') AND project_id = ?",
                    (person_id, project_id),
                ).fetchone()
                if not person:
                    self.send_error(404)
                    return
                active_user = conn.execute(
                    "SELECT * FROM web_users WHERE person_id = ? AND is_active = 1 AND project_id = ?",
                    (person_id, project_id),
                ).fetchone()
                if active_user:
                    flash_token = set_flash(
                        "warn",
                        "Cette personne a déjà un compte actif. Supprimez le compte depuis la liste account si nécessaire.",
                    )
                    redirect(self, f"/users?account_flash={quote(flash_token)}")
                    return
                inactive_users = conn.execute(
                    "SELECT id FROM web_users WHERE person_id = ? AND is_active = 0 AND project_id = ?",
                    (person_id, project_id),
                ).fetchall()
                for inactive_user in inactive_users:
                    conn.execute(
                        "UPDATE web_users SET person_id = NULL, updated_at = ? WHERE id = ?",
                        (now_text(), inactive_user["id"]),
                    )
                conn.execute("DELETE FROM mobile_invitations WHERE person_id = ? AND project_id = ?", (person_id, project_id))
                conn.execute("DELETE FROM attendance WHERE person_id = ?", (person_id,))
                conn.execute("DELETE FROM child_agenda_entries WHERE child_person_id = ?", (person_id,))
                conn.execute("DELETE FROM persons WHERE id = ? AND project_id = ?", (person_id, project_id))
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "delete_invite_person",
                    "person",
                    object_id=person_id,
                    details={"name": person["name"], "role": person["role"], "class_name": person["class_name"]},
                )
                conn.commit()
            redirect(self, "/users?person_deleted=1")
            return

        if path == "/children/delete":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            child_ids = []
            if form.get("ids"):
                child_ids = [value for value in form.get("ids", []) if value.isdigit()]
            else:
                child_id = form.get("id", [""])[0]
                if child_id.isdigit():
                    child_ids = [child_id]
            if not child_ids:
                self.send_error(400)
                return
            with connect_db() as conn:
                project_id = effective_project_id(conn, user)
                deleted_names = []
                deleted_ids = []
                for child_id in child_ids:
                    member = conn.execute(
                        "SELECT * FROM persons WHERE id = ? AND project_id = ?",
                        (int(child_id), project_id),
                    ).fetchone()
                    if not member or member["role"] not in {"children", "teachers", "cook", "principal", "boss"}:
                        continue
                    conn.execute("DELETE FROM attendance WHERE person_id = ?", (int(child_id),))
                    linked_user = conn.execute(
                        "SELECT * FROM web_users WHERE person_id = ? AND is_active = 1 AND project_id = ?",
                        (int(child_id), project_id),
                    ).fetchone()
                    if linked_user:
                        archive_deleted_user(conn, linked_user, user)
                        conn.execute("DELETE FROM sessions WHERE user_id = ?", (linked_user["id"],))
                        conn.execute(
                            """
                            UPDATE web_users
                            SET is_active = 0,
                                person_id = NULL,
                                updated_at = ?
                            WHERE id = ?
                            """,
                            (now_text(), linked_user["id"]),
                        )
                        conn.execute(
                            "UPDATE mobile_devices SET is_active = 0, last_seen_at = ? WHERE user_id = ? AND is_active = 1",
                            (now_text(), linked_user["id"]),
                        )
                        audit_request(
                            self,
                            conn,
                            user["id"],
                            "delete_user",
                            "user",
                            object_id=linked_user["id"],
                            details={"username": linked_user["username"], "display_name": linked_user["display_name"], "role": linked_user["role"]},
                        )
                    conn.execute("DELETE FROM persons WHERE id = ? AND project_id = ?", (int(child_id), project_id))
                    deleted_names.append(member["name"])
                    deleted_ids.append(child_id)
                if not deleted_ids:
                    self.send_error(404)
                    return
                audit_request(
                    self,
                    conn,
                    user["id"],
                    "delete_child",
                    "child",
                    object_id=",".join(deleted_ids) if len(deleted_ids) > 1 else deleted_ids[0],
                    details={"names": deleted_names, "count": len(deleted_ids)},
                )
                conn.commit()
            redirect(self, "/children?deleted=1")
            return

        self.send_error(404)


def render_password_change(user, error=None):
    body = f"""
    <div class="login-box">
      <h1 style="margin-top:0">Change password</h1>
      <p class="muted">Password rotation is required every 30 days.</p>
      {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
      <form method="post" action="/password-change" class="grid" style="gap:12px">
        <div>
          <label>Current password</label>
          <input name="current_password" type="password" autocomplete="current-password" required>
        </div>
        <div>
          <label>New password</label>
          <input name="password" type="password" autocomplete="new-password" required>
        </div>
        <div>
          <label>Confirm password</label>
          <input name="confirm" type="password" autocomplete="new-password" required>
        </div>
        <button class="btn primary" type="submit">Enregistrer le mot de passe</button>
      </form>
    </div>
    """
    return html_page("Change password", user, body)



def split_lines(value):
    return [line.strip() for line in value.replace(",", "\n").splitlines() if line.strip()]


def safe_filename(value):
    keep = []
    for ch in value:
        if ch.isalnum() or ch in {".", "-", "_", " "}:
            keep.append(ch)
    name = "".join(keep).strip().replace(" ", "_")
    return name or "file"


MAIL_PHOTO_RESIZE_THRESHOLD_BYTES = 1 * 1024 * 1024
MAIL_PHOTO_TARGET_BYTES = 1 * 1024 * 1024
MAIL_PHOTO_RESIZE_SIZES = {
    "large": 1600,
    "small": 1024,
}


def is_image_filename(filename):
    mime, _encoding = mimetypes.guess_type(filename or "")
    return bool(mime and mime.startswith("image/"))


def resize_mail_photo_attachment(upload, resize_mode):
    filename = upload.get("filename") or "attachment"
    content = upload.get("content") or b""
    if not content or not is_image_filename(filename):
        return upload
    max_side = MAIL_PHOTO_RESIZE_SIZES.get(resize_mode)
    if not max_side:
        return upload
    if len(content) <= MAIL_PHOTO_RESIZE_THRESHOLD_BYTES:
        return upload
    try:
        from PIL import Image, ImageOps
        image = Image.open(io.BytesIO(content))
        image = ImageOps.exif_transpose(image)
        ext = Path(filename).suffix.lower()
        if image.mode not in {"RGB", "L"} or ext not in {".jpg", ".jpeg"}:
            image = image.convert("RGB")
        working = image.copy()
        if max(working.size) > max_side:
            working.thumbnail((max_side, max_side), Image.LANCZOS)
        output = io.BytesIO()
        for quality in (82, 74, 66, 58, 50, 42):
            output = io.BytesIO()
            working.save(output, format="JPEG", quality=quality, optimize=True)
            if output.tell() <= MAIL_PHOTO_TARGET_BYTES:
                break
        while output.tell() > MAIL_PHOTO_TARGET_BYTES and max(working.size) > 640:
            next_side = max(640, int(max(working.size) * 0.85))
            working = image.copy()
            working.thumbnail((next_side, next_side), Image.LANCZOS)
            for quality in (74, 66, 58, 50, 42):
                output = io.BytesIO()
                working.save(output, format="JPEG", quality=quality, optimize=True)
                if output.tell() <= MAIL_PHOTO_TARGET_BYTES:
                    break
        stem = Path(filename).stem or "photo"
        resized = dict(upload)
        resized["filename"] = f"{stem}_{max_side}px.jpg"
        resized["content"] = output.getvalue()
        return resized
    except Exception:
        return upload


def mail_attachments_need_resize(uploads):
    return any(
        is_image_filename(item.get("filename") or "") and len(item.get("content") or b"") > MAIL_PHOTO_RESIZE_THRESHOLD_BYTES
        for item in uploads
    )


def ensure_user_folder(user_row):
    folder = USER_FILES_DIR / f"user_{user_row['id']}_{safe_filename(user_row['username'])}"
    folder.mkdir(parents=True, exist_ok=True)
    return folder


def parse_multipart_post_data(handler):
    content_type = handler.headers.get("Content-Type", "")
    if "multipart/form-data" not in content_type or "boundary=" not in content_type:
        return parse_post_data(handler), {}
    boundary = content_type.split("boundary=", 1)[1].strip().strip('"')
    length = int(handler.headers.get("Content-Length", "0") or 0)
    data = handler.rfile.read(length)
    delimiter = ("--" + boundary).encode("utf-8")
    form = {}
    files = {}
    for part in data.split(delimiter):
        part = part.strip(b"\r\n")
        if not part or part == b"--":
            continue
        if b"\r\n\r\n" not in part:
            continue
        header_blob, content = part.split(b"\r\n\r\n", 1)
        content = content.rstrip(b"\r\n")
        headers = header_blob.decode("utf-8", "replace").split("\r\n")
        disposition = next((h for h in headers if h.lower().startswith("content-disposition:")), "")
        attrs = {}
        for item in disposition.split(";")[1:]:
            if "=" in item:
                key, val = item.strip().split("=", 1)
                attrs[key] = val.strip().strip('"')
        name = attrs.get("name")
        if not name:
            continue
        filename = attrs.get("filename")
        if filename:
            files.setdefault(name, []).append({"filename": filename, "content": content})
        else:
            form.setdefault(name, []).append(content.decode("utf-8", "replace"))
    return form, files


def get_profile(conn, user_id):
    row = conn.execute("SELECT * FROM user_profiles WHERE user_id = ?", (user_id,)).fetchone()
    if row:
        return row
    user_row = conn.execute("SELECT * FROM web_users WHERE id = ?", (user_id,)).fetchone()
    folder = ensure_user_folder(user_row) if user_row else ""
    return {"phones_json": "[]", "emails_json": "[]", "folder_path": str(folder), "allergies": "", "notes": "", "updated_at": ""}


def manageable_users(conn, actor):
    rows = conn.execute(
        "SELECT * FROM web_users WHERE is_active = 1 AND project_id = ? ORDER BY role, display_name",
        (effective_project_id(conn, actor),),
    ).fetchall()
    if actor["role"] == "boss":
        return rows
    if actor["role"] == "principal":
        return [row for row in rows if row["role"] in {"teacher", "cook", "children"} or row["id"] == actor["id"]]
    return [row for row in rows if row["id"] == actor["id"]]


def resolve_profile_target(conn, actor, query):
    requested = query.get("user_id", [str(actor["id"])])[0]
    target_id = int(requested) if requested.isdigit() else actor["id"]
    target = conn.execute(
        "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
        (target_id, effective_project_id(conn, actor)),
    ).fetchone()
    if not target:
        return None
    if target["id"] != actor["id"] and not can_manage_users(actor, target):
        return None
    return target


def file_visible_users(conn, actor):
    if actor["role"] == "boss":
        return manageable_users(conn, actor)
    return [
        conn.execute(
            "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
            (actor["id"], effective_project_id(conn, actor)),
        ).fetchone()
    ]


def resolve_files_target(conn, actor, query):
    if actor["role"] != "boss":
        return conn.execute(
            "SELECT * FROM web_users WHERE id = ? AND project_id = ?",
            (actor["id"], effective_project_id(conn, actor)),
        ).fetchone()
    return resolve_profile_target(conn, actor, query)


def can_access_files(actor, target):
    if not target:
        return False
    if actor["role"] == "boss":
        return target["id"] == actor["id"] or can_manage_users(actor, target)
    return target["id"] == actor["id"]


def user_file_items(conn, target):
    rows = conn.execute("""
        SELECT user_files.*, uploader.display_name AS uploader_name, uploader.username AS uploader_username
        FROM user_files
        LEFT JOIN web_users AS uploader ON uploader.id = user_files.uploader_user_id
        WHERE owner_user_id = ?
        ORDER BY uploaded_at DESC, id DESC
        """, (target["id"],)).fetchall()
    items = []
    recorded_paths = set()
    for row in rows:
        item = dict(row)
        try:
            recorded_paths.add(str(Path(row["stored_path"]).resolve()).lower())
        except OSError:
            recorded_paths.add(str(row["stored_path"]).lower())
        item["file_id"] = str(row["id"])
        item["is_existing_only"] = False
        items.append(item)

    folder = ensure_user_folder(target)
    for path in sorted((p for p in folder.iterdir() if p.is_file()), key=lambda p: p.stat().st_mtime, reverse=True):
        try:
            resolved_key = str(path.resolve()).lower()
        except OSError:
            resolved_key = str(path).lower()
        if resolved_key in recorded_paths:
            continue
        try:
            uploaded_at = datetime.fromtimestamp(path.stat().st_mtime).strftime("%Y-%m-%d %H:%M:%S")
        except OSError:
            uploaded_at = ""
        items.append({
            "id": "",
            "file_id": "",
            "owner_user_id": target["id"],
            "uploader_user_id": "",
            "original_name": path.name,
            "stored_path": str(path),
            "note": "Existing folder file",
            "uploaded_at": uploaded_at,
            "uploader_name": "",
            "uploader_username": "",
            "is_existing_only": True,
        })
    return sorted(items, key=lambda item: (item["uploaded_at"] or "", str(item.get("id") or "")), reverse=True)


def mail_folder_attachment_picker_html(files):
    rows = []
    for item in files:
        token = file_path_token(item["stored_path"])
        label = item["original_name"] or Path(item["stored_path"]).name
        rows.append(
            '<label class="mail-folder-file">'
            f'<input type="checkbox" name="folder_attachments" value="{html.escape(token)}">'
            f'<span>{html.escape(label)}</span>'
            '</label>'
        )
    return f"""
        <div>
          <label>Attachments from your folder</label>
          <div class="mail-folder-files">
            {''.join(rows) or '<div class="small muted">No files in your folder.</div>'}
          </div>
        </div>
    """


def mail_photo_resize_controls_html():
    return f"""
        <input type="hidden" name="photo_resize_mode" value="large">
        <script>
        (function() {{
          function isPhoto(file) {{
            var name = (file.name || '').toLowerCase();
            return (file.type && file.type.indexOf('image/') === 0) || /\\.(jpg|jpeg|png|webp|gif)$/i.test(name);
          }}
          function loadImage(file) {{
            return new Promise(function(resolve, reject) {{
              var url = URL.createObjectURL(file);
              var img = new Image();
              img.onload = function() {{ URL.revokeObjectURL(url); resolve(img); }};
              img.onerror = function() {{ URL.revokeObjectURL(url); reject(new Error('Cannot read image')); }};
              img.src = url;
            }});
          }}
          function canvasBlob(canvas, quality) {{
            return new Promise(function(resolve) {{
              canvas.toBlob(resolve, 'image/jpeg', quality);
            }});
          }}
          async function resizePhoto(file, maxSide, targetBytes) {{
            if (!isPhoto(file) || file.size <= targetBytes) return file;
            var img = await loadImage(file);
            var scale = Math.min(1, maxSide / Math.max(img.naturalWidth || img.width, img.naturalHeight || img.height));
            var width = Math.max(1, Math.round((img.naturalWidth || img.width) * scale));
            var height = Math.max(1, Math.round((img.naturalHeight || img.height) * scale));
            var canvas = document.createElement('canvas');
            var ctx = canvas.getContext('2d');
            var qualities = [0.82, 0.74, 0.66, 0.58, 0.50, 0.42];
            var blob = null;
            while (true) {{
              canvas.width = width;
              canvas.height = height;
              ctx.drawImage(img, 0, 0, width, height);
              for (var i = 0; i < qualities.length; i++) {{
                blob = await canvasBlob(canvas, qualities[i]);
                if (blob && blob.size <= targetBytes) break;
              }}
              if (blob && blob.size <= targetBytes) break;
              if (Math.max(width, height) <= 640) break;
              var shrink = 0.85;
              width = Math.max(1, Math.round(width * shrink));
              height = Math.max(1, Math.round(height * shrink));
            }}
            if (!blob || blob.size >= file.size) return file;
            var stem = (file.name || 'photo').replace(/\\.[^.]+$/, '');
            return new File([blob], stem + '_' + maxSide + 'px.jpg', {{type: 'image/jpeg', lastModified: Date.now()}});
          }}
          document.querySelectorAll('form[action="/mail/send"]').forEach(function(form) {{
            if (form.dataset.photoResizeReady) return;
            form.dataset.photoResizeReady = '1';
            var fileInput = form.querySelector('input[type="file"][name="attachments"]');
            var targetBytes = {MAIL_PHOTO_TARGET_BYTES};
            form.addEventListener('submit', async function(event) {{
              if (form.dataset.photoResizeSubmitting === '1') return;
              if (!fileInput || !fileInput.files || !fileInput.files.length) return;
              var files = Array.prototype.slice.call(fileInput.files);
              var hasLargePhoto = files.some(function(file) {{ return file && file.size > targetBytes && isPhoto(file); }});
              if (!hasLargePhoto) return;
              event.preventDefault();
              var maxSide = 1600;
              try {{
                var dataTransfer = new DataTransfer();
                for (var i = 0; i < files.length; i++) {{
                  dataTransfer.items.add(await resizePhoto(files[i], maxSide, targetBytes));
                }}
                fileInput.files = dataTransfer.files;
                form.dataset.photoResizeSubmitting = '1';
                form.requestSubmit();
              }} catch (error) {{
                alert('This browser could not resize the selected photo. Please choose a smaller photo and send again.');
              }}
            }});
          }});
        }})();
        </script>
    """


def child_calendar_panel_html(target, events, calendar_month=None):
    target_id = int(target["id"])
    try:
        month_start = datetime.strptime(calendar_month or "", "%Y-%m").date().replace(day=1)
    except ValueError:
        month_start = date.today().replace(day=1)
    selected_month = month_start.strftime("%Y-%m")
    previous_month = (month_start - timedelta(days=1)).replace(day=1).strftime("%Y-%m")
    _, days_in_month = calendar.monthrange(month_start.year, month_start.month)
    next_month = (month_start + timedelta(days=days_in_month)).replace(day=1).strftime("%Y-%m")
    target_param = f"&user_id={target_id}"
    previous_href = f"/profile?calendar_month={quote(previous_month)}{target_param}#child-calendar"
    next_href = f"/profile?calendar_month={quote(next_month)}{target_param}#child-calendar"
    month_label = month_start.strftime("%Y-%m")
    weeks = calendar.Calendar(firstweekday=0).monthdatescalendar(month_start.year, month_start.month)
    week_head = "".join(f'<th class="child-calendar-week-head">{label}</th>' for label in ["Lun", "Mar", "Mer", "Jeu", "Ven", "Sam", "Dim"])
    events_by_day = {}
    for event in events:
        events_by_day.setdefault(event["day_text"], []).append(event)
    calendar_rows = []
    for week in weeks:
        cells = []
        for day in week:
            day_text = day.strftime("%Y-%m-%d")
            outside_style = "opacity:0.38;" if day.month != month_start.month else ""
            day_events = events_by_day.get(day_text, [])
            event_badges = []
            for event in day_events:
                note_text = f" - {event['note']}" if event["note"] else ""
                event_code = {"MALADIE": "M", "VACANCES": "V", "ABSENCE": "A", "AUTRE": "A"}.get(event["event_type"], "A")
                event_class = {"MALADIE": "maladie", "VACANCES": "vacances", "ABSENCE": "absence", "AUTRE": "absence"}.get(event["event_type"], "absence")
                event_badges.append(
                    f"""
                    <div class="child-calendar-event child-calendar-control">
                      <div class="child-calendar-event-main">
                        <span class="child-calendar-event-code {html.escape(event_class)}" title="{html.escape(event['event_type'])}">{html.escape(event_code)}</span>
                        <details class="child-calendar-action-menu">
                          <summary aria-label="Actions">...</summary>
                          <div class="child-calendar-action-panel">
                            <form method="post" action="/profile/calendar/delete" onsubmit="return confirm('Supprimer cette date ?')">
                              <input type="hidden" name="target_user_id" value="{target_id}">
                              <input type="hidden" name="event_id" value="{event['id']}">
                              <input type="hidden" name="calendar_month" value="{html.escape(selected_month)}">
                              <button class="btn red child-calendar-delete" type="submit">Supprimer</button>
                            </form>
                          </div>
                        </details>
                      </div>
                      <div class="small muted child-calendar-note">{html.escape(note_text)}</div>
                    </div>
                    """
                )
            cells.append(
                f"""
                <td class="child-calendar-day" data-date="{day_text}" style="{outside_style}">
                  <div class="child-calendar-day-number">{day.day}</div>
                  {''.join(event_badges)}
                </td>
                """
            )
        calendar_rows.append(f"<tr>{''.join(cells)}</tr>")
    event_options = "".join(
        f'<option value="{value}">{label}</option>'
        for value, label in [
            ("VACANCES", "VACANCES"),
            ("MALADIE", "MALADIE"),
            ("ABSENCE", "ABSENCE"),
            ("AUTRE", "Autre"),
        ]
    )
    return f"""
    <div class="panel" id="child-calendar">
      <div class="child-calendar-title">
        <h2>CALENDRIER</h2>
        <div class="child-calendar-nav">
          <a class="btn ghost" href="{html.escape(previous_href)}">&lt;</a>
          <strong>{html.escape(month_label)}</strong>
          <a class="btn ghost" href="{html.escape(next_href)}">&gt;</a>
        </div>
      </div>
      <style>
        .child-calendar-title {{ display:flex; align-items:center; justify-content:space-between; gap:10px; flex-wrap:wrap; }}
        .child-calendar-title h2 {{ margin:0; }}
        .child-calendar-nav {{ display:flex; align-items:center; gap:6px; }}
        .child-calendar-nav .btn {{ min-height:30px; padding:4px 9px; }}
        .child-calendar-wrap {{ margin-top:12px; overflow-x:visible; }}
        .child-calendar-table {{ width:100%; min-width:0 !important; table-layout:fixed; border-collapse:collapse; }}
        .child-calendar-week-head {{ text-align:center; padding:5px 3px; font-size:11px; }}
        .child-calendar-day {{ position:relative; height:78px; vertical-align:top; padding:5px 4px; cursor:pointer; overflow:visible; }}
        .child-calendar-day-number {{ position:relative; z-index:1; font-weight:900; font-size:16px; line-height:1; }}
        .child-calendar-event {{ position:relative; margin-top:4px; border:1px solid var(--line); border-radius:6px; padding:3px; background:#f8fafc; overflow:visible; }}
        .child-calendar-event-main {{ position:relative; z-index:3; display:flex; align-items:center; justify-content:space-between; gap:2px; background:#f8fafc; }}
        .child-calendar-event-code {{ display:inline-flex; align-items:center; justify-content:center; width:18px; height:18px; border-radius:999px; background:var(--blue-soft); color:var(--text); font-size:12px; font-weight:900; line-height:1; }}
        .child-calendar-event-code.maladie {{ background:var(--red-soft); color:#9f1239; }}
        .child-calendar-event-code.vacances {{ background:var(--green-soft); color:#0d6b39; }}
        .child-calendar-event-code.absence {{ background:var(--amber-soft); color:#8b5c00; }}
        .child-calendar-note {{ font-size:10px; line-height:1.05; }}
        .child-calendar-action-menu {{ position:relative; z-index:10; flex:0 0 auto; }}
        .child-calendar-action-menu summary {{ list-style:none; width:18px; height:18px; border:0; border-radius:999px; background:transparent; color:var(--muted); cursor:pointer; display:inline-flex; align-items:center; justify-content:center; font-size:13px; font-weight:900; line-height:1; }}
        .child-calendar-action-menu summary::-webkit-details-marker {{ display:none; }}
        .child-calendar-action-panel {{ position:absolute; top:20px; right:0; z-index:80; padding:5px; border:1px solid var(--line); border-radius:8px; background:#fff; box-shadow:0 10px 24px rgba(16,55,82,0.16); }}
        .child-calendar-delete {{ min-height:24px; padding:2px 6px; font-size:11px; line-height:1; white-space:nowrap; }}
        @media (max-width: 720px) {{
          .child-calendar-wrap {{ overflow-x:visible; }}
          .child-calendar-table {{ min-width:0 !important; }}
          .child-calendar-week-head {{ padding:3px 1px; font-size:10px; }}
          .child-calendar-day {{ height:54px; padding:3px 2px; }}
          .child-calendar-day-number {{ font-size:13px; }}
          .child-calendar-event {{ margin-top:2px; padding:1px; border-radius:4px; }}
          .child-calendar-event-code {{ width:15px; height:15px; font-size:10px; }}
          .child-calendar-action-menu summary {{ width:15px; height:15px; font-size:11px; }}
          .child-calendar-note {{ display:none; }}
          .child-calendar-delete {{ min-height:18px; padding:1px 3px; font-size:9px; }}
        }}
      </style>
      <form method="post" action="/profile/calendar/add" class="grid child-calendar-form" style="gap:10px" data-calendar-target="{target_id}">
        <input type="hidden" name="target_user_id" value="{target_id}">
        <input type="hidden" name="calendar_month" value="{html.escape(selected_month)}">
        <div class="toolbar" style="margin-bottom:0">
          <div>
            <label>Usage des dates sélectionnées</label>
            <select name="event_type">{event_options}</select>
          </div>
        </div>
      </form>
      <div class="child-calendar-wrap">
        <table class="child-calendar-table">
          <thead><tr>{week_head}</tr></thead>
          <tbody>{''.join(calendar_rows)}</tbody>
        </table>
      </div>
    </div>
    <script>
    (function() {{
      document.querySelectorAll('.child-calendar-form').forEach(function(form) {{
        const eventType = form.querySelector('select[name="event_type"]');
        const panel = form.closest('.panel');
        const dayCells = panel ? Array.prototype.slice.call(panel.querySelectorAll('.child-calendar-day')) : [];
        const dates = new Set();
        let lastSelectedDate = null;
        let submitTimer = null;
        const storageKey = 'child-calendar-event-type-' + (form.getAttribute('data-calendar-target') || '');
        if (eventType) {{
          const savedType = window.localStorage ? window.localStorage.getItem(storageKey) : '';
          if (savedType) eventType.value = savedType;
        }}
        function dateToString(date) {{
          const year = date.getFullYear();
          const month = String(date.getMonth() + 1).padStart(2, '0');
          const day = String(date.getDate()).padStart(2, '0');
          return year + '-' + month + '-' + day;
        }}
        function addDate(value) {{
          if (!value) return;
          dates.add(value);
          lastSelectedDate = value;
        }}
        function addDateRange(fromValue, toValue) {{
          const from = new Date(fromValue + 'T00:00:00');
          const to = new Date(toValue + 'T00:00:00');
          if (isNaN(from.getTime()) || isNaN(to.getTime())) {{
            addDate(toValue);
            return;
          }}
          const step = from <= to ? 1 : -1;
          const cursor = new Date(from.getTime());
          while ((step > 0 && cursor <= to) || (step < 0 && cursor >= to)) {{
            dates.add(dateToString(cursor));
            cursor.setDate(cursor.getDate() + step);
          }}
          lastSelectedDate = toValue;
        }}
        function submitSelectedDates() {{
          if (!dates.size) return;
          if (submitTimer) window.clearTimeout(submitTimer);
          submitTimer = window.setTimeout(function() {{
            form.requestSubmit();
          }}, 80);
        }}
        function renderDates() {{
          form.querySelectorAll('input[name="calendar_dates"]').forEach(function(node) {{ node.remove(); }});
          const values = Array.from(dates).sort();
          dayCells.forEach(function(cell) {{
            const selected = dates.has(cell.getAttribute('data-date'));
            cell.style.outline = selected ? '2px solid #1d4ed8' : '';
            cell.style.background = selected ? '#eef6ff' : '';
          }});
          values.forEach(function(value) {{
            const hidden = document.createElement('input');
            hidden.type = 'hidden';
            hidden.name = 'calendar_dates';
            hidden.value = value;
            form.appendChild(hidden);
          }});
        }}
        if (eventType) {{
          eventType.addEventListener('change', function() {{
            if (window.localStorage) window.localStorage.setItem(storageKey, eventType.value);
            renderDates();
          }});
        }}
        dayCells.forEach(function(cell) {{
          cell.addEventListener('click', function(event) {{
            if (event.target.closest('.child-calendar-control')) return;
            const value = cell.getAttribute('data-date');
            if (!value) return;
            if (event.shiftKey && lastSelectedDate) {{
              addDateRange(lastSelectedDate, value);
            }} else {{
              addDate(value);
            }}
            renderDates();
            submitSelectedDates();
          }});
        }});
      }});
    }})();
    </script>
    """


def render_child_home(user, query):
    calendar_month = query.get("calendar_month", [""])[0].strip()
    with connect_db() as conn:
        target = conn.execute("SELECT * FROM web_users WHERE id = ?", (user["id"],)).fetchone()
        profile = get_profile(conn, user["id"])
        files = conn.execute("""
            SELECT user_files.*, uploader.display_name AS uploader_name, uploader.username AS uploader_username
            FROM user_files
            LEFT JOIN web_users AS uploader ON uploader.id = user_files.uploader_user_id
            WHERE owner_user_id = ?
            ORDER BY uploaded_at DESC, id DESC
            LIMIT 6
            """, (user["id"],)).fetchall()
        recipients = mail_recipients(conn, user)
        inbox = conn.execute("""
            SELECT internal_messages.*, CASE WHEN COALESCE(internal_messages.external_sender_name, '') <> '' THEN internal_messages.external_sender_name ELSE sender.display_name END AS sender_name, CASE WHEN COALESCE(internal_messages.external_sender_name, '') <> '' THEN internal_messages.external_sender_contact ELSE sender.username END AS sender_username
            FROM internal_messages
            LEFT JOIN web_users AS sender ON sender.id = internal_messages.sender_user_id
            WHERE recipient_user_id = ?
            ORDER BY created_at DESC, id DESC
            LIMIT 8
            """, (user["id"],)).fetchall()
        sent = conn.execute("""
            SELECT internal_messages.*, recipient.display_name AS recipient_name, recipient.username AS recipient_username
            FROM internal_messages
            LEFT JOIN web_users AS recipient ON recipient.id = internal_messages.recipient_user_id
            WHERE sender_user_id = ? AND COALESCE(external_sender_name, '') = ''
            ORDER BY created_at DESC, id DESC
            LIMIT 8
            """, (user["id"],)).fetchall()
        calendar_events = conn.execute(
            """
            SELECT * FROM child_calendar_events
            WHERE user_id = ?
            ORDER BY day_text DESC, id DESC
            """,
            (user["id"],),
        ).fetchall()
        folder_attachment_picker = mail_folder_attachment_picker_html(user_file_items(conn, target))
    phones = "\n".join(json.loads(profile["phones_json"] or "[]"))
    emails = "\n".join(json.loads(profile["emails_json"] or "[]"))
    allergies = profile["allergies"] if "allergies" in profile.keys() else ""
    file_cards = []
    for item in files:
        url = child_card_image_url(item["stored_path"])
        is_image = item["stored_path"].lower().endswith((".png", ".jpg", ".jpeg", ".webp", ".gif"))
        thumb = f'<img src="{url}" alt="{html.escape(item["original_name"])}" style="max-width:100%;max-height:60px;border-radius:6px;border:1px solid var(--line)">' if url and is_image else '<div class="muted-box">File</div>'
        file_cards.append(f"""
        <div class="file-card">
          {thumb}
          <div style="font-weight:700;margin-top:8px">{html.escape(item['original_name'])}</div>
          <div class="small muted">Uploaded by {html.escape(item['uploader_name'] or item['uploader_username'] or 'Unknown')} at {html.escape(item['uploaded_at'])}</div>
          <div class="small">{html.escape(item['note'] or '')}</div>
          <a class="btn" style="margin-top:8px" href="{url}">Ouvrir</a>
        </div>
        """)
    recipient_checks = recipient_email_options(recipients)
    photo_resize_controls = mail_photo_resize_controls_html()
    inbox_rows = "".join(f"<tr><td>{html.escape(m['created_at'])}</td><td>{html.escape(m['sender_name'] or m['sender_username'] or '')}</td><td>{html.escape(m['subject'])}</td><td>{html.escape(m['body'])}</td></tr>" for m in inbox)
    sent_rows = "".join(f"<tr><td>{html.escape(m['created_at'])}</td><td>{html.escape(m['recipient_name'] or m['recipient_username'] or '')}</td><td>{html.escape(m['subject'])}</td><td>{html.escape(m['body'])}</td></tr>" for m in sent)
    saved_html = "" if user["role"] == "children" else ('<div class="alert info">Profile saved.</div>' if query.get("saved", ["0"])[0] == "1" else "")
    sent_html = '<div class="alert info">MESSAGE sent.</div>' if query.get("sent", ["0"])[0] == "1" else ""
    body = f"""
    {saved_html}
    {sent_html}
    <div class="grid" style="gap:16px">
      <div class="panel">
        <h2>Profile - {html.escape(target['display_name'])}</h2>
        <form method="post" action="/profile/update" class="grid profile-form" style="gap:12px;margin-top:12px">
          <input type="hidden" name="target_user_id" value="{target['id']}">
          <div><label>Phones</label><textarea name="phones" rows="2" style="resize:vertical;color:#000" placeholder="One phone per line">{html.escape(phones)}</textarea></div>
          <div><label>E-MAIL</label><textarea name="emails" rows="2" style="resize:vertical;color:#000" placeholder="One E-MAIL per line">{html.escape(emails)}</textarea></div>
          <div><label>Alimentaire ALLERGIES</label><textarea name="allergies" rows="2" style="resize:vertical;color:#000" placeholder="Allergies, restrictions alimentaires, consignes importantes">{html.escape(allergies)}</textarea></div>
          <div><label>Notes</label><textarea name="notes" rows="2" style="resize:vertical;color:#000">{html.escape(profile['notes'] or '')}</textarea></div>
          <div><button class="btn primary" type="submit">Enregistrer le profil</button></div>
        </form>
      </div>
      {child_calendar_panel_html(target, calendar_events, calendar_month)}
      <div class="panel">
        <h2>Files</h2>
        <form method="post" action="/files/upload" enctype="multipart/form-data" class="grid" style="gap:10px;margin-bottom:14px">
          <input type="hidden" name="target_user_id" value="{target['id']}">
          <div><label>Photo or file</label><input type="file" name="photo" accept="image/*,.pdf,.doc,.docx,.xls,.xlsx" multiple></div>
          <div><label>Note</label><input name="note" placeholder="Visible tag for this upload"></div>
          <div><button class="btn primary" type="submit">Téléverser</button></div>
        </form>
        <div class="file-grid">{''.join(file_cards) or '<div class="muted">No files uploaded.</div>'}</div>
      </div>
      <div class="panel">
        <h2>MESSAGE</h2>
        <form method="post" action="/mail/send" enctype="multipart/form-data" class="grid" style="gap:10px;margin-bottom:14px">
          {mail_recipient_picker_html(recipient_checks)}
          <div><label>Subject</label><input name="subject"></div>
          <div><label>Message</label><textarea name="body" rows="4"></textarea></div>
          <div><label>Attachments from this device</label><input type="file" name="attachments" multiple></div>
          {photo_resize_controls}
          {folder_attachment_picker}
          <div><button class="btn primary" type="submit">Envoyer</button></div>
        </form>
        <div class="grid two-col">
          <div><h3>MESSAGES REÇUS</h3><div class="table-wrap"><table><thead><tr><th>Time</th><th>From</th><th>Subject</th><th>MESSAGE</th></tr></thead><tbody>{inbox_rows or '<tr><td colspan="4" class="muted">No MESSAGE.</td></tr>'}</tbody></table></div></div>
          <div><h3>MESSAGES ENVOYÉS</h3><div class="table-wrap"><table><thead><tr><th>Time</th><th>To</th><th>Subject</th><th>MESSAGE</th></tr></thead><tbody>{sent_rows or '<tr><td colspan="4" class="muted">No MESSAGE sent.</td></tr>'}</tbody></table></div></div>
        </div>
      </div>
    </div>
    """
    return html_page("Child Account", user, body)


def render_profile(user, query):
    calendar_month = query.get("calendar_month", [""])[0].strip()
    flash = None
    profile_flash_token = query.get("profile_flash", [""])[0].strip()
    if profile_flash_token:
        profile_flash = FLASH_MESSAGES.pop(profile_flash_token, None)
        if profile_flash:
            flash = profile_flash
    with connect_db() as conn:
        target = resolve_profile_target(conn, user, query)
        if not target:
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to view this profile.</div>')
        profile = get_profile(conn, target["id"])
        users = manageable_users(conn, user)
        target_person = None
        calendar_events = []
        if target["role"] == "children":
            target_person = conn.execute(
                "SELECT * FROM persons WHERE id = ? AND role = 'children' AND project_id = ?",
                (target["person_id"], effective_project_id(conn, user)),
            ).fetchone() if target["person_id"] else None
            calendar_events = conn.execute(
                """
                SELECT * FROM child_calendar_events
                WHERE user_id = ?
                ORDER BY day_text DESC, id DESC
                """,
                (target["id"],),
            ).fetchall()
    phones = "\n".join(json.loads(profile["phones_json"] or "[]"))
    emails = "\n".join(json.loads(profile["emails_json"] or "[]"))
    allergies = profile["allergies"] if "allergies" in profile.keys() else ""
    allergies_html = ""
    calendar_html = ""
    if target["role"] == "children":
        allergies_html = f'<div><label>Alimentaire ALLERGIES</label><textarea name="allergies" rows="2" style="resize:vertical;color:#000" placeholder="Allergies, restrictions alimentaires, consignes importantes">{html.escape(allergies)}</textarea></div>'
        calendar_html = child_calendar_panel_html(target, calendar_events, calendar_month)
    chooser = ""
    if len(users) > 1:
        options = "".join(
            f'<option value="{u["id"]}" {"selected" if u["id"] == target["id"] else ""}>'
            f'{html.escape(u["display_name"])} ({html.escape(ROLE_LABELS.get(u["role"], u["role"]))})</option>'
            for u in users
        )
        chooser = f'<form method="get" action="/profile" class="toolbar"><div><label>Profile</label><select name="user_id" onchange="this.form.submit()">{options}</select></div></form>'
        if re.match(r"^\d{4}-\d{2}$", calendar_month or ""):
            chooser = f'<form method="get" action="/profile" class="toolbar"><input type="hidden" name="calendar_month" value="{html.escape(calendar_month)}"><div><label>Profile</label><select name="user_id" onchange="this.form.submit()">{options}</select></div></form>'
    saved_html = "" if target["role"] == "children" else ('<div class="alert info">Profile saved.</div>' if query.get("saved", ["0"])[0] == "1" else "")
    profile_heading = f"Profile - {html.escape(target['display_name'])}" if target["role"] == "children" else "Profile"
    profile_subtitle = "" if target["role"] == "children" else f"{target['display_name']} ? {ROLE_LABELS.get(target['role'], target['role'])}"
    profile_subtitle_html = f'<div class="muted">{html.escape(profile_subtitle)}</div>' if profile_subtitle else ""
    child_avatar_html = ""
    if user["role"] == "children" and target["id"] == user["id"] and target_person:
        expected_filename = expected_child_avatar_filename(target_person["name"])
        current_avatar_url = child_card_image_url(target_person["photo_path"])
        current_avatar_html = (
            f'<img src="{html.escape(current_avatar_url)}" alt="{html.escape(target_person["name"])}" style="width:72px;height:72px;object-fit:cover;border-radius:8px;border:1px solid var(--line)">'
            if current_avatar_url else
            '<div class="muted-box" style="width:72px;height:72px;display:flex;align-items:center;justify-content:center">Photo</div>'
        )
        child_avatar_html = f"""
      <form method="post" action="/profile/avatar/upload" enctype="multipart/form-data" class="child-avatar-upload">
        <div class="child-avatar-preview">{current_avatar_html}</div>
        <div class="child-avatar-fields">
          <label>Avatar enfant</label>
          <input type="file" name="avatar_file" accept=".jpg,.jpeg,image/jpeg" required>
          <div class="small muted">Nom requis: {html.escape(expected_filename)}</div>
        </div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Ajouter avatar</button></div>
      </form>
      """
    body = f"""
    {saved_html}
    <div class="panel">
      <h2>{profile_heading}</h2>
      {chooser}
      {profile_subtitle_html}
      {child_avatar_html}
      <form method="post" action="/profile/update" class="grid profile-form" style="gap:12px;margin-top:12px">
        <input type="hidden" name="target_user_id" value="{target['id']}">
        <div><label>Phones</label><textarea name="phones" rows="2" style="resize:vertical;color:#000" placeholder="One phone per line">{html.escape(phones)}</textarea></div>
        <div><label>E-MAIL</label><textarea name="emails" rows="2" style="resize:vertical;color:#000" placeholder="One E-MAIL per line">{html.escape(emails)}</textarea></div>
        {allergies_html}
        <div><label>Notes</label><textarea name="notes" rows="2" style="resize:vertical;color:#000">{html.escape(profile['notes'] or '')}</textarea></div>
        <div><button class="btn primary" type="submit">Enregistrer le profil</button></div>
      </form>
    </div>
    {calendar_html}
    <style>
      .child-avatar-upload {{ display:grid; grid-template-columns:72px minmax(0,1fr) auto; gap:10px; align-items:end; margin-top:10px; }}
      .child-avatar-fields input {{ width:100%; }}
      @media (max-width: 720px) {{
        .child-avatar-upload {{ grid-template-columns:56px minmax(0,1fr); }}
        .child-avatar-preview img, .child-avatar-preview .muted-box {{ width:56px !important; height:56px !important; }}
        .child-avatar-upload > div:last-child {{ grid-column:1 / -1; }}
        .child-avatar-upload .btn {{ width:100%; }}
      }}
    </style>
    """
    return html_page("Profile", user, body, flash=flash)


def render_files(user, query):
    with connect_db() as conn:
        target = resolve_files_target(conn, user, query)
        if not target:
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to view this folder.</div>')
        files = user_file_items(conn, target)
        users = file_visible_users(conn, user)
    chooser = ""
    if len(users) > 1:
        options = "".join(
            f'<option value="{u["id"]}" {"selected" if u["id"] == target["id"] else ""}>'
            f'{html.escape(u["display_name"])} ({html.escape(ROLE_LABELS.get(u["role"], u["role"]))})</option>'
            for u in users
        )
        chooser = f'<form method="get" action="/files" class="toolbar"><div><label>Folder owner</label><select name="user_id" onchange="this.form.submit()">{options}</select></div></form>'
    cards = []
    for item in files:
        token = file_path_token(item["stored_path"])
        url = "/media/" + token
        is_image = item["stored_path"].lower().endswith((".png", ".jpg", ".jpeg", ".webp", ".gif"))
        thumb = f'<img src="{url}" alt="{html.escape(item["original_name"])}" style="max-width:100%;max-height:70px;border-radius:6px;border:1px solid var(--line)">' if url and is_image else '<div class="muted-box">File</div>'
        uploaded_by = html.escape(item["uploader_name"] or item["uploader_username"] or ("Folder" if item.get("is_existing_only") else "Unknown"))
        delete_file_id = html.escape(str(item.get("file_id") or ""))
        delete_token = html.escape(token)
        cards.append(f"""
        <div class="file-card">
          {thumb}
          <div class="file-title">{html.escape(item['original_name'])}</div>
          <div class="small muted">Uploaded by {uploaded_by} at {html.escape(item['uploaded_at'])}</div>
          <div class="small">{html.escape(item['note'] or '')}</div>
          <div class="file-actions">
            <details class="file-action-menu">
              <summary aria-label="Actions">...</summary>
              <div class="file-action-panel">
                <a class="btn" href="{url}" target="_blank" rel="noopener">Ouvrir</a>
                <form method="post" action="/files/delete" onsubmit="return confirm('Delete this file?')" style="display:inline">
                  <input type="hidden" name="target_user_id" value="{target['id']}">
                  <input type="hidden" name="file_id" value="{delete_file_id}">
                  <input type="hidden" name="file_token" value="{delete_token}">
                  <button class="btn file-delete" type="submit">Supprimer</button>
                </form>
              </div>
            </details>
          </div>
        </div>
        """)
    deleted_html = '<div class="alert info">File deleted.</div>' if query.get("deleted", ["0"])[0] == "1" else ""
    body = f"""
    {deleted_html}
    <div class="panel">
      <h2>Files</h2>
      {chooser}
      <form method="post" action="/files/upload" enctype="multipart/form-data" class="grid" style="gap:10px;margin-bottom:14px">
        <input type="hidden" name="target_user_id" value="{target['id']}">
        <div><label>Photo or file</label><input type="file" name="photo" accept="image/*,.pdf,.doc,.docx,.xls,.xlsx" multiple></div>
        <div><label>Note</label><input name="note" placeholder="Visible tag for this upload"></div>
        <div><button class="btn primary" type="submit">Téléverser</button></div>
      </form>
      <div class="file-grid">{''.join(cards) or '<div class="muted">No files uploaded.</div>'}</div>
    </div>
    """
    return html_page("Files", user, body)


MAIL_RECIPIENT_ROLES = {
    "boss": {"boss", "principal", "teacher", "cook", "children"},
    "principal": {"boss", "principal", "teacher", "cook", "children"},
    "teacher": {"boss", "principal", "teacher", "cook", "children"},
    "cook": {"boss", "principal", "teacher", "cook", "children"},
    "children": {"principal", "teacher", "cook"},
}


def can_mail_multi_select(user):
    return user["role"] in {"boss", "principal"}


def mail_recipients(conn, user):
    rows = conn.execute(
        """
        SELECT web_users.*, COALESCE(user_profiles.emails_json, '[]') AS emails_json,
               COALESCE(persons.class_name, '') AS class_name
        FROM web_users
        LEFT JOIN user_profiles ON user_profiles.user_id = web_users.id
        LEFT JOIN persons ON persons.id = web_users.person_id
        WHERE web_users.is_active = 1
          AND web_users.project_id = ?
        ORDER BY web_users.role, web_users.display_name
        """,
        (effective_project_id(conn, user),),
    ).fetchall()
    allowed_roles = MAIL_RECIPIENT_ROLES.get(user["role"], set())
    return [row for row in rows if row["id"] != user["id"] and row["role"] in allowed_roles]


def recipient_email_options(recipients):
    rows = []
    role_order = ["principal", "boss", "teacher", "cook", "children"]
    role_rank = {role: index for index, role in enumerate(role_order)}
    sorted_recipients = sorted(
        recipients,
        key=lambda recipient: (
            role_rank.get(recipient["role"], len(role_order)),
            (recipient["display_name"] or recipient["username"] or "").lower(),
        ),
    )
    for recipient in sorted_recipients:
        try:
            emails = json.loads(recipient["emails_json"] or "[]")
        except json.JSONDecodeError:
            emails = []
        role_label = ROLE_LABELS.get(recipient["role"], recipient["role"])
        if recipient["role"] == "children":
            role_label = (recipient["class_name"] or "").strip()
            if not role_label:
                allowed_classes = safe_json_list(recipient["allowed_classes_json"])
                role_label = ", ".join(str(item) for item in allowed_classes if str(item).strip()) or ROLE_LABELS.get(recipient["role"], recipient["role"])
        display_name = recipient["display_name"] or recipient["username"]
        label = display_name
        rows.append(
            '<button type="button" class="mail-target-row" draggable="true" '
            f'data-value="{html.escape(str(recipient["id"]))}" data-label="{html.escape(label)}" '
            f'data-role="{html.escape(role_label.lower())}" data-name="{html.escape(display_name.lower())}">'
            f'<span>{html.escape(role_label)}</span>'
            f'<span>{html.escape(display_name)}</span>'
            '</button>'
        )
    return "".join(rows)


def mail_recipient_picker_html(recipient_options, group_hint="", allow_multi_select=False):
    rows = recipient_options or '<div class="mail-target-empty">No MESSAGE recipient available</div>'
    multi_flag = "1" if allow_multi_select else "0"
    return f"""
        <div class="mail-recipient-layout" data-recipient-picker data-multi-select="{multi_flag}">
          <div>
            <label>SEND TO</label>
            <div class="mail-send-to" data-send-to>
              <div class="mail-send-to-empty">No MESSAGE recipient selected.</div>
            </div>
            <div data-selected-inputs></div>
          </div>
          <div>
            <label>MESSAGE recipient</label>
            <div class="mail-target-list" data-target-recipient>
              <div class="mail-target-head"><button type="button" data-sort-recipient="role">Rôle</button><button type="button" data-sort-recipient="name">Name</button></div>
              {rows}
            </div>
            {group_hint}
          </div>
        </div>
      <script>
        (function() {{
          document.querySelectorAll('[data-recipient-picker]').forEach(function(picker) {{
            if (picker.dataset.ready) return;
            picker.dataset.ready = '1';
            var targetList = picker.querySelector('[data-target-recipient]');
            var sendTo = picker.querySelector('[data-send-to]');
            var inputs = picker.querySelector('[data-selected-inputs]');
            var form = picker.closest('form');
            var selected = new Map();
            var lastClickedRow = null;
            var allowMultiSelect = picker.dataset.multiSelect === '1';
            function targetRows() {{
              return Array.prototype.slice.call(targetList.querySelectorAll('.mail-target-row'));
            }}
            function sortRecipients(key) {{
              var currentKey = targetList.dataset.sortKey || '';
              var currentDir = targetList.dataset.sortDir || 'asc';
              var nextDir = currentKey === key && currentDir === 'asc' ? 'desc' : 'asc';
              var rows = targetRows();
              rows.sort(function(a, b) {{
                var av = (a.dataset[key] || '').toLowerCase();
                var bv = (b.dataset[key] || '').toLowerCase();
                if (av < bv) return nextDir === 'asc' ? -1 : 1;
                if (av > bv) return nextDir === 'asc' ? 1 : -1;
                var an = (a.dataset.name || '').toLowerCase();
                var bn = (b.dataset.name || '').toLowerCase();
                if (an < bn) return -1;
                if (an > bn) return 1;
                return 0;
              }});
              rows.forEach(function(row) {{ targetList.appendChild(row); }});
              targetList.dataset.sortKey = key;
              targetList.dataset.sortDir = nextDir;
              lastClickedRow = null;
            }}
            function render() {{
              sendTo.innerHTML = '';
              inputs.innerHTML = '';
              if (!selected.size) {{
                var empty = document.createElement('div');
                empty.className = 'mail-send-to-empty';
                empty.textContent = 'No MESSAGE recipient selected.';
                sendTo.appendChild(empty);
                return;
              }}
              selected.forEach(function(label, value) {{
                var button = document.createElement('button');
                button.type = 'button';
                button.className = 'mail-recipient-pill';
                button.textContent = label;
                button.title = 'Click to remove';
                button.addEventListener('click', function() {{
                  selected.delete(value);
                  render();
                }});
                sendTo.appendChild(button);
                var input = document.createElement('input');
                input.type = 'hidden';
                input.name = 'recipient_emails';
                input.value = value;
                inputs.appendChild(input);
              }});
            }}
            function addRows(rows) {{
              if (!allowMultiSelect) {{
                selected.clear();
                rows = rows.length ? [rows[rows.length - 1]] : [];
              }}
              rows.forEach(function(row) {{
                if (!row || !row.dataset.value) return;
                selected.set(row.dataset.value, row.dataset.label || row.textContent.trim());
              }});
              render();
            }}
            function addRow(row) {{
              addRows([row]);
            }}
            targetList.addEventListener('click', function(event) {{
              var sortButton = event.target.closest('[data-sort-recipient]');
              if (sortButton) {{
                sortRecipients(sortButton.dataset.sortRecipient);
                return;
              }}
              var row = event.target.closest('.mail-target-row');
              if (!row) return;
              if (allowMultiSelect && event.shiftKey && lastClickedRow) {{
                var rows = targetRows();
                var start = rows.indexOf(lastClickedRow);
                var end = rows.indexOf(row);
                if (start !== -1 && end !== -1) {{
                  var from = Math.min(start, end);
                  var to = Math.max(start, end);
                  addRows(rows.slice(from, to + 1));
                }} else {{
                  addRow(row);
                }}
              }} else {{
                addRow(row);
              }}
              lastClickedRow = row;
            }});
            targetList.addEventListener('dragstart', function(event) {{
              var row = event.target.closest('.mail-target-row');
              if (!row) return;
              event.dataTransfer.setData('text/plain', row.dataset.value);
              event.dataTransfer.effectAllowed = 'copy';
            }});
            sendTo.addEventListener('dragover', function(event) {{
              event.preventDefault();
              event.dataTransfer.dropEffect = 'copy';
            }});
            sendTo.addEventListener('drop', function(event) {{
              event.preventDefault();
              var value = event.dataTransfer.getData('text/plain');
              var row = targetList.querySelector('[data-value="' + CSS.escape(value) + '"]');
              addRow(row);
            }});
            if (form) {{
              form.addEventListener('submit', function(event) {{
                if (!selected.size) {{
                  event.preventDefault();
                  alert('Please choose at least one MESSAGE recipient.');
                }} else if (!allowMultiSelect && selected.size > 1) {{
                  event.preventDefault();
                  alert('Please choose only one MESSAGE recipient.');
                }}
              }});
            }}
          }});
        }})();
        </script>
    """

def render_mail(user, query, error=None):
    with connect_db() as conn:
        recipients = mail_recipients(conn, user)
        inbox = conn.execute("""
            SELECT internal_messages.*, CASE WHEN COALESCE(internal_messages.external_sender_name, '') <> '' THEN internal_messages.external_sender_name ELSE sender.display_name END AS sender_name, CASE WHEN COALESCE(internal_messages.external_sender_name, '') <> '' THEN internal_messages.external_sender_contact ELSE sender.username END AS sender_username
            FROM internal_messages
            LEFT JOIN web_users AS sender ON sender.id = internal_messages.sender_user_id
            WHERE recipient_user_id = ?
            ORDER BY created_at DESC, id DESC
            LIMIT 50
            """, (user["id"],)).fetchall()
        sent = conn.execute("""
            SELECT internal_messages.*, recipient.display_name AS recipient_name, recipient.username AS recipient_username
            FROM internal_messages
            LEFT JOIN web_users AS recipient ON recipient.id = internal_messages.recipient_user_id
            WHERE sender_user_id = ? AND COALESCE(external_sender_name, '') = ''
            ORDER BY created_at DESC, id DESC
            LIMIT 30
            """, (user["id"],)).fetchall()
        folder_attachment_picker = mail_folder_attachment_picker_html(user_file_items(conn, user))
        conn.execute(
            "UPDATE internal_messages SET read_at = ? WHERE recipient_user_id = ? AND read_at IS NULL",
            (now_text(), user["id"]),
        )
    recipient_checks = recipient_email_options(recipients)
    photo_resize_controls = mail_photo_resize_controls_html()
    inbox_rows = "".join(f"<tr><td>{html.escape(m['created_at'])}</td><td>{html.escape(m['sender_name'] or m['sender_username'] or '')}</td><td>{html.escape(m['subject'])}</td><td>{html.escape(m['body'])}</td></tr>" for m in inbox)
    sent_rows = "".join(f"<tr><td>{html.escape(m['created_at'])}</td><td>{html.escape(m['recipient_name'] or m['recipient_username'] or '')}</td><td>{html.escape(m['subject'])}</td><td>{html.escape(m['body'])}</td></tr>" for m in sent)
    group_hint = '<div class="small muted">.</div>' if user["role"] == "principal" else ""
    sent_html = '<div class="alert info">MESSAGE sent.</div>' if query.get("sent", ["0"])[0] == "1" else ""
    body = f"""
    {sent_html}
    {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
    <div class="panel">
      <h2>MESSAGE</h2>
      <form method="post" action="/mail/send" enctype="multipart/form-data" class="grid" style="gap:10px">
        {mail_recipient_picker_html(recipient_checks, group_hint, can_mail_multi_select(user))}
        <div><label>Subject</label><input name="subject"></div>
        <div><label>Message</label><textarea name="body" rows="5"></textarea></div>
        <div><label>Attachments from this device</label><input type="file" name="attachments" multiple></div>
        {photo_resize_controls}
        {folder_attachment_picker}
        <div><button class="btn primary" type="submit">Envoyer</button></div>
      </form>
    </div>
    <div class="grid two-col child-mobile-mail-history" style="margin-top:16px">
      <div class="panel"><h3>MESSAGES REÇUS</h3><div class="table-wrap"><table><thead><tr><th>Time</th><th>From</th><th>Subject</th><th>MESSAGE</th></tr></thead><tbody>{inbox_rows or '<tr><td colspan="4" class="muted">No MESSAGE.</td></tr>'}</tbody></table></div></div>
      <div class="panel"><h3>MESSAGES ENVOYÉS</h3><div class="table-wrap"><table><thead><tr><th>Time</th><th>To</th><th>Subject</th><th>MESSAGE</th></tr></thead><tbody>{sent_rows or '<tr><td colspan="4" class="muted">No MESSAGE sent.</td></tr>'}</tbody></table></div></div>
    </div>
    """
    return html_page("MESSAGE", user, body)

def render_me(user, query):
    if user["role"] != "teacher":
        return html_page("Forbidden", user, '<div class="panel">This page is for teachers only.</div>')
    with connect_db() as conn:
        person_id = user["person_id"]
        person = conn.execute("SELECT * FROM persons WHERE id = ?", (person_id,)).fetchone()
        if not person:
            return html_page("Not Found", user, '<div class="panel">Linked teacher profile not found.</div>')
        rows = latest_attendance_rows(conn, person_id, 20)
        today = today_text()
        status = "P" if current_child_present(conn, person_id, today) else "A"
        rows_html = "".join(
            f"<tr><td>{html.escape(r['timestamp'])}</td><td>{html.escape(r['event_type'])}</td></tr>"
            for r in rows
        )
    body = f"""
    <div class="grid two-col">
      <div class="panel">
        <h2>My Attendance</h2>
        <div class="muted">{html.escape(person['name'])}</div>
        <div class="badge {'present' if status == 'P' else 'absent'}" style="margin:12px 0">{status_label(status)}</div>
        <form method="post" action="/me/event" class="btn-row">
          <button class="btn green" type="submit" name="event_type" value="checkin">Arrivée</button>
          <button class="btn gray" type="submit" name="event_type" value="checkout">Départ</button>
        </form>
      </div>
      <div class="panel">
        <h3>Recent records</h3>
        <div class="table-wrap">
          <table>
            <thead><tr><th>Timestamp</th><th>Event</th></tr></thead>
            <tbody>{rows_html or '<tr><td colspan=\"2\" class=\"muted\">No records</td></tr>'}</tbody>
          </table>
        </div>
      </div>
    </div>
    """
    return html_page("My Attendance", user, body)


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Kindergarten attendance web app")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--port", type=int, default=DEFAULT_PORT)
    args = parser.parse_args()
    init_db()
    closeout_stop_event = threading.Event()
    closeout_thread = threading.Thread(target=teacher_daily_closeout_worker, args=(closeout_stop_event,), daemon=True)
    closeout_thread.start()
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    if args.host == "0.0.0.0":
        print(f"Serving on http://0.0.0.0:{args.port}", flush=True)
        print("Access URLs:", flush=True)
        for url in access_urls(args.port):
            print(f"  {url}", flush=True)
    else:
        print(f"Serving on http://{args.host}:{args.port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        closeout_stop_event.set()
        server.server_close()


if __name__ == "__main__":
    main()










