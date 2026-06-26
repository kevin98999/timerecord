import base64
import calendar
import hashlib
import hmac
import html
import json
import mimetypes
import os
import io
import secrets
import shutil
import sqlite3
import sys
import socket
import zipfile
from datetime import datetime, timedelta, date
from http import cookies
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urlparse


def app_base_dir():
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = app_base_dir()
DATA_DIR = BASE_DIR / "data"
CHILDREN_DIR = BASE_DIR / "children"
DB_PATH = DATA_DIR / "attendance.db"
WORK_DB_PATH = DATA_DIR / "attendance_web.db"
DAILY_EXPORT_DIR = DATA_DIR / "daily_exports"
FORM_DIR = DATA_DIR / "form"
SETTINGS_PATH = DATA_DIR / "settings.json"
SECRET_PATH = DATA_DIR / "webapp_secret.txt"
SESSION_TTL_DAYS = 7
PASSWORD_ROTATION_DAYS = 30
DEFAULT_PORT = 8000
DEFAULT_HOST = "0.0.0.0"

ROLE_LABELS = {
    "teacher": "Teacher",
    "principal": "Principal",
    "boss": "Boss",
    "cook": "Cook",
}

EVENT_LABELS = {
    "checkin": "Check In",
    "checkout": "Check Out",
}

EDIT_ROLES = {"teacher", "principal", "boss"}
MANAGE_USERS_ROLES = {"principal", "boss"}
MANAGE_ALL_USERS_ROLES = {"boss"}
MANAGE_CLOSED_DATES_ROLES = {"principal", "boss"}
VIEW_ALL_CLASSES_ROLES = {"principal", "boss", "cook"}


def now_text():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def today_text():
    return datetime.now().strftime("%Y-%m-%d")


def ensure_dirs():
    DATA_DIR.mkdir(exist_ok=True)
    DAILY_EXPORT_DIR.mkdir(exist_ok=True)
    FORM_DIR.mkdir(exist_ok=True)


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
            CREATE TABLE IF NOT EXISTS web_users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
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
            CREATE TABLE IF NOT EXISTS sessions (
                token TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                expires_at TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES web_users(id) ON DELETE CASCADE
            )
            """
        )
        columns = {row["name"] for row in conn.execute("PRAGMA table_info(web_users)").fetchall()}
        # Older SQLite files may not have these columns.
        for column_sql in [
            ("allowed_classes_json", "TEXT NOT NULL DEFAULT '[]'"),
            ("is_active", "INTEGER NOT NULL DEFAULT 1"),
            ("next_password_change_at", "TEXT"),
            ("password_fingerprint", "TEXT"),
        ]:
            name, ddl = column_sql
            if name not in columns:
                conn.execute(f"ALTER TABLE web_users ADD COLUMN {name} {ddl}")
        seed_default_users(conn)


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


def create_user(conn, username, display_name, role, password, person_id=None, allowed_classes=None):
    fingerprint = password_fingerprint(password)
    now = now_text()
    next_change = (datetime.now() + timedelta(days=PASSWORD_ROTATION_DAYS)).strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        """
        INSERT INTO web_users(
            username, display_name, role, person_id, password_hash, password_fingerprint,
            password_changed_at, next_password_change_at, allowed_classes_json,
            is_active, created_at, updated_at
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?, ?)
        """,
        (
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


def get_user_by_id(conn, user_id):
    return conn.execute("SELECT * FROM web_users WHERE id = ?", (user_id,)).fetchone()


def get_children(conn, user, class_name=None):
    params = []
    where = ["role = 'children'"]
    if class_name and class_name != "all":
        where.append("class_name = ?")
        params.append(class_name)
    if user["role"] not in VIEW_ALL_CLASSES_ROLES:
        allowed = json.loads(user["allowed_classes_json"] or "[]")
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


def get_classes(conn):
    rows = conn.execute("SELECT name FROM class_names ORDER BY rowid").fetchall()
    return [row["name"] for row in rows]


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
               attendance.event_type, COALESCE(attendance.snapshot_path, '')
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        {date_filter}
        ORDER BY attendance.timestamp DESC
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


def build_presence_summary_rows(rows):
    child_events = []
    for person_id, name, role, class_name, timestamp, event_type, *_extra in rows:
        if role != "children":
            continue
        try:
            event_time = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S")
        except (TypeError, ValueError):
            continue
        child_events.append(
            {
                "person_id": person_id,
                "name": name,
                "class_name": class_name or "Unassigned",
                "time": event_time,
                "event_type": event_type,
            }
        )

    if not child_events:
        return []

    summary_rows = []
    dates = sorted({event["time"].date() for event in child_events})
    events_by_date = {
        date: sorted(
            (event for event in child_events if event["time"].date() == date),
            key=lambda event: event["time"],
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


def generate_acceo_detail_attendance_pdf(start_date):
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError("PyMuPDF is required to generate PDF reports.") from exc

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report()
    checkins = load_child_checkin_dates(start_date, end_date)
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

        draw_text(page, 410, 767, f"Imprimé le {acceo_date_text(now.date())} à {now.strftime('%I:%M %p').lstrip('0')}", size=8)
        draw_text(page, 515, 780, "Page 1 de 1", size=8)
        draw_text(page, 331, 790, "Ce rapport a été produit avec ACCEO Services de garde.", size=8)

    try:
        return doc.tobytes()
    finally:
        doc.close()


def generate_acceo_summary_attendance_pdf(start_date):
    try:
        import fitz
    except ImportError as exc:
        raise RuntimeError("PyMuPDF is required to generate PDF reports.") from exc

    start_date = monday_for_date(start_date)
    week_starts = [start_date + timedelta(days=7 * index) for index in range(4)]
    end_date = start_date + timedelta(days=27)
    children = load_children_for_acceo_report()
    checkins = load_child_checkin_dates(start_date, end_date)
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

        draw_text(page, 610, 574, f"Imprimé le {acceo_date_text(now.date())} à {now.strftime('%I:%M %p').lstrip('0')}", size=8)
        draw_text(page, 710, 590, "Page 1 de 1", size=8)
        draw_text(page, 530, 605, "Ce rapport a été produit avec ACCEO Services de garde.", size=8)

    try:
        return doc.tobytes()
    finally:
        doc.close()


def get_attendance_rows(conn, person_id, day_text):
    return conn.execute(
        """
        SELECT id, event_type, timestamp
        FROM attendance
        WHERE person_id = ? AND timestamp LIKE ?
        ORDER BY timestamp ASC, id ASC
        """,
        (person_id, f"{day_text}%"),
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


def dashboard_version(conn, children, day_text):
    if not children:
        return 0
    ids = [child["id"] for child in children]
    placeholders = ",".join("?" for _ in ids)
    row = conn.execute(
        f"""
        SELECT COALESCE(MAX(id), 0) AS max_id
        FROM attendance
        WHERE person_id IN ({placeholders}) AND timestamp LIKE ?
        """,
        (*ids, f"{day_text}%"),
    ).fetchone()
    return int(row["max_id"] or 0)


def child_card_image_url(photo_path):
    if not photo_path:
        return None
    return "/media/" + base64.urlsafe_b64encode(str(Path(photo_path).resolve()).encode("utf-8")).decode("ascii").rstrip("=")


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


def status_label(status):
    return {"P": "Present", "A": "Absence", "F": "Closed"}.get(status, status)


def css():
    return """
    <style>
    :root {
      --bg: #f4f7fb;
      --panel: #ffffff;
      --text: #16202a;
      --muted: #5f6b7a;
      --line: #dbe4ee;
      --blue: #1f6feb;
      --green: #138a4a;
      --gray: #697582;
      --amber: #b26b00;
      --red: #b42318;
      --nav: #10233d;
      --navText: #eff4fb;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      font-family: Segoe UI, Arial, sans-serif;
      background: var(--bg);
      color: var(--text);
    }
    a { color: var(--blue); text-decoration: none; }
    a:hover { text-decoration: underline; }
    .topbar {
      background: var(--nav);
      color: var(--navText);
      padding: 12px 18px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      flex-wrap: wrap;
    }
    .brand {
      font-size: 18px;
      font-weight: 700;
      letter-spacing: 0;
    }
    .nav {
      display: flex;
      gap: 10px;
      flex-wrap: wrap;
      align-items: center;
    }
    .nav a, .nav button {
      color: var(--navText);
      background: rgba(255,255,255,0.10);
      border: 1px solid rgba(255,255,255,0.18);
      padding: 8px 12px;
      border-radius: 6px;
      cursor: pointer;
      font-size: 14px;
      text-decoration: none;
    }
    .wrap {
      max-width: 1600px;
      margin: 0 auto;
      padding: 18px;
    }
    .grid {
      display: grid;
      gap: 16px;
    }
    .two-col {
      grid-template-columns: minmax(0, 1.7fr) minmax(360px, 1fr);
      align-items: start;
    }
    .panel {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 14px;
      box-shadow: 0 1px 1px rgba(16, 35, 61, 0.04);
    }
    .panel h2, .panel h3 {
      margin: 0 0 10px;
      font-size: 18px;
    }
    .muted { color: var(--muted); }
    .stats {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
      gap: 10px;
      margin-bottom: 14px;
    }
    .stat {
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 12px;
      background: #fff;
    }
    .stat .value { font-size: 22px; font-weight: 700; margin-top: 4px; }
    .toolbar {
      display: flex;
      flex-wrap: wrap;
      gap: 10px;
      align-items: end;
      margin-bottom: 12px;
    }
    label { display: block; font-size: 12px; color: var(--muted); margin-bottom: 4px; }
    input, select, textarea {
      width: 100%;
      border: 1px solid #bcc7d4;
      border-radius: 6px;
      padding: 9px 10px;
      font-size: 14px;
      background: white;
    }
    input[type="checkbox"] { width: auto; }
    .btn {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      gap: 6px;
      border: 1px solid transparent;
      border-radius: 6px;
      padding: 9px 12px;
      font-size: 14px;
      cursor: pointer;
      background: #dbe7f5;
      color: #10233d;
      text-decoration: none;
      white-space: nowrap;
    }
    .btn.primary { background: var(--blue); color: white; }
    .btn.green { background: #0e9f6e; color: white; }
    .btn.gray { background: #e6ebf2; color: #394b59; }
    .btn.red { background: var(--red); color: white; }
    .btn.amber { background: #d99a2b; color: white; }
    .btn.ghost { background: transparent; border-color: var(--line); }
    .btn-row { display: flex; gap: 8px; flex-wrap: wrap; }
    .action-panel {
      display: grid;
      grid-template-columns: 1fr;
      gap: 10px;
      align-items: start;
      margin-bottom: 12px;
    }
    .action-card {
      border: 1px solid var(--line);
      border-radius: 8px;
      background: #fff;
      padding: 10px;
    }
    .dashboard-filters {
      display: grid;
      grid-template-columns: repeat(4, minmax(130px, 1fr));
      gap: 10px;
      align-items: end;
    }
    .selected-action-card {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      flex-wrap: wrap;
    }
    .selected-action-meta {
      min-width: 180px;
    }
    .action-buttons {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      align-items: center;
    }
    .action-buttons .btn {
      min-width: 110px;
      justify-content: center;
    }
    .btn:disabled {
      background: #e7edf5 !important;
      color: #9aa7b6 !important;
      border-color: #d6deea !important;
      cursor: not-allowed;
      opacity: 1;
    }
    .cards {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(150px, 1fr));
      gap: 6px;
    }
    .card {
      border: 1px solid var(--line);
      border-radius: 8px;
      overflow: hidden;
      background: #fff;
      display: grid;
      grid-template-columns: 52px minmax(0, 1fr);
      align-items: center;
      min-height: 0;
      padding: 5px;
      gap: 6px;
    }
.card.present { border-color: #8fd3a5; background: #f2fbf5; }
.card.absent, .card.checkedout, .card.closed { background: #f7f8fa; color: #8b97a5; }
    .card.closed { background: #fff8e8; border-color: #f0d38a; }
    .card.selected { outline: 3px solid #1f6feb; outline-offset: 0; }
.card.absent .photo,
.card.checkedout .photo,
.card.closed .photo {
  filter: grayscale(1) opacity(0.42);
}
.card.absent .name,
.card.checkedout .name,
.card.closed .name,
.card.absent .class-tag,
.card.checkedout .class-tag,
.card.closed .class-tag,
.card.absent .small,
.card.checkedout .small,
.card.closed .small {
  color: #8b97a5;
}
    .count-strip {
      display: flex;
      flex-wrap: wrap;
      gap: 3px;
      margin: 0 0 6px;
    }
    .count-chip {
      border: 1px solid var(--line);
      border-radius: 999px;
      padding: 1px 6px;
      font-size: 11px;
      line-height: 1.1;
      background: #fff;
      color: var(--muted);
    }
    .count-chip.strong { color: var(--text); font-weight: 700; }
    .card .photo {
      width: 48px;
      height: 48px;
      background: #f2fbf5;
      display: flex;
      align-items: center;
      justify-content: center;
      overflow: hidden;
      padding: 0;
      border-radius: 50%;
    }
    .card .photo img {
      width: 48px;
      height: 48px;
      border-radius: 50%;
      object-fit: cover;
      display: block;
      border: 2px solid #cde0f6;
      background: #e8f5ef;
    }
    .card .content { padding: 0; display: grid; gap: 2px; min-width: 0; }
    .name { font-weight: 700; line-height: 1.05; font-size: 12px; overflow-wrap: anywhere; }
    .class-tag, .badge {
      display: inline-flex;
      width: fit-content;
      border-radius: 999px;
      padding: 0 4px;
      font-size: 10px;
      line-height: 1;
      border: 1px solid transparent;
    }
    .class-tag { margin-top: 0; }
    .badge.present { background: #d8f5e4; color: #0d6b39; }
.badge.absent { background: #eef2f6; color: #52616e; }
.badge.closed { background: #fff2c8; color: #8b5c00; }
    .badge.checkedout { background: #eef2f6; color: #52616e; }
    .badge.warn { background: #fff2f2; color: #9f1239; }
    .selected-child-head {
      display: grid;
      grid-template-columns: auto 1fr;
      gap: 10px;
      align-items: center;
      margin-bottom: 10px;
    }
    .selected-child-head img {
      width: 64px;
      height: 64px;
      object-fit: cover;
      border-radius: 8px;
      border: 1px solid var(--line);
    }
    .selected-child-head .badge { margin-top: 6px; }
    .table-wrap { overflow-x: auto; }
    table { width: 100%; border-collapse: collapse; }
    th, td {
      border-bottom: 1px solid var(--line);
      padding: 8px 10px;
      text-align: left;
      vertical-align: top;
      font-size: 14px;
    }
    th { background: #f7f9fc; position: sticky; top: 0; z-index: 1; }
    .fiche th, .fiche td { text-align: center; min-width: 42px; }
    .fiche .name-col { text-align: left; min-width: 220px; }
    .fiche .week-col { min-width: 100px; }
    .pill {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      min-width: 28px;
      height: 28px;
      border-radius: 999px;
      font-weight: 700;
    }
    .pill.P { background: #d8f5e4; color: #0d6b39; }
    .pill.A { background: #eef2f6; color: #52616e; }
    .pill.F { background: #fff2c8; color: #8b5c00; }
    .login-box {
      max-width: 420px;
      margin: 72px auto;
      background: white;
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 20px;
    }
    .alert {
      padding: 10px 12px;
      border-radius: 6px;
      margin-bottom: 12px;
      border: 1px solid;
    }
    .alert.info { background: #eef6ff; border-color: #bcd7ff; color: #0e3a66; }
    .alert.warn { background: #fff8e6; border-color: #f0d38a; color: #7a4a00; }
    .alert.error { background: #fff0f0; border-color: #f5b0b0; color: #921919; }
    .small { font-size: 12px; }
    .card-link {
      display: block;
      color: inherit;
      text-decoration: none;
      height: auto;
    }
.auto-hide { display: none !important; }
.right { text-align: right; }
.nowrap { white-space: nowrap; }
    .muted-box {
      padding: 18px;
      background: #f7f9fc;
      border: 1px solid var(--line);
      border-radius: 6px;
    }
    .user-grid {
      display: grid;
      grid-template-columns: 1fr 1fr 1fr;
      gap: 8px;
    }
    @media (max-width: 1180px) {
      .two-col, .user-grid { grid-template-columns: 1fr; }
    }
    @media print {
      .topbar, .no-print { display: none !important; }
      body { background: white; }
      .wrap { max-width: none; padding: 0; }
      .panel { border: none; box-shadow: none; }
    }
    </style>
    """


def html_page(title, user, body, flash=None):
    nav = []
    if user:
        nav.append('<a href="/dashboard">Dashboard</a>')
        if user["role"] in {"principal", "boss"}:
            nav.append('<a href="/reports">4-Week Fiche</a>')
        if user["role"] == "boss":
            nav.append('<a href="/audit">Logs</a>')
        if user["role"] in MANAGE_CLOSED_DATES_ROLES:
            nav.append('<a href="/closed-dates">Closed Dates</a>')
        if user["role"] in MANAGE_USERS_ROLES:
            nav.append('<a href="/users">Users</a>')
            nav.append('<a href="/children">Children</a>')
        nav.append(f'<form method="post" action="/logout" style="display:inline"><button type="submit">Logout</button></form>')
    header = ""
    if user:
        header = f"""
        <div class="topbar">
          <div class="brand">Kindergarten Attendance Web</div>
          <div class="nav">
            {''.join(nav)}
          </div>
          <div class="small">{html.escape(user['display_name'])} · {ROLE_LABELS.get(user['role'], user['role'])}</div>
        </div>
        """
    else:
        header = """
        <div class="topbar">
          <div class="brand">Kindergarten Attendance Web</div>
        </div>
        """
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
      {css()}
    </head>
    <body>
      {header}
      <div class="wrap">
        {alert_html}
        {body}
      </div>
    </body>
    </html>"""


def login_page(error=None):
    body = f"""
    <div class="login-box">
      <h1 style="margin-top:0">Sign in</h1>
      <p class="muted">Use the seeded local accounts to start. Change passwords after the first login.</p>
      {f'<div class="alert error">{html.escape(error)}</div>' if error else ''}
      <form method="post" action="/login" class="grid" style="gap:12px">
        <div>
          <label>Username</label>
          <input name="username" autocomplete="username" required>
        </div>
        <div>
          <label>Password</label>
          <input name="password" type="password" autocomplete="current-password" required>
        </div>
        <button class="btn primary" type="submit">Sign in</button>
      </form>
      <div class="muted-box small" style="margin-top:16px">
        Defaults: <b>boss / Boss123!</b>, <b>principal / Principal123!</b>, <b>cook / Cook123!</b>, <b>ky / Teacher123!</b>
      </div>
    </div>
    """
    return html_page("Sign in", None, body)


def session_cookie_header(token):
    c = cookies.SimpleCookie()
    c["session"] = token
    c["session"]["path"] = "/"
    c["session"]["httponly"] = True
    c["session"]["samesite"] = "Lax"
    return c.output(header="").strip()


def clear_session_cookie():
    c = cookies.SimpleCookie()
    c["session"] = ""
    c["session"]["path"] = "/"
    c["session"]["httponly"] = True
    c["session"]["samesite"] = "Lax"
    c["session"]["max-age"] = 0
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
    all_classes = get_classes(conn)
    if user["role"] in VIEW_ALL_CLASSES_ROLES:
        return all_classes
    allowed = json.loads(user["allowed_classes_json"] or "[]")
    return [c for c in all_classes if c in allowed]


def can_edit_child(user):
    return user["role"] in EDIT_ROLES


def can_view_all_classes(user):
    return user["role"] in VIEW_ALL_CLASSES_ROLES


def can_manage_users(actor, target):
    if actor["role"] in MANAGE_ALL_USERS_ROLES:
        return True
    if actor["role"] != "principal":
        return False
    return target["role"] in {"teacher", "cook"}


def password_is_expired(user):
    try:
        due = datetime.strptime(user["next_password_change_at"], "%Y-%m-%d %H:%M:%S")
    except Exception:
        return True
    return datetime.now() >= due


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
    return (datetime.now() - last).total_seconds() < 30 * 60


def record_attendance(conn, actor, person_id, event_type, source="web"):
    person = conn.execute("SELECT id, name, role FROM persons WHERE id = ?", (person_id,)).fetchone()
    if not person:
        raise ValueError("Child or teacher not found")
    if person["role"] == "teachers" and recent_teacher_event_block(conn, person_id, event_type):
        raise ValueError("Teacher attendance changes are locked for 30 minutes after the last record")
    timestamp = now_text()
    conn.execute(
        """
        INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path)
        VALUES (?, ?, ?, ?, ?, NULL)
        """,
        (person["id"], person["name"], person["role"], event_type, timestamp),
    )
    audit(
        conn,
        actor["id"] if actor else None,
        f"{source}_{event_type}",
        "attendance",
        object_id=person["id"],
        details={"person_name": person["name"], "role": person["role"], "event_type": event_type},
        ip_address=None,
    )


def delete_today_attendance(conn, actor, person_id, day_text):
    conn.execute(
        "DELETE FROM attendance WHERE person_id = ? AND timestamp LIKE ?",
        (person_id, f"{day_text}%"),
    )
    audit(
        conn,
        actor["id"] if actor else None,
        "delete_attendance",
        "attendance",
        object_id=person_id,
        details={"day": day_text},
    )


def latest_attendance_rows(conn, person_id, limit=30):
    return conn.execute(
        """
        SELECT
            attendance.id,
            attendance.event_type,
            attendance.timestamp,
            COALESCE(attendance.snapshot_path, '') AS snapshot_path,
            COALESCE((
                SELECT COALESCE(web_users.display_name, web_users.username, '')
                FROM audit_log
                LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
                WHERE audit_log.object_type = 'attendance'
                  AND audit_log.object_id = attendance.person_id
                  AND audit_log.action LIKE '%' || attendance.event_type
                  AND audit_log.created_at <= attendance.timestamp
                ORDER BY audit_log.created_at DESC, audit_log.id DESC
                LIMIT 1
            ), 'System') AS actor_name
        FROM attendance
        WHERE person_id = ?
        ORDER BY timestamp DESC, id DESC
        LIMIT ?
        """,
        (person_id, limit),
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


def render_dashboard(user, query):
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        selected_class = query.get("class", ["all"])[0]
        selected_date = query.get("date", [today_text()])[0]
        selected_child_id = query.get("child_id", [""])[0]
        selected_sort = query.get("sort", ["class"])[0]
        if selected_sort not in {"class", "name"}:
            selected_sort = "class"
        if selected_class not in classes and selected_class != "all":
            selected_class = classes[0] if classes else "all"
        children = get_children(conn, user, selected_class)
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
            cards.append(
                f"""
                <a class="card-link" href="/dashboard?class={quote(selected_class)}&date={quote(selected_date)}&sort={quote(selected_sort)}&child_id={child['id']}">
                  <div class="card {status_class} {'selected' if str(child['id']) == selected_child_id else ''}">
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
        class_count_items = "".join(
            f'<span class="count-chip">{html.escape(name)}: {total_count}</span>'
            for name, total_count, _p, _a, _fcount in summary_rows
        )
        class_count_html = f'<div class="count-strip"><span class="count-chip strong">Total: {total}</span>{class_count_items}</div>'
        control_options = "".join(
            f'<option value="{html.escape(cls)}" {"selected" if cls == selected_class else ""}>{html.escape(cls)}</option>'
            for cls in (["all"] + classes)
        )
        sort_options = "".join(
            f'<option value="{value}" {"selected" if value == selected_sort else ""}>{label}</option>'
            for value, label in (("class", "Class"), ("name", "Name"))
        )
        child_options = "".join(
            f'<option value="{child["id"]}" {"selected" if str(child["id"]) == selected_child_id else ""}>{html.escape(child["name"])}</option>'
            for child in children
        )
        selected_name = html.escape(selected_child["name"]) if selected_child else "No child selected"
        selected_class_name = html.escape(selected_child["class_name"] or "Unassigned") if selected_child else ""
        selected_status = current_child_status(conn, selected_child["id"], selected_date) if selected_child else "A"
        checkin_disabled = selected_status == "P" or selected_status == "F" or not can_edit_child(user) or not selected_child
        checkout_disabled = selected_status == "A" or selected_status == "F" or not can_edit_child(user) or not selected_child
        checkin_class = "green" if not checkin_disabled else "gray"
        checkout_class = "primary" if not checkout_disabled else "gray"
        checkin_label = "Check in"
        checkout_label = "Check out"
        if selected_status == "P":
            checkin_label = "Already in"
        elif selected_status == "A":
            checkout_label = "Already out"
        elif selected_status == "F":
            checkin_label = "Closed"
            checkout_label = "Closed"
        action_disabled_note = "" if can_edit_child(user) else '<div class="small muted">Editing is not allowed for this account.</div>'
        clear_day_html = ""
        if user["role"] != "cook":
            clear_day_html = f"""
                <form method="post" action="/child/{selected_child['id'] if selected_child else 0}/delete-day" onsubmit="return confirm('Clear attendance for {selected_name} on {html.escape(selected_date)} ?')" style="display:inline">
                  <input type="hidden" name="date" value="{html.escape(selected_date)}">
                  <button class="btn red" type="submit">Clear day</button>
                </form>
            """
        selected_recent_rows = ""
        selected_photo_url = ""
        if selected_child:
            selected_recent = latest_attendance_rows(conn, selected_child["id"], 10)
            selected_recent_rows = "".join(
                f"<tr><td>{html.escape(r['timestamp'])}</td><td>{html.escape(r['event_type'])}</td><td>{html.escape(r['actor_name'] or 'System')}</td></tr>"
                for r in selected_recent
            )
            selected_photo_url = child_card_image_url(selected_child["photo_path"]) or ""
        selected_status_class = {"P": "present", "A": "absent", "F": "closed"}.get(selected_status, "absent")
        admin_tools_html = ""
        if user["role"] in {"principal", "boss"}:
            export_url = "/export.xlsx"
            stats_url = "/statistics"
            fiche_url = f"/reports?date={quote(selected_date)}&format=detailed"
            admin_tools_html = f"""
            <div class="panel">
              <h3>Admin Tools</h3>
              <div class="btn-row">
                <a class="btn amber" href="{stats_url}">Presence Summary</a>
                <a class="btn" href="{export_url}">Export Excel</a>
                <a class="btn primary" href="{fiche_url}">4-Week Fiche</a>
              </div>
            </div>
            """
        body = f"""
        <div class="panel">
          <h2>Dashboard</h2>
          <div class="action-panel">
            <div class="action-card">
              <form method="get" action="/dashboard" class="dashboard-filters" id="dashboard-filters">
                <div>
                  <label>Class</label>
                  <select name="class" id="dashboard-class" onchange="this.form.submit()">{control_options}</select>
                </div>
                <div>
                  <label>Date</label>
                  <input type="date" name="date" value="{html.escape(selected_date)}" onchange="this.form.submit()">
                </div>
                <div>
                  <label>Sort</label>
                  <select name="sort" id="dashboard-sort" onchange="this.form.submit()">{sort_options}</select>
                </div>
                <div>
                  <label>Child</label>
                  <select name="child_id" id="dashboard-child" onchange="this.form.submit()">{child_options}</select>
                </div>
              </form>
            </div>
          </div>
          <div class="stats">
            <div class="stat"><div class="muted">Children</div><div class="value">{total}</div></div>
            <div class="stat"><div class="muted">Present</div><div class="value" style="color:var(--green)">{present_count}</div></div>
            <div class="stat"><div class="muted">Absence</div><div class="value" style="color:var(--gray)">{absent_count}</div></div>
            <div class="stat"><div class="muted">Closed</div><div class="value" style="color:var(--amber)">{closed_count}</div></div>
          </div>
        </div>
          <div class="grid two-col" style="margin-top:16px">
          <div class="panel">
            <h3 style="margin-bottom:6px">Children</h3>
            {class_count_html}
            <div class="cards">{''.join(cards) if cards else '<div class="muted">No children found for this scope.</div>'}</div>
          </div>
            <div class="grid" style="gap:16px">
            <div class="panel">
              <h3>Selected Child</h3>
              <div class="selected-child-head">
                {f'<img src="{selected_photo_url}" alt="{selected_name}">' if selected_photo_url else '<div class="muted">No photo</div>'}
                <div>
                  <div style="font-weight:700">{selected_name}</div>
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
              <div class="table-wrap">
                <table>
                  <thead><tr><th>Timestamp</th><th>Event</th><th>By</th></tr></thead>
                  <tbody>{selected_recent_rows or '<tr><td colspan="3" class="muted">No records</td></tr>'}</tbody>
                </table>
              </div>
            </div>
            <div class="panel">
              <h3>Class Summary</h3>
              <div class="table-wrap">
                <table>
                  <thead><tr><th>Class</th><th>Total</th><th>P</th><th>A</th><th>F</th></tr></thead>
                  <tbody>{summary_html or '<tr><td colspan="5" class="muted">No data</td></tr>'}</tbody>
                </table>
              </div>
            </div>
            {admin_tools_html}
          </div>
        </div>
        <script>
        (function() {{
          const version = {version};
          const currentUrl = new URL(window.location.href);
          function poll() {{
            fetch('/api/dashboard-version?class=' + encodeURIComponent(currentUrl.searchParams.get('class') || '{html.escape(selected_class)}') + '&date=' + encodeURIComponent(currentUrl.searchParams.get('date') || '{html.escape(selected_date)}'), {{
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
          setInterval(poll, 5000);
        }})();
        </script>
        """
        return html_page("Dashboard", user, body)


def render_child_detail(user, child_id, query):
    with connect_db() as conn:
        child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (child_id,)).fetchone()
        if not child:
            return html_page("Not Found", user, '<div class="panel">Child not found.</div>')
        if not can_view_all_classes(user) and child["class_name"] not in classes_for_user(user, conn):
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to view this child.</div>')
        selected_date = query.get("date", [today_text()])[0]
        status = current_child_status(conn, child["id"], selected_date)
        rows = latest_attendance_rows(conn, child["id"], 30)
        rows_html = "".join(
            f"<tr><td>{html.escape(r['timestamp'])}</td><td>{html.escape(r['event_type'])}</td><td>{html.escape(r['actor_name'] or 'System')}</td></tr>"
            for r in rows
        )
        photo_url = child_card_image_url(child["photo_path"])
        badge_class = {"P": "present", "A": "absent", "F": "closed"}.get(status, "absent")
        body = f"""
        <div class="grid two-col">
          <div class="panel">
            <h2>{html.escape(child['name'])}</h2>
            <div class="muted">{html.escape(child['class_name'] or 'Unassigned')}</div>
            <div class="no-print" style="margin:8px 0 12px">
              <a class="btn" href="/dashboard">Back to Dashboard</a>
            </div>
            <div style="margin:14px 0">
              {f'<img src="{photo_url}" alt="{html.escape(child["name"])}" style="max-width:25%;border-radius:8px;border:1px solid var(--line)">' if photo_url else '<div class="muted">No photo</div>'}
            </div>
            <div class="badge {badge_class}" style="margin-bottom:12px">{status_label(status)}</div>
            <div class="muted-box no-print">
              No direct actions on this page.
            </div>
          </div>
            <div class="panel">
            <h3>Recent Attendance</h3>
            <div class="table-wrap">
              <table>
                <thead><tr><th>Timestamp</th><th>Event</th><th>By</th></tr></thead>
                <tbody>{rows_html or '<tr><td colspan="3" class="muted">No records</td></tr>'}</tbody>
              </table>
            </div>
          </div>
        </div>
        """
        return html_page(child["name"], user, body)


def render_reports(user, query):
    with connect_db() as conn:
        classes = classes_for_user(user, conn)
        children = get_children(conn, user)
        person_id = query.get("person_id", [str(children[0]["id"]) if children else ""])[0]
        selected_format = query.get("format", ["detailed"])[0]
        selected_date = query.get("date", [today_text()])[0]
        if person_id:
            child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (person_id,)).fetchone()
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
        if selected_format == "summary":
            rows = []
            for week_index, week in enumerate(weeks, start=1):
                p = sum(1 for _, s in week if s == "P")
                a = sum(1 for _, s in week if s == "A")
                fcount = sum(1 for _, s in week if s == "F")
                rows.append(f"<tr><td>Week {week_index}</td><td>{p}</td><td>{a}</td><td>{fcount}</td></tr>")
            sheet = f"""
            <table class="fiche">
              <thead><tr><th class="name-col">Week</th><th>P</th><th>A</th><th>F</th></tr></thead>
              <tbody>{''.join(rows)}</tbody>
            </table>
            """
        else:
            header_cols = []
            for week in weeks:
                for day_text, _ in week:
                    dt = datetime.strptime(day_text, "%Y-%m-%d").strftime("%m/%d")
                    header_cols.append(f"<th>{dt}</th>")
            body_rows = []
            flat = [item for week in weeks for item in week]
            cells = "".join(f'<td><span class="pill {status}">{status}</span></td>' for _, status in flat)
            body_rows.append(f"<tr><td class='name-col'>{html.escape(child['name'])}</td>{cells}</tr>")
            sheet = f"""
            <table class="fiche">
              <thead>
                <tr><th class="name-col">Child</th>{''.join(header_cols)}</tr>
              </thead>
              <tbody>{''.join(body_rows)}</tbody>
            </table>
            """
        body = f"""
        <div class="panel no-print">
          <h2>4-Week Fiche</h2>
          <form method="get" action="/reports" class="toolbar" style="margin-bottom:0">
            <div>
              <label>Child</label>
              <select name="person_id">
                {''.join(f'<option value="{c["id"]}" {"selected" if c["id"] == child["id"] else ""}>{html.escape(c["name"])}</option>' for c in children)}
              </select>
            </div>
            <div>
              <label>Date</label>
              <input type="date" name="date" value="{html.escape(selected_date)}">
            </div>
            <div>
              <label>Format</label>
              <select name="format">
                <option value="detailed" {"selected" if selected_format == "detailed" else ""}>Detailed 4 week</option>
                <option value="summary" {"selected" if selected_format == "summary" else ""}>Summary 4 week</option>
              </select>
            </div>
            <div>
              <button class="btn primary" type="submit" name="generate" value="1">Generate PDF</button>
            </div>
          </form>
        </div>
        <div class="panel" style="margin-top:16px">
          <div class="muted small">Child: {html.escape(child['name'])} · Class: {html.escape(child['class_name'] or 'Unassigned')} · Start: {html.escape(start_text)}</div>
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
      .stats-calendar {{ margin-top: 10px; }}
      .stats-calendar table {{ width: 100%; border-collapse: collapse; }}
      .stats-calendar th, .stats-calendar td {{ text-align: center; padding: 6px 4px; border: 1px solid var(--line); }}
      .stats-calendar td.out-month a {{ color: #aaa; }}
      .stats-calendar td.today a {{ font-weight: 700; }}
      .stats-calendar td.selected {{ background: #d7b5ff; }}
      .stats-calendar td.selected a {{ color: #000; font-weight: 700; }}
      .stats-calendar td a {{ display: block; text-decoration: none; color: inherit; }}
      .stats-calendar-nav {{ display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-bottom: 8px; }}
    </style>
    <div class="panel">
      <h2>Presence Summary</h2>
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
      <div class="muted small" style="margin-top:10px">Selected date: {html.escape(selected_date_text)}. Child attendance records: {len(rows)}</div>
      <div class="table-wrap" style="margin-top:10px">
        <table>
          <thead><tr><th>Date</th><th>Time</th><th>Children Present</th><th>Class Counts</th></tr></thead>
          <tbody>{table_rows or '<tr><td colspan="4" class="muted">No child attendance records are available for this date.</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Presence Summary", user, body)


def build_attendance_export_xlsx(user, selected_class, selected_date):
    with connect_db() as conn:
        rows = attendance_export_source_rows(conn)
    export_rows = [
        [name, ROLE_LABELS.get(role, role), class_name, timestamp, EVENT_LABELS.get(event_type, event_type), snapshot_path]
        for _person_id, name, role, class_name, timestamp, event_type, snapshot_path in rows
    ]
    summary_rows = build_presence_summary_rows(rows)
    workbook = [
        {
            "name": "Attendance Records",
            "headers": ["Name", "Role", "Class", "Time", "Type", "Snapshot Photo"],
            "rows": export_rows,
        },
        {
            "name": "Presence Summary",
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
    rows = "".join(f"<tr><td>{html.escape(d)}</td><td><form method='post' action='/closed-dates/remove' onsubmit=\"return confirm('Remove this date?')\"><input type='hidden' name='date' value='{html.escape(d)}'><button class='btn red' type='submit'>Remove</button></form></td></tr>" for d in closed)
    body = f"""
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
          <button class="btn amber" type="submit">Add F date</button>
        </div>
      </form>
    </div>
    <div class="panel" style="margin-top:16px">
      <h3>Current Closed Dates</h3>
      <div class="table-wrap">
        <table>
          <thead><tr><th>Date</th><th>Action</th></tr></thead>
          <tbody>{rows or '<tr><td colspan=\"2\" class=\"muted\">No closed dates</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Closed Dates", user, body)


def render_users(user, query):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage users.</div>')
    with connect_db() as conn:
        users = conn.execute("SELECT * FROM web_users ORDER BY role, username").fetchall()
        classes = get_classes(conn)
    table_rows = []
    for target in users:
        if user["role"] == "principal" and target["role"] == "boss":
            continue
        classes_value = json.loads(target["allowed_classes_json"] or "[]")
        class_text = ", ".join(classes_value) if classes_value else "-"
        table_rows.append(
            f"""
            <tr>
              <td>{html.escape(target['username'])}</td>
              <td>{html.escape(target['display_name'])}</td>
              <td>{html.escape(target['role'])}</td>
              <td>{html.escape(class_text)}</td>
              <td>{html.escape(target['password_changed_at'])}</td>
              <td>
                <a class="btn" href="/users/edit?id={target['id']}">Edit</a>
              </td>
            </tr>
            """
        )
    body = f"""
    <div class="panel">
      <h2>User Management</h2>
      <div class="muted">Principal can edit teachers and cooks. Boss can edit all users.</div>
      <div class="table-wrap" style="margin-top:12px">
        <table>
          <thead><tr><th>Username</th><th>Name</th><th>Role</th><th>Classes</th><th>Password changed</th><th>Action</th></tr></thead>
          <tbody>{''.join(table_rows) or '<tr><td colspan=\"6\" class=\"muted\">No users</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <div class="panel" style="margin-top:16px">
      <h3>Create User</h3>
      <form method="post" action="/users/create" class="user-grid">
        <div><label>Username</label><input name="username" required></div>
        <div><label>Display name</label><input name="display_name" required></div>
        <div><label>Role</label>
          <select name="role">
            {"<option value='teacher'>teacher</option><option value='cook'>cook</option>" if user["role"] == "principal" else "<option value='teacher'>teacher</option><option value='principal'>principal</option><option value='boss'>boss</option><option value='cook'>cook</option>"}
          </select>
        </div>
        <div><label>Initial password</label><input name="password" type="password" required></div>
        <div><label>Classes (comma separated)</label><input name="classes" placeholder="{html.escape(', '.join(classes))}"></div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Create</button></div>
      </form>
    </div>
    """
    return html_page("Users", user, body)


def render_children_admin(user, query):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to manage children.</div>')
    with connect_db() as conn:
        classes = get_classes(conn)
        children = conn.execute(
            """
            SELECT id, name, class_name, photo_path, created_at
            FROM persons
            WHERE role = 'children'
            ORDER BY class_name, name
            """
        ).fetchall()
    rows = "".join(
        f"""
        <tr>
          <td>{html.escape(child['name'])}</td>
          <td>{html.escape(child['class_name'] or '')}</td>
          <td>{html.escape(child['photo_path'] or '')}</td>
          <td>{html.escape(child['created_at'])}</td>
          <td class="nowrap">
            <a class="btn" href="/children/edit?id={child['id']}">Edit</a>
            <form method="post" action="/children/delete" style="display:inline" onsubmit="return confirm('Delete this child and attendance records?')">
              <input type="hidden" name="id" value="{child['id']}">
              <button class="btn red" type="submit">Delete</button>
            </form>
          </td>
        </tr>
        """
        for child in children
    )
    class_options = "".join(f'<option value="{html.escape(cls)}">{html.escape(cls)}</option>' for cls in classes)
    body = f"""
    <div class="panel">
      <h2>Child Management</h2>
      <div class="muted">Boss and Principal can add, edit, and remove children.</div>
      <div class="table-wrap" style="margin-top:12px">
        <table>
          <thead><tr><th>Name</th><th>Class</th><th>Photo path</th><th>Created</th><th>Action</th></tr></thead>
          <tbody>{rows or '<tr><td colspan="5" class="muted">No children found</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    <div class="panel" style="margin-top:16px">
      <h3>Add Child</h3>
      <form method="post" action="/children/create" class="user-grid">
        <div><label>Name</label><input name="name" required></div>
        <div><label>Class</label><select name="class_name">{class_options}</select></div>
        <div><label>Photo path (optional)</label><input name="photo_path" placeholder="Leave blank to use a placeholder"></div>
        <div><label>Initial status</label>
          <select name="initial_status">
            <option value="A">Absence</option>
            <option value="P">Present</option>
          </select>
        </div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Add</button></div>
      </form>
    </div>
    """
    return html_page("Children", user, body)


def render_child_edit(user, child_id):
    if user["role"] not in MANAGE_USERS_ROLES:
        return html_page("Forbidden", user, '<div class="panel">You are not allowed to edit children.</div>')
    with connect_db() as conn:
        child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (child_id,)).fetchone()
        if not child:
            return html_page("Not Found", user, '<div class="panel">Child not found.</div>')
        classes = get_classes(conn)
    body = f"""
    <div class="panel">
      <h2>Edit Child</h2>
      <form method="post" action="/children/update" class="user-grid">
        <input type="hidden" name="id" value="{child['id']}">
        <div><label>Name</label><input name="name" value="{html.escape(child['name'])}" required></div>
        <div><label>Class</label>
          <select name="class_name">
            {''.join(f'<option value="{html.escape(cls)}" {"selected" if cls == (child["class_name"] or "") else ""}>{html.escape(cls)}</option>' for cls in classes)}
          </select>
        </div>
        <div><label>Photo path</label><input name="photo_path" value="{html.escape(child['photo_path'] or '')}"></div>
        <div><label>Created at</label><input value="{html.escape(child['created_at'])}" disabled></div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Save</button></div>
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
        if not can_manage_users(user, target) and not self_edit:
            return html_page("Forbidden", user, '<div class="panel">You are not allowed to edit this user.</div>')
        classes = get_classes(conn)
        selected = set(json.loads(target["allowed_classes_json"] or "[]"))
        checks = "".join(
            f'<label style="display:inline-flex;gap:6px;align-items:center;margin-right:12px"><input type="checkbox" name="classes" value="{html.escape(cls)}" {"checked" if cls in selected else ""}>{html.escape(cls)}</label>'
            for cls in classes
        )
    body = f"""
    <div class="panel">
      <h2>Edit User</h2>
      {f'<div class="muted small" style="margin-bottom:10px">You can only change your password here.</div>' if self_edit else ''}
      <form method="post" action="/users/update" class="user-grid">
        <input type="hidden" name="id" value="{target['id']}">
        <div><label>Username</label><input name="username" value="{html.escape(target['username'])}" {"readonly disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit else 'required'}></div>
        <div><label>Display name</label><input name="display_name" value="{html.escape(target['display_name'])}" {"readonly disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit else 'required'}></div>
        <div><label>Role</label>
          <select name="role" {"disabled style='background:#f3f4f6;color:#9ca3af;cursor:not-allowed'" if self_edit else ''}>
            {''.join(f'<option value="{role}" {"selected" if role == target["role"] else ""}>{role}</option>' for role in ["teacher", "principal", "boss", "cook"])}
          </select>
        </div>
        <div><label>New password</label><input name="password" type="password" placeholder="Leave blank to keep current" {"required" if self_edit else ''}></div>
        <div><label>Classes</label><div class="muted-box">{"<span class=\"muted\">Locked for your account.</span>" if self_edit else (checks or '<span class="muted">No classes configured.</span>')}</div></div>
        <div style="display:flex;align-items:end"><button class="btn primary" type="submit">Save</button></div>
      </form>
    </div>
    """
    return html_page(f"Edit {target['username']}", user, body)


def render_audit(user):
    with connect_db() as conn:
        rows = conn.execute(
            """
            SELECT audit_log.*, COALESCE(web_users.username, '') AS actor_username, COALESCE(web_users.display_name, '') AS actor_name
            FROM audit_log
            LEFT JOIN web_users ON web_users.id = audit_log.actor_user_id
            ORDER BY audit_log.id DESC
            LIMIT 200
            """
        ).fetchall()
    body_rows = "".join(
        f"<tr><td>{html.escape(r['created_at'])}</td><td>{html.escape(r['actor_name'] or r['actor_username'] or '')}</td><td>{html.escape(r['action'])}</td><td>{html.escape(r['object_type'])}</td><td>{html.escape(r['object_id'] or '')}</td><td><code>{html.escape(r['details_json'])}</code></td></tr>"
        for r in rows
    )
    body = f"""
    <div class="panel">
      <h2>Audit Log</h2>
      <div class="table-wrap">
        <table>
          <thead><tr><th>Time</th><th>Actor</th><th>Action</th><th>Type</th><th>Object</th><th>Details</th></tr></thead>
          <tbody>{body_rows or '<tr><td colspan=\"6\" class=\"muted\">No logs yet</td></tr>'}</tbody>
        </table>
      </div>
    </div>
    """
    return html_page("Audit Log", user, body)


def redirect(handler, location, extra_headers=None):
    handler.send_response(302)
    handler.send_header("Location", location)
    if extra_headers:
        for key, value in extra_headers.items():
            handler.send_header(key, value)
    handler.end_headers()


def parse_post_data(handler):
    length = int(handler.headers.get("Content-Length", "0") or 0)
    raw = handler.rfile.read(length).decode("utf-8")
    return parse_qs(raw, keep_blank_values=True)


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
        return row


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


class Handler(BaseHTTPRequestHandler):
    server_version = "KindergartenAttendanceWeb/1.0"

    def log_message(self, format, *args):
        return

    def send_html(self, content, status=200, extra_headers=None):
        body = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
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
        if path.startswith("/media/"):
            path_token = path.split("/media/", 1)[1]
            file_path = safe_resolve_media(path_token)
            if not file_path or not file_path.exists():
                self.send_error(404)
                return
            self.send_file(file_path)
            return
        if not user:
            if path == "/":
                self.send_html(login_page())
                return
            self.send_html(login_page())
            return
        if path not in {"/password-change", "/logout"} and password_is_expired(user):
            redirect(self, "/password-change")
            return
        if path == "/":
            redirect(self, "/dashboard")
            return
        if path == "/dashboard":
            self.send_html(render_dashboard(user, query))
            return
        if path == "/me":
            self.send_html(render_me(user, query))
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
                    payload = generate_acceo_summary_attendance_pdf(chosen_date)
                    filename = f"Fiche_assiduite_summary_{chosen_date.strftime('%Y%m%d')}.pdf"
                else:
                    payload = generate_acceo_detail_attendance_pdf(chosen_date)
                    filename = f"Fiche_assiduite_detaillee_4_week_{chosen_date.strftime('%Y%m%d')}.pdf"
                self.send_response(200)
                self.send_header("Content-Type", "application/pdf")
                self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
            else:
                self.send_html(render_reports(user, query))
            return
        if path in {"/statistics", "/statistics/15min"}:
            self.send_html(render_statistics_15min(user, query))
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
        if path == "/children":
            self.send_html(render_children_admin(user, query))
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
            self.send_html(render_audit(user))
            return
        if path == "/api/dashboard-version":
            with connect_db() as conn:
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
        if path == "/password-change":
            self.send_html(render_password_change(user))
            return
        self.send_error(404)

    def do_POST(self):
        user = get_session_user(self)
        parsed = urlparse(self.path)
        path = parsed.path
        if path == "/login":
            form = parse_post_data(self)
            username = form.get("username", [""])[0]
            password = form.get("password", [""])[0]
            with connect_db() as conn:
                target = login_user(conn, username, password)
                if not target:
                    self.send_html(login_page("Invalid username or password"))
                    return
                token = create_session(conn, target["id"])
                audit(conn, target["id"], "login", "session", object_id=target["id"], details={"username": target["username"]})
                conn.commit()
            redirect(self, "/password-change" if password_is_expired(target) else "/dashboard", {"Set-Cookie": session_cookie_header(token)})
            return
        if path == "/logout":
            if user:
                cookie = parse_cookie(self.headers.get("Cookie"))
                token = cookie.get("session")
                with connect_db() as conn:
                    if token:
                        delete_session(conn, token.value)
                    audit(conn, user["id"], "logout", "session", object_id=user["id"])
                    conn.commit()
            redirect(self, "/", {"Set-Cookie": clear_session_cookie()})
            return
        if not user:
            self.send_error(401)
            return

        form = parse_post_data(self)

        if path == "/password-change":
            new_password = form.get("password", [""])[0]
            confirm = form.get("confirm", [""])[0]
            if len(new_password) < 8:
                self.send_html(render_password_change(user, "Password must be at least 8 characters."), status=200)
                return
            if new_password != confirm:
                self.send_html(render_password_change(user, "Passwords do not match."), status=200)
                return
            with connect_db() as conn:
                try:
                    update_user_password(conn, user["id"], new_password)
                    audit(conn, user["id"], "password_change", "user", object_id=user["id"])
                    conn.commit()
                except ValueError as exc:
                    self.send_html(render_password_change(user, str(exc)), status=200)
                    return
            redirect(self, "/dashboard")
            return

        if path.startswith("/child/") and path.endswith("/event"):
            child_id = path.split("/")[2]
            event_type = form.get("event_type", [""])[0]
            day_text = form.get("date", [today_text()])[0]
            if event_type not in {"checkin", "checkout"}:
                self.send_error(400)
                return
            with connect_db() as conn:
                child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (child_id,)).fetchone()
                if not child:
                    self.send_error(404)
                    return
                if not can_view_all_classes(user) and child["class_name"] not in classes_for_user(user, conn):
                    self.send_error(403)
                    return
                try:
                    if user["role"] == "teacher" and recent_teacher_event_block(conn, child["id"], event_type):
                        raise ValueError("Teacher attendance changes are locked for 30 minutes after the last record")
                    if day_text != today_text():
                        timestamp = f"{day_text} {datetime.now().strftime('%H:%M:%S')}"
                        conn.execute(
                            "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path) VALUES (?, ?, ?, ?, ?, NULL)",
                            (child["id"], child["name"], child["role"], event_type, timestamp),
                        )
                        audit(conn, user["id"], f"manual_{event_type}", "attendance", object_id=child["id"], details={"date": day_text})
                    else:
                        record_attendance(conn, user, child["id"], event_type, source="manual")
                    conn.commit()
                except ValueError as exc:
                    self.send_html(html_page("Error", user, f'<div class="panel">{html.escape(str(exc))}</div>'))
                    return
            redirect(self, f"/dashboard?class={quote(child['class_name'] or 'all')}&date={quote(day_text)}&child_id={child['id']}")
            return

        if path.startswith("/child/") and path.endswith("/delete-day"):
            child_id = path.split("/")[2]
            day_text = form.get("date", [today_text()])[0]
            with connect_db() as conn:
                child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (child_id,)).fetchone()
                if not child:
                    self.send_error(404)
                    return
                if not can_edit_child(user):
                    self.send_error(403)
                    return
                delete_today_attendance(conn, user, child["id"], day_text)
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
                person = conn.execute("SELECT * FROM persons WHERE id = ?", (person_id,)).fetchone()
                if not person or person["role"] != "teachers":
                    self.send_error(404)
                    return
                try:
                    record_attendance(conn, user, person_id, event_type, source="teacher_self")
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
                    audit(conn, user["id"], "closed_date_add", "settings", object_id=day_text, details={"reason": reason})
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
                audit(conn, user["id"], "closed_date_remove", "settings", object_id=day_text)
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
            if not username or not display_name or role not in ROLE_LABELS or len(password) < 8:
                self.send_html(render_users(user, {}), status=200)
                return
            if user["role"] == "principal" and role not in {"teacher", "cook"}:
                self.send_html(html_page("Forbidden", user, '<div class="panel">Principal can create only teacher or cook accounts.</div>'))
                return
            with connect_db() as conn:
                try:
                    create_user(conn, username, display_name, role, password, person_id=None, allowed_classes=classes)
                    audit(conn, user["id"], "create_user", "user", object_id=username, details={"role": role})
                    conn.commit()
                except sqlite3.IntegrityError:
                    self.send_html(html_page("Error", user, '<div class="panel">Username already exists.</div>'))
                    return
            redirect(self, "/users")
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
                if not can_manage_users(user, target) and not self_edit:
                    self.send_error(403)
                    return
                password = form.get("password", [""])[0]
                if self_edit:
                    if not password.strip():
                        self.send_html(html_page("Error", user, '<div class="panel">Please enter a new password.</div>'))
                        return
                    update_user_password(conn, target["id"], password)
                    audit(conn, user["id"], "update_user_password", "user", object_id=target["id"], details={"username": target["username"]})
                    conn.commit()
                    redirect(self, "/users")
                    return
                username = form.get("username", [""])[0].strip()
                display_name = form.get("display_name", [""])[0].strip()
                role = form.get("role", [""])[0].strip()
                classes = form.get("classes", [])
                class_list = [part for part in classes if part in get_classes(conn)]
                if not username or not display_name or role not in ROLE_LABELS:
                    self.send_error(400)
                    return
                conn.execute(
                    """
                    UPDATE web_users
                    SET username = ?, display_name = ?, role = ?, allowed_classes_json = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (username, display_name, role, allowed_classes_value(class_list), now_text(), target["id"]),
                )
                if password.strip():
                    update_user_password(conn, target["id"], password)
                audit(conn, user["id"], "update_user", "user", object_id=target["id"], details={"username": username, "role": role})
                conn.commit()
            redirect(self, "/users")
            return

        if path == "/children/create":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            name = form.get("name", [""])[0].strip()
            class_name = form.get("class_name", [""])[0].strip()
            photo_path = form.get("photo_path", [""])[0].strip()
            initial_status = form.get("initial_status", ["A"])[0]
            if not name:
                self.send_html(render_children_admin(user, {}), status=200)
                return
            if not photo_path:
                photo_path = default_child_photo_path(name)
            if not class_name:
                class_name = ""
            with connect_db() as conn:
                conn.execute(
                    """
                    INSERT INTO persons(name, role, class_name, photo_path, qr_token, created_at)
                    VALUES (?, 'children', ?, ?, ?, ?)
                    """,
                    (name, class_name, photo_path, f"CHILD:{name}", now_text()),
                )
                child_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
                if initial_status == "P":
                    conn.execute(
                        "INSERT INTO attendance(person_id, name, role, event_type, timestamp, snapshot_path) VALUES (?, ?, 'children', 'checkin', ?, NULL)",
                        (child_id, name, now_text()),
                    )
                audit(conn, user["id"], "create_child", "child", object_id=child_id, details={"name": name, "class_name": class_name})
                conn.commit()
            redirect(self, "/children")
            return

        if path == "/children/update":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
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
                conn.execute(
                    """
                    UPDATE persons
                    SET name = ?, class_name = ?, photo_path = ?, qr_token = ?
                    WHERE id = ? AND role = 'children'
                    """,
                    (name, class_name, photo_path, f"CHILD:{name}", int(child_id)),
                )
                conn.execute("UPDATE attendance SET name = ? WHERE person_id = ?", (name, int(child_id)))
                audit(conn, user["id"], "update_child", "child", object_id=child_id, details={"name": name, "class_name": class_name})
                conn.commit()
            redirect(self, "/children")
            return

        if path == "/children/delete":
            if user["role"] not in MANAGE_USERS_ROLES:
                self.send_error(403)
                return
            child_id = form.get("id", [""])[0]
            if not child_id.isdigit():
                self.send_error(400)
                return
            with connect_db() as conn:
                child = conn.execute("SELECT * FROM persons WHERE id = ? AND role = 'children'", (int(child_id),)).fetchone()
                if not child:
                    self.send_error(404)
                    return
                conn.execute("DELETE FROM attendance WHERE person_id = ?", (int(child_id),))
                conn.execute("DELETE FROM persons WHERE id = ? AND role = 'children'", (int(child_id),))
                audit(conn, user["id"], "delete_child", "child", object_id=child_id, details={"name": child["name"]})
                conn.commit()
            redirect(self, "/children")
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
          <label>New password</label>
          <input name="password" type="password" required>
        </div>
        <div>
          <label>Confirm password</label>
          <input name="confirm" type="password" required>
        </div>
        <button class="btn primary" type="submit">Save password</button>
      </form>
    </div>
    """
    return html_page("Change password", user, body)


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
          <button class="btn green" type="submit" name="event_type" value="checkin">Check in</button>
          <button class="btn gray" type="submit" name="event_type" value="checkout">Check out</button>
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
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    if args.host == "0.0.0.0":
        host_names = {"127.0.0.1", "localhost"}
        try:
            for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
                host_names.add(info[4][0])
        except OSError:
            pass
        print(f"Serving on http://0.0.0.0:{args.port}", flush=True)
        print("LAN access URLs:", flush=True)
        for host in sorted(host_names):
            print(f"  http://{host}:{args.port}", flush=True)
    else:
        print(f"Serving on http://{args.host}:{args.port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
