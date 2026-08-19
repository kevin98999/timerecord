import argparse
import json
import sqlite3
import sys
import urllib.error
import urllib.request
from datetime import datetime, timedelta
from pathlib import Path


DB_PATH = Path("data") / "attendance.db"
SETTINGS_PATH = Path("data") / "settings.json"


def load_settings():
    try:
        with SETTINGS_PATH.open("r", encoding="utf-8") as file:
            data = json.load(file)
            return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def normalize_url(value):
    value = str(value or "").strip()
    if not value:
        return ""
    if not value.lower().startswith(("http://", "https://")):
        value = "https://" + value
    return value.rstrip("/")


def load_rows(day_text):
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    rows = conn.execute(
        """
        SELECT attendance.person_id,
               attendance.name,
               attendance.role,
               attendance.event_type,
               attendance.timestamp,
               COALESCE(persons.class_name, '') AS class_name
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        WHERE attendance.timestamp LIKE ?
        ORDER BY attendance.timestamp, attendance.id
        """,
        (f"{day_text} %",),
    ).fetchall()
    return filter_utc_shift_duplicates(rows)


def filter_utc_shift_duplicates(rows):
    row_keys = {
        (row["name"].strip().lower(), row["role"], row["event_type"], row["timestamp"])
        for row in rows
    }
    filtered = []
    skipped = []
    for row in rows:
        try:
            event_time = datetime.strptime(row["timestamp"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            filtered.append(row)
            continue
        shifted_timestamp = (event_time - timedelta(hours=4)).strftime("%Y-%m-%d %H:%M:%S")
        shifted_key = (row["name"].strip().lower(), row["role"], row["event_type"], shifted_timestamp)
        if shifted_key in row_keys:
            skipped.append(row)
            continue
        filtered.append(row)
    if skipped:
        print(f"Skipping UTC-shift duplicate rows: {len(skipped)}")
        for row in skipped:
            print(f"SKIP {row['timestamp']} {row['name']} {row['event_type']}")
    return filtered


def post_record(remote_url, token, row, dry_run=False):
    payload = {
        "person_id": row["person_id"],
        "name": row["name"],
        "role": row["role"],
        "event_type": row["event_type"],
        "timestamp": row["timestamp"],
        "source": "desktop_backfill",
    }
    if dry_run:
        print("DRY-RUN", payload)
        return True, "dry-run"

    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    request = urllib.request.Request(
        f"{remote_url}/api/desktop/attendance",
        data=body,
        method="POST",
        headers={
            "Content-Type": "application/json; charset=utf-8",
            "X-TimeRecord-Token": token,
            "User-Agent": "TimeRecordBackfill/1.0",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=10) as response:
            text = response.read().decode("utf-8")
            return 200 <= response.status < 300, text
    except urllib.error.HTTPError as exc:
        try:
            return False, exc.read().decode("utf-8")
        except OSError:
            return False, f"HTTP {exc.code}"
    except OSError as exc:
        return False, str(exc)


def main():
    parser = argparse.ArgumentParser(description="Push local desktop attendance records for one date to the configured webapp.")
    parser.add_argument("--date", required=True, help="Date to push, format YYYY-MM-DD.")
    parser.add_argument("--url", help="Webapp base URL. Defaults to data/settings.json webapp_url.")
    parser.add_argument("--token", help="Desktop sync token. Defaults to data/settings.json desktop_sync_token.")
    parser.add_argument("--dry-run", action="store_true", help="Print records without sending.")
    args = parser.parse_args()

    settings = load_settings()
    remote_url = normalize_url(args.url or settings.get("webapp_url"))
    token = (args.token or settings.get("desktop_sync_token") or "").strip()
    if not remote_url:
        raise SystemExit("Missing webapp URL. Pass --url or set webapp_url in data/settings.json.")
    if not token and not args.dry_run:
        raise SystemExit("Missing desktop sync token. Pass --token or set desktop_sync_token in data/settings.json.")

    rows = load_rows(args.date)
    print(f"Remote URL: {remote_url}")
    print(f"Date: {args.date}")
    print(f"Rows to push: {len(rows)}")

    ok_count = 0
    fail_count = 0
    for row in rows:
        ok, detail = post_record(remote_url, token, row, dry_run=args.dry_run)
        if ok:
            ok_count += 1
            print(f"OK {row['timestamp']} {row['name']} {row['event_type']} {detail}")
        else:
            fail_count += 1
            print(f"FAIL {row['timestamp']} {row['name']} {row['event_type']} {detail}", file=sys.stderr)

    print(f"Done. OK={ok_count} FAIL={fail_count}")
    if fail_count:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
