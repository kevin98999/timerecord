import argparse
import shutil
import sqlite3
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

try:
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None


DB_PATH = Path("data") / "attendance.db"
TORONTO_TZ_NAME = "America/Toronto"


def toronto_offset_hours(utc_dt):
    march = date(utc_dt.year, 3, 1)
    second_sunday_march = march + timedelta(days=(6 - march.weekday()) % 7 + 7)
    november = date(utc_dt.year, 11, 1)
    first_sunday_november = november + timedelta(days=(6 - november.weekday()) % 7)
    dst_start_utc = datetime.combine(second_sunday_march, datetime.min.time()).replace(hour=7, tzinfo=timezone.utc)
    dst_end_utc = datetime.combine(first_sunday_november, datetime.min.time()).replace(hour=6, tzinfo=timezone.utc)
    return -4 if dst_start_utc <= utc_dt < dst_end_utc else -5


def toronto_now():
    if ZoneInfo is not None:
        try:
            return datetime.now(ZoneInfo(TORONTO_TZ_NAME)).replace(tzinfo=None)
        except Exception:
            pass
    utc_now = datetime.now(timezone.utc)
    return (utc_now + timedelta(hours=toronto_offset_hours(utc_now))).replace(tzinfo=None)


def utc_text_to_toronto_text(value):
    utc_dt = datetime.strptime(value, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
    if ZoneInfo is not None:
        try:
            return utc_dt.astimezone(ZoneInfo(TORONTO_TZ_NAME)).replace(tzinfo=None).strftime("%Y-%m-%d %H:%M:%S")
        except Exception:
            pass
    return (utc_dt + timedelta(hours=toronto_offset_hours(utc_dt))).replace(tzinfo=None).strftime("%Y-%m-%d %H:%M:%S")


def ceil_to_interval(dt, minutes):
    discard = timedelta(minutes=dt.minute % minutes, seconds=dt.second, microseconds=dt.microsecond)
    rounded = dt - discard
    if discard:
        rounded += timedelta(minutes=minutes)
    return rounded


def build_presence_summary_rows(rows):
    child_events = []
    for person_id, _name, role, class_name, timestamp, event_type, event_id in rows:
        if role != "children":
            continue
        try:
            event_time = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S")
        except (TypeError, ValueError):
            continue
        child_events.append(
            {
                "person_id": person_id,
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
    for date_value in dates:
        day_events = sorted(
            (event for event in child_events if event["time"].date() == date_value),
            key=lambda event: (event["time"], event["id"]),
        )
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
            summary_rows.append([date_value.strftime("%Y-%m-%d"), slot_time.strftime("%H:%M"), len(current_children), class_text])
            slot_time += timedelta(minutes=15)

    return summary_rows


def backup_database(db_path):
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_path = db_path.with_name(f"{db_path.stem}_before_time_fix_{stamp}{db_path.suffix}")
    shutil.copy2(db_path, backup_path)
    return backup_path


def fetch_day_rows(conn, day_text):
    return conn.execute(
        """
        SELECT attendance.id, attendance.person_id, attendance.name, attendance.role,
               attendance.event_type, attendance.timestamp, COALESCE(persons.class_name, '') AS class_name
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        WHERE attendance.timestamp LIKE ?
        ORDER BY attendance.timestamp, attendance.id
        """,
        (f"{day_text} %",),
    ).fetchall()


def print_day_rows(conn, day_text):
    print("\nAttendance rows:")
    for row in fetch_day_rows(conn, day_text):
        print(tuple(row))


def print_summary(conn, day_text):
    rows = conn.execute(
        """
        SELECT attendance.person_id, attendance.name, attendance.role,
               COALESCE(persons.class_name, ''), attendance.timestamp,
               attendance.event_type, attendance.id
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        WHERE attendance.timestamp LIKE ?
        ORDER BY attendance.timestamp DESC, attendance.id DESC
        """,
        (f"{day_text} %",),
    ).fetchall()
    print("\n15-minute presence summary:")
    for row in build_presence_summary_rows(rows):
        print(row)


def fix_future_utc_rows(conn, day_text, dry_run):
    now_local = toronto_now()
    cutoff = now_local + timedelta(minutes=5)
    print(f"Toronto now: {now_local:%Y-%m-%d %H:%M:%S}")
    print(f"Future cutoff: {cutoff:%Y-%m-%d %H:%M:%S}")

    changed = 0
    deleted = 0
    rows = fetch_day_rows(conn, day_text)
    for row in rows:
        record_id, _person_id, name, role, event_type, timestamp, _class_name = row
        try:
            event_time = datetime.strptime(timestamp, "%Y-%m-%d %H:%M:%S")
        except ValueError:
            continue

        converted = utc_text_to_toronto_text(timestamp)
        if converted == timestamp:
            continue
        duplicate = conn.execute(
            """
            SELECT id FROM attendance
            WHERE id <> ?
              AND name = ?
              AND role = ?
              AND event_type = ?
              AND timestamp = ?
            LIMIT 1
            """,
            (record_id, name, role, event_type, converted),
        ).fetchone()

        if duplicate:
            print(f"DELETE duplicate id={record_id} {name}: {timestamp} -> {converted}")
            if not dry_run:
                conn.execute("DELETE FROM attendance WHERE id = ?", (record_id,))
            deleted += 1
        elif event_time <= cutoff:
            continue
        else:
            print(f"UPDATE id={record_id} {name}: {timestamp} -> {converted}")
            if not dry_run:
                conn.execute("UPDATE attendance SET timestamp = ? WHERE id = ?", (converted, record_id))
            changed += 1

    return changed, deleted


def main():
    parser = argparse.ArgumentParser(description="Fix remote UTC attendance timestamps and print 15-minute presence summary.")
    parser.add_argument("--date", default=toronto_now().strftime("%Y-%m-%d"), help="Date to fix/check, format YYYY-MM-DD.")
    parser.add_argument("--db", default=str(DB_PATH), help="SQLite database path.")
    parser.add_argument("--dry-run", action="store_true", help="Show changes without writing them.")
    args = parser.parse_args()

    db_path = Path(args.db)
    if not db_path.exists():
        raise SystemExit(f"Database not found: {db_path}")

    day_text = datetime.strptime(args.date, "%Y-%m-%d").strftime("%Y-%m-%d")
    print(f"Database: {db_path}")
    print(f"Date: {day_text}")

    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row

    print_day_rows(conn, day_text)

    if args.dry_run:
        print("\nDry run only. No backup or database changes will be written.")
        changed, deleted = fix_future_utc_rows(conn, day_text, dry_run=True)
    else:
        backup_path = backup_database(db_path)
        print(f"\nBackup created: {backup_path}")
        with conn:
            changed, deleted = fix_future_utc_rows(conn, day_text, dry_run=False)

    print(f"\nRows updated: {changed}")
    print(f"Rows deleted: {deleted}")
    print_day_rows(conn, day_text)
    print_summary(conn, day_text)


if __name__ == "__main__":
    main()
