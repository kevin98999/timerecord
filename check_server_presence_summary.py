import argparse
import sqlite3
from datetime import datetime, timedelta
from pathlib import Path


DB_PATH = Path("data") / "attendance.db"


def ceil_to_interval(dt, minutes):
    discard = timedelta(minutes=dt.minute % minutes, seconds=dt.second, microseconds=dt.microsecond)
    rounded = dt - discard
    if discard:
        rounded += timedelta(minutes=minutes)
    return rounded


def load_rows(conn, day_text):
    return conn.execute(
        """
        SELECT attendance.id,
               attendance.person_id,
               attendance.name,
               attendance.role,
               COALESCE(persons.class_name, '') AS class_name,
               attendance.event_type,
               attendance.timestamp
        FROM attendance
        LEFT JOIN persons ON persons.id = attendance.person_id
        WHERE attendance.timestamp LIKE ?
        ORDER BY attendance.timestamp, attendance.id
        """,
        (f"{day_text} %",),
    ).fetchall()


def print_raw_rows(rows):
    print("RAW ATTENDANCE ROWS")
    print("id | person_id | name | role | class | event | timestamp")
    for row in rows:
        print(f"{row['id']} | {row['person_id']} | {row['name']} | {row['role']} | {row['class_name']} | {row['event_type']} | {row['timestamp']}")


def print_duplicate_warnings(rows):
    seen = {}
    duplicates = []
    for row in rows:
        key = (row["person_id"], row["event_type"], row["timestamp"])
        if key in seen:
            duplicates.append((seen[key], row))
        else:
            seen[key] = row
    if not duplicates:
        print("\nDUPLICATES: none")
        return
    print("\nDUPLICATES")
    for first, second in duplicates:
        print(f"duplicate: id={first['id']} and id={second['id']} {second['name']} {second['event_type']} {second['timestamp']}")


def print_future_like_rows(rows, day_text):
    print("\nUTC-SHIFT SUSPECTS")
    suspects = []
    by_local_key = {}
    for row in rows:
        try:
            event_time = datetime.strptime(row["timestamp"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            continue
        shifted = event_time - timedelta(hours=4)
        if shifted.strftime("%Y-%m-%d") != day_text:
            continue
        key = (row["name"].lower(), row["role"], row["event_type"], shifted.strftime("%Y-%m-%d %H:%M:%S"))
        by_local_key.setdefault(key, []).append(row)

    all_keys = {
        (row["name"].lower(), row["role"], row["event_type"], row["timestamp"])
        for row in rows
    }
    for row_list_key, row_list in by_local_key.items():
        if row_list_key in all_keys:
            suspects.extend(row_list)

    if not suspects:
        print("none")
        return
    for row in suspects:
        shifted = datetime.strptime(row["timestamp"], "%Y-%m-%d %H:%M:%S") - timedelta(hours=4)
        print(f"id={row['id']} {row['name']} {row['timestamp']} may duplicate {shifted:%Y-%m-%d %H:%M:%S}")


def print_timeline(rows, day_text):
    events = []
    for row in rows:
        if row["role"] != "children":
            continue
        try:
            event_time = datetime.strptime(row["timestamp"], "%Y-%m-%d %H:%M:%S")
        except ValueError:
            continue
        events.append(
            {
                "id": row["id"],
                "person_id": row["person_id"],
                "name": row["name"],
                "class_name": row["class_name"] or "Unassigned",
                "event_type": row["event_type"],
                "time": event_time,
            }
        )

    print("\n15-MINUTE PRESENCE TIMELINE")
    if not events:
        print("No child attendance rows for this date.")
        return

    events.sort(key=lambda item: (item["time"], item["id"]))
    selected_date = datetime.strptime(day_text, "%Y-%m-%d").date()
    start_time = datetime.combine(selected_date, datetime.min.time()).replace(hour=6)
    end_time = max(start_time, ceil_to_interval(events[-1]["time"], 15))
    current = {}
    event_index = 0
    slot_time = start_time

    while slot_time <= end_time:
        applied = []
        while event_index < len(events) and events[event_index]["time"] <= slot_time:
            event = events[event_index]
            if event["event_type"] == "checkin":
                current[event["person_id"]] = event
            elif event["event_type"] == "checkout":
                current.pop(event["person_id"], None)
            applied.append(event)
            event_index += 1

        class_counts = {}
        for event in current.values():
            class_counts[event["class_name"]] = class_counts.get(event["class_name"], 0) + 1
        class_text = "; ".join(f"{name}: {count}" for name, count in sorted(class_counts.items()))
        names = ", ".join(sorted(event["name"] for event in current.values()))
        print(f"{slot_time:%H:%M} | present={len(current)} | {class_text}")
        print(f"       names: {names}")
        if applied:
            print("       events applied up to this time:")
            for event in applied:
                print(f"       - {event['time']:%H:%M:%S} {event['event_type']} {event['name']} id={event['id']}")
        slot_time += timedelta(minutes=15)


def main():
    parser = argparse.ArgumentParser(description="Inspect raw attendance rows and 15-minute presence summary.")
    parser.add_argument("--date", required=True, help="Date to inspect, format YYYY-MM-DD.")
    parser.add_argument("--db", default=str(DB_PATH), help="SQLite database path.")
    args = parser.parse_args()

    day_text = datetime.strptime(args.date, "%Y-%m-%d").strftime("%Y-%m-%d")
    db_path = Path(args.db)
    if not db_path.exists():
        raise SystemExit(f"Database not found: {db_path}")

    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    rows = load_rows(conn, day_text)

    print(f"Database: {db_path}")
    print(f"Date: {day_text}")
    print(f"Total rows: {len(rows)}\n")
    print_raw_rows(rows)
    print_duplicate_warnings(rows)
    print_future_like_rows(rows, day_text)
    print_timeline(rows, day_text)


if __name__ == "__main__":
    main()
