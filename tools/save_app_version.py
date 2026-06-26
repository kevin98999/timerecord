import argparse
import json
import os
import re
import zipfile
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSIONS_DIR = ROOT / ".app_versions"
HISTORY_PATH = ROOT / "APP_VERSION_HISTORY.md"
MANIFEST_PATH = VERSIONS_DIR / "manifest.json"

EXCLUDED_DIRS = {
    ".app_versions",
    ".git",
    ".agents",
    ".codex",
    "__pycache__",
    ".chrome-pdf-profile",
    ".edge-pdf-profile",
}
EXCLUDED_SUFFIXES = {".pyc", ".log", ".err", ".journal"}


def load_manifest():
    if MANIFEST_PATH.exists():
        return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    return {"versions": []}


def next_version_id(manifest):
    today = datetime.now().strftime("%Y%m%d")
    pattern = re.compile(rf"^v{today}-(\d{{3}})$")
    max_seq = 0
    for item in manifest.get("versions", []):
        match = pattern.match(item.get("version", ""))
        if match:
            max_seq = max(max_seq, int(match.group(1)))
    return f"v{today}-{max_seq + 1:03d}"


def should_include(path):
    rel_parts = path.relative_to(ROOT).parts
    if any(part in EXCLUDED_DIRS for part in rel_parts):
        return False
    if path.suffix.lower() in EXCLUDED_SUFFIXES:
        return False
    return path.is_file()


def iter_files():
    for path in ROOT.rglob("*"):
        if should_include(path):
            yield path


def main():
    parser = argparse.ArgumentParser(description="Save a rollback snapshot for the app.")
    parser.add_argument("note", nargs="?", default="manual snapshot")
    args = parser.parse_args()

    VERSIONS_DIR.mkdir(exist_ok=True)
    manifest = load_manifest()
    version = next_version_id(manifest)
    created_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    zip_path = VERSIONS_DIR / f"{version}.zip"

    files = list(iter_files())
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in files:
            zf.write(path, path.relative_to(ROOT).as_posix())

    record = {
        "version": version,
        "created_at": created_at,
        "note": args.note,
        "archive": zip_path.relative_to(ROOT).as_posix(),
        "file_count": len(files),
    }
    manifest.setdefault("versions", []).append(record)
    MANIFEST_PATH.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")

    if not HISTORY_PATH.exists():
        HISTORY_PATH.write_text("# App Version History\n\n", encoding="utf-8")
    with HISTORY_PATH.open("a", encoding="utf-8") as fh:
        fh.write(f"- `{version}` - {created_at} - {args.note} - {len(files)} files - `{record['archive']}`\n")

    print(version)


if __name__ == "__main__":
    main()
