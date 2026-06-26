import argparse
import json
import shutil
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSIONS_DIR = ROOT / ".app_versions"
MANIFEST_PATH = VERSIONS_DIR / "manifest.json"


def main():
    parser = argparse.ArgumentParser(description="Restore an app snapshot by version id.")
    parser.add_argument("version", help="Version id, for example v20260624-001")
    parser.add_argument("--yes", action="store_true", help="Restore without interactive confirmation")
    args = parser.parse_args()

    if not MANIFEST_PATH.exists():
        raise SystemExit("No version manifest found.")
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    record = next((item for item in manifest.get("versions", []) if item.get("version") == args.version), None)
    if not record:
        raise SystemExit(f"Version not found: {args.version}")

    archive = ROOT / record["archive"]
    if not archive.exists():
        raise SystemExit(f"Archive not found: {archive}")

    if not args.yes:
        answer = input(f"Restore {args.version} from {archive}? This overwrites matching files. Type YES: ")
        if answer != "YES":
            raise SystemExit("Restore cancelled.")

    pre_restore = VERSIONS_DIR / f"before_restore_{args.version}.zip"
    with zipfile.ZipFile(pre_restore, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in ROOT.rglob("*"):
            if path.is_file() and ".app_versions" not in path.relative_to(ROOT).parts:
                zf.write(path, path.relative_to(ROOT).as_posix())

    with zipfile.ZipFile(archive, "r") as zf:
        zf.extractall(ROOT)

    print(f"Restored {args.version}")
    print(f"Pre-restore backup: {pre_restore.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
