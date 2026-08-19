# App Versioning

Before changing this app, save a rollback snapshot:

```powershell
python tools/save_app_version.py "before: short description of requested change"
```

Tell the user the generated version number. To restore a previous version:

```powershell
python tools/restore_app_version.py vYYYYMMDD-001 --yes
```

Version archives are stored in `.app_versions/`. Human-readable history is stored in `APP_VERSION_HISTORY.md`.
