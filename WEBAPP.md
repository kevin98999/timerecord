# Kindergarten Attendance Web

Run:

```powershell
cd D:\codextest\timerecord
python webapp.py --host 0.0.0.0 --port 8000
```

Open on this computer:

- http://127.0.0.1:8000

Open from another computer on the same LAN:

- Use the LAN URL printed after startup, for example: http://192.168.4.60:8000
- If the computer reconnects to Wi-Fi, the IP can change. Run `ipconfig` and use the current `IPv4 Address`.
- Do not use an old address such as `192.168.4.44` after the PC has changed to another IP.

Seeded accounts:

- `boss / Boss123!`
- `principal / Principal123!`
- `cook / Cook123!`
- `ky / Teacher123!`

Notes:

- The web app reads the existing attendance data.
- If the main SQLite file is locked, it creates a working copy under `data\attendance_web_*.db`.
- Teacher attendance uses a 30-minute cooldown.
- Closed dates are managed from the web UI and stored in `data\settings.json`.
