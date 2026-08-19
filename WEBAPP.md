# Kindergarten Attendance Web
## Release readiness check

Run isolated acceptance tests plus read-only checks of the current deployment:

    python tools/check_release_readiness.py

Before a production release, use strict mode. It returns a non-zero exit code when warnings remain:

    python tools/check_release_readiness.py --strict

For automation or deployment pipelines:

    python tools/check_release_readiness.py --json

The acceptance portion creates a temporary database and does not modify the live application database.

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

External hosted web app:

- Set `webapp_url` and `desktop_sync_token` in `data\settings.json` on the desktop computer. Use a long random token and set the same token on the hosted web server.

```json
{
  "webapp_url": "https://your-hosted-web-app.example.com",
  "desktop_sync_token": "replace-with-a-long-random-secret"
}
```

- Or set environment variables before launching the desktop app:

```powershell
$env:TIMERECORD_WEBAPP_URL = "https://your-hosted-web-app.example.com"
$env:TIMERECORD_DESKTOP_SYNC_TOKEN = "replace-with-a-long-random-secret"
python app.py
```

- When an external URL is configured, the desktop app connects to that URL and does not start the local `webapp.py` server.
- When `desktop_sync_token` is configured on both sides, the desktop app sends each successful attendance record to `/api/desktop/attendance` on the hosted web app.

Mobile invitation email:

- Mobile invitation links can be created from `Invitations mobiles`.
- If SMTP or Amazon SES API is configured, the server sends the invitation email automatically.
- If email delivery is not configured, the page still creates the link and you can copy it manually.

Linux server example:

```bash
export TIMERECORD_PUBLIC_URL="http://174.138.37.29:8000"
export TIMERECORD_SMTP_HOST="smtp.example.com"
export TIMERECORD_SMTP_PORT="587"
export TIMERECORD_SMTP_USERNAME="your@email.com"
export TIMERECORD_SMTP_PASSWORD="your-smtp-password"
export TIMERECORD_SMTP_FROM="your@email.com"
export TIMERECORD_SMTP_TLS="1"
python3 webapp.py --host 0.0.0.0 --port 8000
```

Amazon SES API example:

```bash
export TIMERECORD_PUBLIC_URL="https://your-domain.com"
export TIMERECORD_EMAIL_PROVIDER="ses"
export TIMERECORD_SES_REGION="ca-central-1"
export TIMERECORD_SES_FROM="no-reply@your-domain.com"
export AWS_ACCESS_KEY_ID="your-access-key-id"
export AWS_SECRET_ACCESS_KEY="your-secret-access-key"
python3 webapp.py --host 0.0.0.0 --port 8000
```

For a production domain, set `TIMERECORD_PUBLIC_URL` to the public HTTPS address, for example `https://garderieunivers.com`.

Readiness check:

```bash
cd /opt/codextest/TIMERECORD
python3 tools/check_mobile_readiness.py
```

After logging in as boss or principal, the server can also be checked from:

```text
/api/health
```
