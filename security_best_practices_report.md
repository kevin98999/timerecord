# Security hardening report

## Executive summary

The requested review found and fixed two high-impact web issues: authenticated state-changing requests had no CSRF token validation, and user-controlled names were interpolated into JavaScript strings inside HTML event attributes. Login throttling and the attendance export query were also hardened. No unescaped user-controlled value was found in the remaining server-generated teacher-record or dashboard-chart HTML fragments.

## Fixed findings

### CSRF-001 - Authenticated POST requests accepted without an anti-CSRF token (High)

- A per-user HMAC token is now injected into every server-rendered POST form.
- Same-origin non-GET fetch requests automatically carry the token in the X-CSRF-Token header.
- JavaScript-created forms are protected, including direct calls to form.submit().
- The server rejects missing or invalid tokens before authenticated mutation routes run.
- Request bodies are cached so multipart and URL-encoded bodies can be validated and then parsed by the route without being consumed twice.

### AUTH-001 - Unlimited password attempts (Medium)

- Five consecutive failed attempts lock the account for 15 minutes.
- Locked accounts reject valid and invalid passwords using the same public response.
- Expired locks and successful authentication reset the counters.
- Failure and lock events are written to the audit log when request context is available.
- Release probes disable failure tracking so health checks cannot lock a real account.

### XSS-ATTR-001 - User names embedded in inline JavaScript confirmation strings (High)

Child, teacher, and account names had been HTML-escaped but were still placed inside JavaScript string literals in event-handler attributes. Browsers decode HTML entities before compiling the handler, so a quote in stored input could break the JavaScript context. Dynamic names were removed from these inline confirmation strings. Dashboard class and date JavaScript defaults now use JSON encoding.

### PERF-EXPORT-001 - Repeated attendance export audit lookups (Medium)

Modern attendance rows now read their stored source and operator directly. The correlated audit-log fallback executes only for legacy rows that do not have an operator, reducing repeated audit-table work while retaining old-data compatibility.

## Residual observations

- Two UI areas intentionally insert server-generated HTML returned by same-origin JSON endpoints. Their generators were reviewed: text fields use html.escape, URLs are generated from server-side file tokens, and chart geometry is numeric. Keep this escaping contract if those fragments are changed.
- Public anonymous forms do not carry a user-bound CSRF token. They do not use an authenticated browser session; abuse controls such as rate limiting and origin checking can be added separately if these endpoints become a target.

## Verification

- Python syntax compilation passed.
- Project release readiness passed: 17 checks, 0 failures, 3 existing configuration warnings.
- Isolated security regression passed for the five-attempt lock, locked valid-password rejection, expiry reset, form token injection, JSON header validation, and dynamic-form protection.
- Teacher-hours export regression passed all checks, including project isolation, authorization, range limits, and workbook validity.
