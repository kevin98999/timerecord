import argparse
import csv
import json
import os
import sys
import time
import urllib.parse
import urllib.request
from datetime import datetime, timedelta


AMADEUS_TEST_BASE = "https://test.api.amadeus.com"
AMADEUS_PROD_BASE = "https://api.amadeus.com"


def date_range(start_text, end_text):
    start = datetime.strptime(start_text, "%Y-%m-%d").date()
    end = datetime.strptime(end_text, "%Y-%m-%d").date()
    if end < start:
        raise ValueError("End date must be after start date")
    current = start
    while current <= end:
        yield current.strftime("%Y-%m-%d")
        current += timedelta(days=1)


def http_json(url, method="GET", headers=None, data=None, timeout=30):
    body = None
    if data is not None:
        body = data.encode("utf-8")
    request = urllib.request.Request(url, data=body, method=method, headers=headers or {})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        message = exc.read().decode("utf-8", "replace")
        raise RuntimeError(f"HTTP {exc.code}: {message}") from exc


def amadeus_token(base_url, client_id, client_secret):
    payload = urllib.parse.urlencode(
        {
            "grant_type": "client_credentials",
            "client_id": client_id,
            "client_secret": client_secret,
        }
    )
    data = http_json(
        f"{base_url}/v1/security/oauth2/token",
        method="POST",
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        data=payload,
    )
    token = data.get("access_token")
    if not token:
        raise RuntimeError(f"Amadeus token response did not include access_token: {data}")
    return token


def flight_offers(base_url, token, origin, destination, departure_date, return_date, adults, currency, max_results):
    params = {
        "originLocationCode": origin,
        "destinationLocationCode": destination,
        "departureDate": departure_date,
        "returnDate": return_date,
        "adults": str(adults),
        "currencyCode": currency,
        "max": str(max_results),
    }
    url = f"{base_url}/v2/shopping/flight-offers?{urllib.parse.urlencode(params)}"
    return http_json(url, headers={"Authorization": f"Bearer {token}"})


def segment_text(offer, dictionaries):
    carriers = dictionaries.get("carriers", {}) if isinstance(dictionaries, dict) else {}
    itineraries = offer.get("itineraries", [])
    parts = []
    for idx, itinerary in enumerate(itineraries, start=1):
        labels = []
        for segment in itinerary.get("segments", []):
            carrier_code = segment.get("carrierCode", "")
            carrier = carriers.get(carrier_code, carrier_code)
            flight = f"{carrier_code}{segment.get('number', '')}"
            dep = segment.get("departure", {})
            arr = segment.get("arrival", {})
            labels.append(
                f"{flight} {carrier}: {dep.get('iataCode', '')} {dep.get('at', '')} -> "
                f"{arr.get('iataCode', '')} {arr.get('at', '')}"
            )
        parts.append(f"Leg {idx}: " + " | ".join(labels))
    return " / ".join(parts)


def search(args):
    client_id = args.client_id or os.environ.get("AMADEUS_CLIENT_ID")
    client_secret = args.client_secret or os.environ.get("AMADEUS_CLIENT_SECRET")
    if not client_id or not client_secret:
        raise RuntimeError("Set AMADEUS_CLIENT_ID and AMADEUS_CLIENT_SECRET, or pass --client-id/--client-secret")

    base_url = AMADEUS_PROD_BASE if args.production else AMADEUS_TEST_BASE
    token = amadeus_token(base_url, client_id, client_secret)
    rows = []

    for departure_date in date_range(args.depart_start, args.depart_end):
        for return_date in date_range(args.return_start, args.return_end):
            print(f"Searching {departure_date} -> {return_date}...", file=sys.stderr)
            try:
                response = flight_offers(
                    base_url,
                    token,
                    args.origin,
                    args.destination,
                    departure_date,
                    return_date,
                    args.adults,
                    args.currency,
                    args.max_per_combo,
                )
            except RuntimeError as exc:
                rows.append(
                    {
                        "departure_date": departure_date,
                        "return_date": return_date,
                        "total_price": "",
                        "currency": args.currency,
                        "airlines": "",
                        "segments": "",
                        "error": str(exc),
                    }
                )
                continue
            dictionaries = response.get("dictionaries", {})
            for offer in response.get("data", []):
                price = offer.get("price", {})
                carrier_codes = sorted(
                    {
                        segment.get("carrierCode", "")
                        for itinerary in offer.get("itineraries", [])
                        for segment in itinerary.get("segments", [])
                        if segment.get("carrierCode")
                    }
                )
                rows.append(
                    {
                        "departure_date": departure_date,
                        "return_date": return_date,
                        "total_price": price.get("grandTotal") or price.get("total") or "",
                        "currency": price.get("currency") or args.currency,
                        "airlines": "/".join(carrier_codes),
                        "segments": segment_text(offer, dictionaries),
                        "error": "",
                    }
                )
            time.sleep(args.pause)

    rows.sort(key=lambda row: float(row["total_price"]) if row["total_price"] else 999999999)
    return rows


def write_csv(path, rows):
    headers = ["departure_date", "return_date", "total_price", "currency", "airlines", "segments", "error"]
    with open(path, "w", newline="", encoding="utf-8-sig") as fh:
        writer = csv.DictWriter(fh, fieldnames=headers)
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description="Search round-trip flight prices with Amadeus Flight Offers Search.")
    parser.add_argument("--origin", default="YUL")
    parser.add_argument("--destination", default="SFO")
    parser.add_argument("--depart-start", default="2026-09-05")
    parser.add_argument("--depart-end", default="2026-09-10")
    parser.add_argument("--return-start", default="2026-09-15")
    parser.add_argument("--return-end", default="2026-09-18")
    parser.add_argument("--adults", type=int, default=2)
    parser.add_argument("--currency", default="CAD")
    parser.add_argument("--max-per-combo", type=int, default=5)
    parser.add_argument("--output", default="flight_prices_yul_sfo.csv")
    parser.add_argument("--client-id", default="")
    parser.add_argument("--client-secret", default="")
    parser.add_argument("--production", action="store_true", help="Use production API instead of test API.")
    parser.add_argument("--pause", type=float, default=0.2)
    args = parser.parse_args()

    rows = search(args)
    write_csv(args.output, rows)
    print(f"Wrote {len(rows)} rows to {args.output}")
    for row in rows[:10]:
        if row["error"]:
            continue
        print(f"{row['total_price']} {row['currency']}  depart {row['departure_date']} return {row['return_date']}  {row['airlines']}")


if __name__ == "__main__":
    main()
