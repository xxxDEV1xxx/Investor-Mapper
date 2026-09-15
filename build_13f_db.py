"""
build_13f_db.py -- SEC Form 13F ingest -> 13f_holdings.db
Download a file from here and unzip, then point this at it
https://www.sec.gov/data-research/sec-markets-data/form-13f-data-sets

Run ONCE per downloaded quarter folder. Streams INFOTABLE.tsv (large) in
chunks, loads COVERPAGE.tsv + SUMMARYPAGE.tsv (small) whole, geocodes each
DISTINCT filer HQ once via the free US Census Geocoder (cached in the DB,
so re-running never re-geocodes an address already seen), and writes
everything into one SQLite file that holders_map.py queries instantly --
no TSV re-parsing, ever, after this runs.

Re-running against a NEW quarter's folder appends to the same DB (accession
numbers are globally unique across quarters, so nothing collides).

Usage:
    python build_13f_db.py --data-dir "J:\\01mar2026-31may2026_form13f"
    python build_13f_db.py --data-dir "J:\\...\\another_quarter" --skip-geocode
"""

import argparse
import json
import ssl
import sqlite3
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path

import pandas as pd

DB_PATH = Path(r"J:\True-Sentinel\Investor-Mapper\13f_holdings.db")
CHUNK_SIZE = 200_000
GEOCODE_UA = "Mozilla/5.0 (compatible; local-research-script)"

SCHEMA = """
CREATE TABLE IF NOT EXISTS holdings (
    accession_number TEXT,
    infotable_sk      TEXT,
    nameofissuer      TEXT,
    cusip             TEXT,
    value             REAL,
    sshprnamt         REAL,
    sshprnamttype     TEXT,
    PRIMARY KEY (accession_number, infotable_sk)
);
CREATE INDEX IF NOT EXISTS ix_holdings_cusip      ON holdings(cusip);
CREATE INDEX IF NOT EXISTS ix_holdings_accession  ON holdings(accession_number);
CREATE INDEX IF NOT EXISTS ix_holdings_issuer     ON holdings(nameofissuer);

CREATE TABLE IF NOT EXISTS filers (
    accession_number TEXT PRIMARY KEY,
    report_period     TEXT,
    is_amendment      TEXT,
    manager_name      TEXT,
    street1           TEXT,
    city              TEXT,
    state_or_country  TEXT,
    zipcode           TEXT,
    lat               REAL,
    lon               REAL
);

CREATE TABLE IF NOT EXISTS summary (
    accession_number  TEXT PRIMARY KEY,
    table_value_total REAL
);

CREATE TABLE IF NOT EXISTS geocode_cache (
    address_key TEXT PRIMARY KEY,
    lat REAL,
    lon REAL
);
"""


def ssl_context():
    try:
        import truststore
        return truststore.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    except Exception:
        pass
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


def http_json(url, tries=3, timeout=20):
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": GEOCODE_UA})
            with urllib.request.urlopen(req, timeout=timeout, context=ssl_context()) as r:
                return json.loads(r.read().decode("utf-8", "replace"))
        except Exception as e:
            last = e
            time.sleep(1.0 * (i + 1))
    print(f"  [WARN] geocode request failed: {url}\n         -> {last}")
    return None


def geocode_address(street1, city, state_or_country, zipcode):
    """US Census Geocoder -- free, official, keyless. Needs a street address,
    matches against real TIGER/Line ranges. Foreign filers won't match --
    that's expected, not an error."""
    if not street1 or not city:
        return None, None
    params = {
        "street": street1, "city": city,
        "state": state_or_country, "zip": zipcode or "",
        "benchmark": "Public_AR_Current", "format": "json",
    }
    url = ("https://geocoding.geo.census.gov/geocoder/locations/address?"
           + urllib.parse.urlencode(params))
    data = http_json(url)
    matches = (data or {}).get("result", {}).get("addressMatches", [])
    if not matches:
        return None, None
    coords = matches[0]["coordinates"]
    return float(coords["y"]), float(coords["x"])  # lat, lon


def address_key(street1, city, state_or_country, zipcode):
    return "|".join(str(x or "").strip().upper()
                     for x in (street1, city, state_or_country, zipcode))


def ingest_holdings(conn, data_dir: Path):
    path = data_dir / "INFOTABLE.tsv"
    if not path.exists():
        sys.exit(f"[ERROR] Missing: {path}")

    print(f"[NOTE] Ingesting {path.name} ({path.stat().st_size/1e6:,.0f} MB)...")
    cols = ["ACCESSION_NUMBER", "INFOTABLE_SK", "NAMEOFISSUER", "CUSIP",
            "VALUE", "SSHPRNAMT", "SSHPRNAMTTYPE"]
    total = 0
    cur = conn.cursor()
    for chunk in pd.read_csv(path, sep="\t", usecols=cols, dtype=str,
                              chunksize=CHUNK_SIZE):
        chunk["VALUE"] = pd.to_numeric(chunk["VALUE"], errors="coerce")
        chunk["SSHPRNAMT"] = pd.to_numeric(chunk["SSHPRNAMT"], errors="coerce")
        rows = list(chunk[cols].itertuples(index=False, name=None))
        cur.executemany(
            "INSERT OR IGNORE INTO holdings "
            "(accession_number, infotable_sk, nameofissuer, cusip, value, "
            "sshprnamt, sshprnamttype) VALUES (?,?,?,?,?,?,?)", rows)
        total += len(rows)
        print(f"  {total:,} rows...", end="\r", flush=True)
    conn.commit()
    print(f"\n[NOTE] holdings: {total:,} rows staged.")


def ingest_filers(conn, data_dir: Path, skip_geocode: bool):
    path = data_dir / "COVERPAGE.tsv"
    if not path.exists():
        sys.exit(f"[ERROR] Missing: {path}")

    print(f"[NOTE] Ingesting {path.name}...")
    cover = pd.read_csv(path, sep="\t", dtype=str, usecols=[
        "ACCESSION_NUMBER", "REPORTCALENDARORQUARTER", "ISAMENDMENT",
        "FILINGMANAGER_NAME", "FILINGMANAGER_STREET1", "FILINGMANAGER_CITY",
        "FILINGMANAGER_STATEORCOUNTRY", "FILINGMANAGER_ZIPCODE"])

    cur = conn.cursor()
    cached = dict(cur.execute("SELECT address_key, lat FROM geocode_cache "
                               "WHERE lat IS NOT NULL").fetchall())
    cached_lonmap = dict(cur.execute("SELECT address_key, lon FROM geocode_cache "
                                      "WHERE lon IS NOT NULL").fetchall())
    known_keys = set(r[0] for r in cur.execute(
        "SELECT address_key FROM geocode_cache").fetchall())

    to_geocode = []
    seen_keys = set()
    for _, row in cover.iterrows():
        k = address_key(row["FILINGMANAGER_STREET1"], row["FILINGMANAGER_CITY"],
                         row["FILINGMANAGER_STATEORCOUNTRY"], row["FILINGMANAGER_ZIPCODE"])
        if k and k not in known_keys and k not in seen_keys:
            seen_keys.add(k)
            to_geocode.append((k, row["FILINGMANAGER_STREET1"], row["FILINGMANAGER_CITY"],
                                row["FILINGMANAGER_STATEORCOUNTRY"], row["FILINGMANAGER_ZIPCODE"]))

    if not skip_geocode and to_geocode:
        print(f"[NOTE] Geocoding {len(to_geocode):,} new filer HQs "
              f"(cached: {len(known_keys):,} already done)...")
        for i, (k, street1, city, state, zipc) in enumerate(to_geocode):
            lat, lon = geocode_address(street1, city, state, zipc)
            cur.execute("INSERT OR REPLACE INTO geocode_cache (address_key, lat, lon) "
                        "VALUES (?,?,?)", (k, lat, lon))
            if lat is not None:
                cached[k] = lat
                cached_lonmap[k] = lon
            if (i + 1) % 25 == 0:
                conn.commit()
            time.sleep(0.3)
            print(f"  geocoded {i+1}/{len(to_geocode)}...", end="\r", flush=True)
        conn.commit()
        print()
    elif skip_geocode:
        print("[NOTE] --skip-geocode: new filer HQs will have no lat/lon this run.")

    rows = []
    for _, row in cover.iterrows():
        k = address_key(row["FILINGMANAGER_STREET1"], row["FILINGMANAGER_CITY"],
                         row["FILINGMANAGER_STATEORCOUNTRY"], row["FILINGMANAGER_ZIPCODE"])
        lat = cached.get(k)
        lon = cached_lonmap.get(k)
        rows.append((
            row["ACCESSION_NUMBER"], row["REPORTCALENDARORQUARTER"], row["ISAMENDMENT"],
            row["FILINGMANAGER_NAME"], row["FILINGMANAGER_STREET1"], row["FILINGMANAGER_CITY"],
            row["FILINGMANAGER_STATEORCOUNTRY"], row["FILINGMANAGER_ZIPCODE"], lat, lon,
        ))
    cur.executemany(
        "INSERT OR REPLACE INTO filers (accession_number, report_period, is_amendment, "
        "manager_name, street1, city, state_or_country, zipcode, lat, lon) "
        "VALUES (?,?,?,?,?,?,?,?,?,?)", rows)
    conn.commit()
    geocoded = sum(1 for r in rows if r[8] is not None)
    print(f"[NOTE] filers: {len(rows):,} rows staged ({geocoded:,} with HQ coordinates).")


def ingest_summary(conn, data_dir: Path):
    path = data_dir / "SUMMARYPAGE.tsv"
    if not path.exists():
        sys.exit(f"[ERROR] Missing: {path}")
    print(f"[NOTE] Ingesting {path.name}...")
    summary = pd.read_csv(path, sep="\t", dtype=str,
                           usecols=["ACCESSION_NUMBER", "TABLEVALUETOTAL"])
    summary["TABLEVALUETOTAL"] = pd.to_numeric(summary["TABLEVALUETOTAL"], errors="coerce")
    rows = list(summary.itertuples(index=False, name=None))
    conn.executemany(
        "INSERT OR REPLACE INTO summary (accession_number, table_value_total) "
        "VALUES (?,?)", rows)
    conn.commit()
    print(f"[NOTE] summary: {len(rows):,} rows staged.")


def main():
    ap = argparse.ArgumentParser(description="SEC 13F -> SQLite master file")
    ap.add_argument("--data-dir", required=True)
    ap.add_argument("--db", default=str(DB_PATH))
    ap.add_argument("--skip-geocode", action="store_true")
    args = ap.parse_args()

    data_dir = Path(args.data_dir)
    if not data_dir.exists():
        sys.exit(f"[ERROR] --data-dir not found: {data_dir}")

    db_path = Path(args.db)
    db_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(db_path)
    conn.executescript(SCHEMA)
    conn.execute("PRAGMA synchronous=OFF")
    conn.execute("PRAGMA journal_mode=MEMORY")
    conn.commit()
    print(f"[NOTE] DB: {db_path}")

    ingest_holdings(conn, data_dir)
    ingest_filers(conn, data_dir, args.skip_geocode)
    ingest_summary(conn, data_dir)

    n_holdings = conn.execute("SELECT COUNT(*) FROM holdings").fetchone()[0]
    n_filers = conn.execute("SELECT COUNT(*) FROM filers").fetchone()[0]
    n_geo = conn.execute("SELECT COUNT(*) FROM filers WHERE lat IS NOT NULL").fetchone()[0]
    print(f"\n[NOTE] Master DB totals: {n_holdings:,} holdings, {n_filers:,} filer-quarters, "
          f"{n_geo:,} geocoded HQs.")
    conn.close()


if __name__ == "__main__":
    main()