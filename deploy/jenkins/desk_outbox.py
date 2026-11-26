"""Store signed desk verdict inputs independently of proof execution."""

import argparse
import json
import sqlite3
import time
from contextlib import closing
from pathlib import Path
from urllib.error import HTTPError, URLError

from desk_verdict import send_verdict


def initialize(db):
    db.execute("""CREATE TABLE IF NOT EXISTS desk_outbox (
        run INTEGER NOT NULL, attempt INTEGER NOT NULL, payload BLOB NOT NULL,
        retries INTEGER NOT NULL DEFAULT 0, retry_at INTEGER NOT NULL DEFAULT 0,
        delivered INTEGER NOT NULL DEFAULT 0, error TEXT,
        PRIMARY KEY (run, attempt)
    )""")


def enqueue(db, record):
    run, attempt = record["run_id"], record["run_attempt"]
    if (type(run) is not int or run < 1 or type(attempt) is not int or attempt < 1
            or record["verdict"] not in ("ACCEPTED", "REJECTED")):
        raise ValueError("Invalid desk verdict identity or conclusion")
    payload = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    if len(payload) > 262144:
        raise ValueError("Desk verdict exceeds the API limit")
    with db:
        db.execute("INSERT OR IGNORE INTO desk_outbox (run, attempt, payload) VALUES (?, ?, ?)",
                   (run, attempt, payload))
        previous = db.execute("SELECT payload FROM desk_outbox WHERE run=? AND attempt=?",
                              (run, attempt)).fetchone()
        if previous[0] != payload:
            raise ValueError("The run attempt already has a different verdict")


def drain(db, url, secret):
    now = int(time.time())
    rows = db.execute("""SELECT run,attempt,payload,retries FROM desk_outbox
                         WHERE delivered=0 AND retry_at<=? ORDER BY run,attempt LIMIT 20""", (now,))
    for run, attempt, payload, retries in rows.fetchall():
        try:
            send_verdict(url, secret, payload)
        except HTTPError as error:
            retry_after = error.headers.get("Retry-After", "")
            delay = min(3600, 30 * 2 ** min(retries, 7))
            if retry_after.isdecimal():
                delay = max(delay, int(retry_after))
            message = f"HTTP {error.code}"
        except (URLError, TimeoutError, RuntimeError, json.JSONDecodeError) as error:
            delay = min(3600, 30 * 2 ** min(retries, 7))
            message = type(error).__name__
        else:
            with db:
                db.execute("UPDATE desk_outbox SET delivered=1,error=NULL WHERE run=? AND attempt=?",
                           (run, attempt))
            continue
        with db:
            db.execute("""UPDATE desk_outbox SET retries=retries+1,retry_at=?,error=?
                          WHERE run=? AND attempt=?""", (int(time.time()) + delay, message, run, attempt))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=Path)
    parser.add_argument("--verdict-url", required=True)
    parser.add_argument("--secret-file", required=True, type=Path)
    args = parser.parse_args()
    with closing(sqlite3.connect(args.database.resolve().as_uri() + "?mode=rw", uri=True, timeout=15)) as db:
        initialize(db)
        drain(db, args.verdict_url, args.secret_file.read_bytes().strip())


if __name__ == "__main__":
    main()
