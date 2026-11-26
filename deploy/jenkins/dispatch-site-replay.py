"""Dispatch one signed, fixed-revision website replay in staging."""

import argparse
import json
import sqlite3
from contextlib import closing
from pathlib import Path

from jenkins_client import Jenkins

REPLAY_SHA = "0b2a2c36f712e43ff940f9cc314ff6a89197176f"


def dispatch(db, client, delivery_id):
    db.execute("""CREATE TABLE IF NOT EXISTS staging_dispatches (
        delivery_id TEXT PRIMARY KEY, queue_id INTEGER NOT NULL
    )""")
    with db:
        db.execute("BEGIN IMMEDIATE")
        existing = db.execute("SELECT queue_id FROM staging_dispatches WHERE delivery_id=?",
                              (delivery_id,)).fetchone()
        if existing:
            return existing[0]
        row = db.execute("SELECT event,body FROM deliveries WHERE id=?", (delivery_id,)).fetchone()
        if not row or row[0] != "push":
            raise ValueError("Expected a recorded push delivery")
        body = json.loads(row[1])
        if body.get("ref") != "refs/heads/main" or body.get("after") != REPLAY_SHA:
            raise ValueError("Delivery does not match the fixed staging source")
        queue_id = client.enqueue("goldbach-site-replay")
        db.execute("INSERT INTO staging_dispatches VALUES (?,?)", (delivery_id, queue_id))
        return queue_id


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database")
    parser.add_argument("delivery_id")
    parser.add_argument("credential_file", type=Path)
    args = parser.parse_args()
    client = Jenkins("http://127.0.0.1:18080", "goldbach-admin",
                     args.credential_file.read_text().strip())
    with closing(sqlite3.connect(args.database, timeout=30)) as db:
        print(dispatch(db, client, args.delivery_id))


if __name__ == "__main__":
    main()
