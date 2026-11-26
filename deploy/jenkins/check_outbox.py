"""Publish completed Jenkins checks from a durable, single-consumer outbox."""

import argparse
import json
import re
import sqlite3
import time
from contextlib import closing
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode

from github_app import APP_ID, GitHubApp, RateLimited

REPO = "/repos/CGandGameEngineLearner/goldbach-proofs"
CHECKS = {
    "authoritative-pr": "Goldbach CI / formal Lean verdict",
    "advisory-pr": "Goldbach CI / Lean advisory",
    "advisory-replay": "Goldbach CI / Jenkins Lean replay",
    "grh": "Goldbach CI / GRH source",
    "grh-pr": "Goldbach CI / GRH source PR",
    "grh-replay": "Goldbach CI / Jenkins GRH replay",
    "site": "Goldbach CI / site release",
    "site-pr": "Goldbach CI / website PR",
    "catalogue-pr": "Goldbach CI / catalogue PR",
    "site-replay": "Goldbach CI / Jenkins site replay",
    "catalogue": "Goldbach CI / catalogue release",
}
CONCLUSIONS = ("success", "failure", "neutral", "cancelled", "timed_out")


def database(path):
    db = sqlite3.connect(path, timeout=15)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA journal_mode=WAL")
    db.execute("""CREATE TABLE IF NOT EXISTS checks (
        external_id TEXT PRIMARY KEY, sha TEXT NOT NULL, name TEXT NOT NULL,
        conclusion TEXT NOT NULL, summary TEXT NOT NULL, attempts INTEGER NOT NULL DEFAULT 0,
        retry_at INTEGER NOT NULL DEFAULT 0, check_id INTEGER, published INTEGER NOT NULL DEFAULT 0
    )""")
    db.execute("""CREATE TABLE IF NOT EXISTS check_cooldown (
        id INTEGER PRIMARY KEY CHECK (id=1), retry_at INTEGER NOT NULL
    )""")
    return db


def enqueue(db, kind, sha, conclusion, summary, *, pr=0, run_id=None):
    if not re.fullmatch(r"[a-f0-9]{40}", sha):
        raise ValueError("Expected a full commit SHA")
    external_id = f"pr:{pr}:{kind}:{sha}" if pr else f"main:{kind}:{sha}"
    if run_id is not None:
        if type(run_id) is not int or run_id < 1:
            raise ValueError("Invalid verdict run ID")
        external_id += f":{run_id}"
    with db:
        db.execute("""INSERT INTO checks (external_id, sha, name, conclusion, summary)
                      VALUES (?, ?, ?, ?, ?) ON CONFLICT(external_id) DO NOTHING""",
                   (external_id, sha, CHECKS[kind], conclusion, summary))


def publish(db, app, row):
    check_id = row["check_id"]
    if check_id is None:
        query = urlencode({"check_name": row["name"], "app_id": APP_ID, "per_page": 100})
        found = app.request("GET", f'{REPO}/commits/{row["sha"]}/check-runs?{query}')
        for check in found["check_runs"]:
            if (check.get("external_id") == row["external_id"]
                    and check.get("head_sha") == row["sha"]
                    and (check.get("app") or {}).get("id") == APP_ID):
                check_id = check["id"]
                break
    payload = {"status": "completed", "conclusion": row["conclusion"],
               "output": {"title": row["name"], "summary": row["summary"]}}
    if check_id is None:
        check = app.request("POST", f"{REPO}/check-runs",
                            payload | {"name": row["name"], "head_sha": row["sha"],
                                       "external_id": row["external_id"]})
    else:
        check = app.request("PATCH", f"{REPO}/check-runs/{check_id}", payload)
    with db:
        db.execute("UPDATE checks SET check_id=?, published=1 WHERE external_id=?",
                   (check["id"], row["external_id"]))


def drain(db, app):
    now = int(time.time())
    cooldown = db.execute("SELECT retry_at FROM check_cooldown WHERE id=1").fetchone()
    if cooldown and cooldown["retry_at"] > now:
        return
    for row in db.execute(
            "SELECT * FROM checks WHERE published=0 AND retry_at<=? ORDER BY rowid LIMIT 20",
            (now,)).fetchall():
        try:
            publish(db, app, row)
        except RateLimited as error:
            with db:
                db.execute("""INSERT INTO check_cooldown VALUES (1,?)
                              ON CONFLICT(id) DO UPDATE
                              SET retry_at=max(retry_at,excluded.retry_at)""", (error.retry_at,))
            break
        except (HTTPError, URLError, TimeoutError):
            delay = min(3600, 30 * 2 ** min(row["attempts"], 7))
            with db:
                db.execute("UPDATE checks SET attempts=attempts+1, retry_at=? WHERE external_id=?",
                           (int(time.time()) + delay, row["external_id"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True)
    commands = parser.add_subparsers(dest="command", required=True)
    put = commands.add_parser("enqueue")
    put.add_argument("kind", choices=CHECKS)
    put.add_argument("sha")
    put.add_argument("conclusion", choices=CONCLUSIONS)
    put.add_argument("summary")
    send = commands.add_parser("drain")
    send.add_argument("--private-key", required=True)
    args = parser.parse_args()
    with closing(database(args.database)) as db:
        if args.command == "enqueue":
            enqueue(db, args.kind, args.sha, args.conclusion, args.summary)
        else:
            drain(db, GitHubApp(args.private_key))


if __name__ == "__main__":
    main()
