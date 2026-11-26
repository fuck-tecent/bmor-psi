"""Persist routed checks with their exact GitHub revision."""

import json
import re
import time

from event_routes import route

SHA = re.compile(r"[0-9a-f]{40}")


def initialize(db):
    db.executescript("""
        CREATE TABLE IF NOT EXISTS routed_deliveries (
            id TEXT PRIMARY KEY
        );
        CREATE TABLE IF NOT EXISTS ci_jobs (
            id INTEGER PRIMARY KEY,
            kind TEXT NOT NULL,
            sha TEXT NOT NULL,
            pr INTEGER NOT NULL,
            trigger TEXT NOT NULL,
            source_delivery TEXT NOT NULL,
            UNIQUE(kind, sha, pr, trigger)
        );
        CREATE TABLE IF NOT EXISTS desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL);
    """)


def enqueue_delivery(db, delivery_id, event, payload, changed_paths, *,
                     comment_head=None, grh_enabled=True):
    """The consumer supplies API-verified changed paths and the current comment PR head."""
    if event == "pull_request":
        sha = payload["pull_request"]["head"]["sha"]
        pr = payload["number"]
    elif event == "issue_comment":
        sha = comment_head
        pr = payload["issue"]["number"]
    else:
        sha = payload.get("after")
        pr = 0

    jobs = route(event, payload, None if changed_paths is None else tuple(changed_paths),
                 grh_enabled=grh_enabled)
    if jobs and (not isinstance(sha, str) or not SHA.fullmatch(sha) or sha == "0" * 40
                 or type(pr) is not int or pr < (0 if event == "push" else 1)):
        raise ValueError("Delivery does not identify a valid revision")

    with db:
        added = db.execute("INSERT OR IGNORE INTO routed_deliveries VALUES (?)",
                           (delivery_id,))
        if not added.rowcount:
            return 0
        count = 0
        for kind in jobs:
            trigger = str(payload["comment"]["id"]) if kind == "authoritative" else ""
            result = db.execute(
                """INSERT OR IGNORE INTO ci_jobs
                (kind, sha, pr, trigger, source_delivery) VALUES (?, ?, ?, ?, ?)""",
                (kind, sha, pr, trigger, delivery_id),
            )
            count += result.rowcount
        return count


def pending_deliveries(db, limit=20):
    rows = db.execute("""SELECT d.id, d.event, d.body FROM deliveries d
                         WHERE NOT EXISTS (SELECT 1 FROM routed_deliveries r WHERE r.id=d.id)
                         ORDER BY d.rowid LIMIT ?""", (limit,))
    return [(delivery, event, json.loads(body)) for delivery, event, body in rows]

def desk_run_id(db, job_id):
    """Reserve a time-ordered numeric ID once for an authoritative job."""
    with db:
        db.execute("""INSERT OR IGNORE INTO desk_runs (job_id, run_id)
                      SELECT id, max(?, (SELECT coalesce(max(run_id), 0) + 1 FROM desk_runs))
                      FROM ci_jobs WHERE id=? AND kind='authoritative'""",
                   (time.time_ns() // 1000, job_id))
        row = db.execute("SELECT run_id FROM desk_runs WHERE job_id=?", (job_id,)).fetchone()
        if not row:
            raise ValueError("Only authoritative jobs can acquire a desk run ID")
        return row[0]
