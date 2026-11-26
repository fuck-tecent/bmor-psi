"""Receive signed GitHub App events for the Jenkins dispatcher."""

import hashlib
import hmac
import json
import os
import re
import sqlite3
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

REPOSITORY = "CGandGameEngineLearner/goldbach-proofs"
INSTALLATION = 186036038
EVENTS = {"pull_request", "issue_comment", "push", "check_run"}
MAX_BODY = 25 * 1024 * 1024


class Receiver(BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path != "/github/webhook":
            self.send_error(404)
            return
        self.connection.settimeout(10)
        size = self.headers.get("Content-Length", "")
        if not re.fullmatch(r"[0-9]{1,8}", size) or not 0 < int(size) <= MAX_BODY:
            self.send_error(413)
            return
        try:
            raw = self.rfile.read(int(size))
        except TimeoutError:
            self.send_error(408)
            return
        if len(raw) != int(size):
            self.send_error(400)
            return
        expected = "sha256=" + hmac.new(self.server.secret, raw, hashlib.sha256).hexdigest()
        supplied = self.headers.get("X-Hub-Signature-256", "")
        if not supplied.isascii() or not hmac.compare_digest(expected, supplied):
            self.send_error(401)
            return

        event = self.headers.get("X-GitHub-Event", "")
        delivery = self.headers.get("X-GitHub-Delivery", "")
        if event not in EVENTS:
            self.respond(204)
            return
        if not re.fullmatch(r"[0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}", delivery):
            self.send_error(400)
            return
        try:
            payload = json.loads(raw)
            repository = payload["repository"]["full_name"]
            installation = payload["installation"]["id"]
        except (UnicodeError, ValueError, TypeError, KeyError):
            self.send_error(400)
            return
        if repository != REPOSITORY or installation != INSTALLATION:
            self.send_error(403)
            return
        try:
            with sqlite3.connect(self.server.database) as db:
                inserted = db.execute(
                    "INSERT INTO deliveries (id,event,body) VALUES (?,?,?) ON CONFLICT(id) DO NOTHING",
                    (delivery.lower(), event, raw),
                ).rowcount
                if not inserted:
                    previous = db.execute(
                        "SELECT event,body FROM deliveries WHERE id=?", (delivery.lower(),),
                    ).fetchone()
                    if previous != (event, raw):
                        self.send_error(409)
                        return
        except sqlite3.Error:
            self.send_error(503)
            return
        self.respond(202)

    def respond(self, status):
        self.send_response(status)
        self.send_header("Content-Length", "0")
        self.end_headers()


def main():
    database = os.environ["GOLDBACH_WEBHOOK_DB"]
    with sqlite3.connect(database) as db:
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("""CREATE TABLE IF NOT EXISTS deliveries (
            id TEXT PRIMARY KEY, event TEXT NOT NULL, body BLOB NOT NULL,
            received_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )""")
    secret = Path(os.environ["GOLDBACH_WEBHOOK_SECRET_FILE"]).read_bytes().strip()
    if len(secret) < 32:
        raise ValueError("Webhook secret is too short")
    with ThreadingHTTPServer(("127.0.0.1", 18081), Receiver) as server:
        server.secret = secret
        server.database = database
        server.serve_forever()


if __name__ == "__main__":
    main()
