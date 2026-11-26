"""Run a fixed-repository website, catalogue, GRH or proof check per Unix socket request."""

import json
import logging
import os
import re
import socketserver
import sqlite3
import subprocess
import tempfile
from contextlib import closing
from pathlib import Path
from threading import BoundedSemaphore

from formal_proof import judge
from github_app import GitHubApp
from prepare_proof import grh_enabled, prepare
from verify_proof import verify

ROOT = Path("/opt/goldbach-ci")
TRUSTED_BASE = Path(os.environ.get("GOLDBACH_TRUSTED_BASE", ROOT / "lean-replay"))
SOCKET = Path("/run/goldbach-ci-site/runner.sock")
MAX_PARALLEL_CHECKS = 4
PROOF_GITHUB = GitHubApp("/etc/goldbach-ci/github-app.pem", request_interval=0.25)


class RunnerServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    request_queue_size = 16
    daemon_threads = True

    def __init__(self, address, handler):
        self.slots = BoundedSemaphore(MAX_PARALLEL_CHECKS)
        super().__init__(address, handler)

    def process_request(self, request, client_address):
        self.slots.acquire()
        try:
            super().process_request(request, client_address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.slots.release()


class Handler(socketserver.StreamRequestHandler):
    def handle(self):
        self.connection.settimeout(15)
        line = self.rfile.readline(80)
        formal = re.fullmatch(rb"formal ([1-9][0-9]{0,17})\n", line)
        if formal:
            result = check_formal(int(formal[1]))
            self.wfile.write(f"{result}\n".encode())
            return
        proof = re.fullmatch(rb"proof ([1-9][0-9]{0,9}) ([a-f0-9]{40})\n", line)
        if proof:
            self.wfile.write(f"{check_proof(int(proof[1]), proof[2].decode())}\n".encode())
            return
        request = re.fullmatch(rb"(catalogue |grh )?([a-f0-9]{40})\n", line)
        if request is None:
            self.wfile.write(b"2\n")
            return
        if request[1] == b"grh " and not grh_enabled():
            self.wfile.write(b"3\nGRH verification is temporarily disabled\n")
            return
        sha = request[2].decode()
        diagnostics = b""
        try:
            with tempfile.TemporaryDirectory(prefix="goldbach-site-") as temporary:
                stage = Path(temporary)
                stage.chmod(0o755)
                subprocess.run([
                    "bash", str(ROOT / "controller/prepare-site-revision.sh"), sha, str(stage),
                    str(ROOT / "site-replay/check-site.sh"),
                ], check=True, timeout=120)
                if request[1] == b"grh ":
                    command = [ROOT / "controller/run-grh-revision.sh", stage / "source.tar"]
                elif request[1]:
                    command = [ROOT / "controller/run-catalogue-revision.sh", stage / "source.tar"]
                else:
                    command = [ROOT / "replay-site.sh", stage]
                if request[1] == b"grh ":
                    completed = subprocess.run([
                        "bash", "-o", "pipefail", "-c", 'bash "$@" 2>&1 | tail -c 32768',
                        "goldbach-grh", *command,
                    ], stdout=subprocess.PIPE, timeout=1850)
                    result = completed.returncode
                    diagnostics = completed.stdout
                else:
                    result = subprocess.run(["bash", *command], timeout=1850).returncode
        except (OSError, subprocess.SubprocessError):
            result = 3
        self.wfile.write(f"{result}\n".encode() + diagnostics)


def check_proof(number, head):
    try:
        base = TRUSTED_BASE.resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="goldbach-proof-") as temporary:
            work = Path(temporary)
            file = prepare(PROOF_GITHUB, number, head, base, work)
            verify(file, work, base / "lean", ROOT / "toolchains/lean-4.36.0",
                   ROOT / "controller/build-ownership.sh")
    except (ValueError, OSError, subprocess.SubprocessError):
        logging.exception("Proof check failed for PR %s at %s", number, head)
        return 3
    return 0


def check_formal(job_id):
    database = os.environ.get("GOLDBACH_CI_DATABASE")
    desk_url = os.environ.get("GOLDBACH_DESK_URL")
    secret_file = os.environ.get("GOLDBACH_DESK_SECRET_FILE")
    if not all((database, desk_url, secret_file)):
        logging.error("Formal proof runner configuration is missing")
        return 3
    try:
        base = TRUSTED_BASE.resolve(strict=True)
        with closing(sqlite3.connect(database, timeout=15)) as db, tempfile.TemporaryDirectory(
                prefix="goldbach-formal-") as temporary:
            run = judge(
                db, PROOF_GITHUB, job_id, Path(temporary), base,
                ROOT / "toolchains/lean-4.36.0", ROOT / "controller/build-ownership.sh",
                desk_url=desk_url, secret=Path(secret_file).read_bytes().strip(),
            )
            row = db.execute("SELECT payload FROM desk_outbox WHERE run=? AND attempt=1", (run,)).fetchone()
            return {"ACCEPTED": 0, "REJECTED": 1}[json.loads(row[0])["verdict"]]
    except (ValueError, OSError, sqlite3.Error, subprocess.SubprocessError):
        logging.exception("Formal proof infrastructure error for job %s", job_id)
        return 3


def main():
    with RunnerServer(str(SOCKET), Handler) as server:
        os.chown(SOCKET, 0, 1000)
        SOCKET.chmod(0o660)
        server.serve_forever()


if __name__ == "__main__":
    main()
