import datetime
import hashlib
import hmac
import json
import os
import re
import sqlite3
import time
from contextlib import closing
from pathlib import Path
import urllib.error
import urllib.parse
import urllib.request

from event_jobs import enqueue_delivery, initialize
from github_app import GitHubApp, RateLimited

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None

opener = urllib.request.build_opener(NoRedirect())

def fetch(url, body, headers, label, maximum=65536):
    request = urllib.request.Request(url, body, {
        "Content-Type": "application/json",
        **headers,
    })
    try:
        with opener.open(request, timeout=15) as response:
            data = response.read(maximum + 1)
            if len(data) > maximum:
                raise SystemExit(f"{label} response exceeds size limit")
            return data
    except urllib.error.HTTPError as error:
        if body is None and error.code in (404, 410):
            return b"null"
        raise SystemExit(f"{label} returned HTTP {error.code}") from None
    except urllib.error.URLError:
        raise SystemExit(f"{label} could not be reached") from None

env = os.environ
desk = urllib.parse.urlsplit(env["DESK_URL"])
secret = Path(env["GOLDBACH_DESK_SECRET_FILE"]).read_bytes().strip()
if (desk.scheme != "https" or not desk.hostname or desk.username is not None
        or desk.query or desk.fragment or not secret or not env["DEFAULT_BRANCH"]):
    raise SystemExit("HTTPS desk URL, signing secret and default branch required")
request_body = b"{}"
signature = hmac.new(secret, request_body, hashlib.sha256).hexdigest()
response = fetch(
    desk.geturl().rstrip("/") + "/pending",
    request_body,
    {"X-Goldbach-Signature": "sha256=" + signature, "Accept": "application/json"},
    "Desk queue",
)
rows = json.loads(response)["pending"]
if not isinstance(rows, list) or len(rows) > 16:
    raise SystemExit("Invalid desk batch")

pending = []
for row in rows:
    if not isinstance(row, dict):
        raise SystemExit("Invalid queued proof")
    pr, gap, head, handle = (row.get(field) for field in ("pr", "gap", "head", "handle"))
    if (type(pr) is not int or not 1 <= pr <= 9999999
            or not isinstance(gap, str) or not re.fullmatch(r"L-[a-z0-9]+(?:-[a-z0-9]+)*", gap)
            or len(gap) > 64 or not isinstance(head, str) or not re.fullmatch(r"[a-f0-9]{40}", head)
            or not isinstance(handle, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}", handle)):
        raise SystemExit("Invalid queued proof")
    pending.append((pr, gap, head, handle))

app = GitHubApp(env["GOLDBACH_APP_PRIVATE_KEY"])

def github(path):
    try:
        return app.request("GET", f"/repos/{env['REPO']}" + path)
    except RateLimited as error:
        with db:
            db.execute("""INSERT INTO github_dispatch_cooldown VALUES (1,?)
                          ON CONFLICT(id) DO UPDATE
                          SET retry_at=max(retry_at,excluded.retry_at)""", (error.retry_at,))
        raise SystemExit(0) from None
    except urllib.error.HTTPError as error:
        if error.code in (404, 410):
            return None
        raise

def matching_author_comment(pr, handle, gap):
    since = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=1)
    for page in range(1, 4):
        query = urllib.parse.urlencode({
            "per_page": 100, "page": page, "since": since.isoformat(timespec="seconds"),
        })
        comments = github(f"/issues/{pr}/comments?{query}")
        if not comments:
            return False
        for comment in comments:
            if ((comment.get("user") or {}).get("login", "").casefold() == handle.casefold()
                    and (comment.get("user") or {}).get("type") == "User"
                    and comment.get("body", "").strip() == f"/goldbach-check {gap}"):
                return comment["id"]
        if len(comments) < 100:
            return False
    return False

with closing(sqlite3.connect(env["GOLDBACH_CI_DATABASE"], timeout=15)) as db:
    initialize(db)
    db.execute("""CREATE TABLE IF NOT EXISTS github_dispatch_cooldown (
        id INTEGER PRIMARY KEY CHECK (id=1), retry_at INTEGER NOT NULL
    )""")
    cooldown = db.execute("SELECT retry_at FROM github_dispatch_cooldown WHERE id=1").fetchone()
    if cooldown and cooldown[0] > time.time():
        raise SystemExit(0)
    print(f"Task desk returned {len(pending)} pending requests")
    first_formal_job = int(env.get("GOLDBACH_CI_FIRST_FORMAL_JOB", "1"))
    dispatched = set()
    for pr, gap, head, handle in pending:
        if pr in dispatched:
            continue
        pull = github(f"/pulls/{pr}")
        if (not pull or pull["state"] != "open" or pull["changed_files"] != 1
                or pull["base"]["ref"] != env["DEFAULT_BRANCH"] or pull["head"]["sha"] != head
                or (pull.get("user") or {}).get("login", "").casefold() != handle.casefold()):
            continue
        comment = matching_author_comment(pr, handle, gap)
        if not comment:
            continue
        user = {"login": pull["user"]["login"], "type": "User"}
        event = {"action": "created", "issue": {"number": pr, "pull_request": True, "user": user},
                 "comment": {"id": comment, "user": user, "body": f"/goldbach-check {gap}"}}
        queued = enqueue_delivery(db, f"desk:{comment}:{head}", "issue_comment", event, (), comment_head=head)
        if not queued:
            # The desk has reconfirmed that this pre-cutover submission is still unclaimed.
            with db:
                queued = db.execute(
                    """UPDATE ci_jobs SET id=max(?, (SELECT coalesce(max(id),0)+1 FROM ci_jobs))
                       WHERE kind='authoritative' AND pr=? AND sha=? AND trigger=? AND id<?
                         AND NOT EXISTS (SELECT 1 FROM jenkins_dispatches WHERE job_id=ci_jobs.id)
                         AND NOT EXISTS (SELECT 1 FROM desk_runs WHERE job_id=ci_jobs.id)""",
                    (first_formal_job, pr, head, str(comment), first_formal_job),
                ).rowcount
        dispatched.add(pr)
        if queued:
            print(f"Queued PR {pr} for {gap}")
