"""Merge registered, independently accepted one-file Lean proofs and publish their sources."""

import argparse
import hashlib
import json
import logging
import os
import re
import sqlite3
import subprocess
import tempfile
import time
from contextlib import closing
from pathlib import Path
from urllib.error import HTTPError, URLError

from github_app import GitHubApp, INSTALLATION_ID, RateLimited
from github_revision import REPO, SHA, pull_request
from proof_blob import proof_blob
from verdict_manifest import MODULE, PROOF_MODULE, module_path

CONTENTS_WRITE = {"contents": "write", "pull_requests": "read"}
TRUST_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "CheckLemma.lean")
BATCH = 4


class SkipMerge(ValueError):
    """The registered revision is no longer eligible."""


def task(base, gap_id):
    research = base / "research"
    gaps = json.loads((research / "gaps.json").read_bytes())["gaps"]
    for problem in json.loads((research / "problems.json").read_bytes()).values():
        gaps.extend(problem["gaps"])
    matches = [gap for gap in gaps if gap["id"] == gap_id]
    if len(matches) != 1 or not PROOF_MODULE.fullmatch(matches[0]["module"]):
        raise SkipMerge("No current registered community proof file")
    return matches[0]


def metadata(app, path, revision):
    if not SHA.fullmatch(revision):
        raise ValueError("Expected a full GitHub revision")
    data = app.request("GET", f"{REPO}/contents/{path}?ref={revision}")
    if not isinstance(data, dict) or data.get("type") != "file" or data.get("path") != path:
        raise ValueError("Expected a plain GitHub file")
    return data


def git_blob(content):
    return hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()


def verify_dependency(app, base, revision, path, expected=None):
    content = (base / path).read_bytes()
    if expected is not None and hashlib.sha256(content).hexdigest() != expected:
        raise ValueError("A verified dependency changed in the Jenkins baseline")
    if metadata(app, path, revision)["sha"] != git_blob(content):
        raise ValueError("A verified dependency or pinned Lean input changed on main")


def manifest_hashes(record, target):
    manifest = record["manifest"]
    hashes = {}
    for item in manifest["rests_on"] + manifest["defs"]:
        module = item["module"]
        digest = item["sha256"]
        if (not MODULE.fullmatch(module) or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or hashes.setdefault(module, digest) != digest):
            raise ValueError("Invalid proof dependency manifest")
    if target not in hashes:
        raise ValueError("The verified manifest does not include the target theorem")
    return hashes


def current_head(pr, expected):
    return (pr["head"]["sha"] == expected
            and pr["base"]["ref"] == "main"
            and pr["base"]["repo"]["full_name"] == REPO.removeprefix("/repos/"))


def proven_content(app, path, revision, expected):
    entry = metadata(app, path, revision)
    content = proof_blob(app, entry["sha"], entry["size"])
    if hashlib.sha256(content).hexdigest() != expected:
        raise SkipMerge("The GitHub proof bytes differ from the official verdict")
    return content


def merge(app, number, head, record, base, *, dry_run=False):
    if record["verdict"] != "ACCEPTED" or record["head_sha"] != head:
        raise SkipMerge("No official ACCEPTED verdict for this revision")
    gap = task(base, record["lemma_id"])
    path = gap["file"]
    module = path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
    if gap["module"] != module or path != "lean/" + module_path(module):
        raise SkipMerge("The task does not map to its registered module")
    hashes = manifest_hashes(record, module)
    pr = pull_request(app, number)
    if not current_head(pr, head):
        raise SkipMerge("The pull request head or target has changed")

    if pr["merged"]:
        commit = pr["merge_commit_sha"]
        content = proven_content(app, path, commit, hashes[module])
        # A manually merged proof may have been reverted. Import only sources still on main.
        main = app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"]
        if metadata(app, path, main)["sha"] != git_blob(content):
            raise SkipMerge("The merged proof differs from main")
        return commit, path, content
    if pr["state"] != "open":
        raise SkipMerge("The pull request was closed")
    if pr["draft"] or pr["mergeable"] is False:
        raise ValueError("The pull request is draft or conflicted")

    files = app.request("GET", f"{REPO}/pulls/{number}/files?per_page=2")
    if (pr["changed_files"] != 1 or len(files) != 1 or files[0]["filename"] != path
            or files[0]["status"] != "added"):
        raise SkipMerge("The pull request must add only the registered Lean file")
    content = proven_content(app, path, head, hashes.pop(module))
    base_revision = pr["base"]["sha"]
    for name in TRUST_FILES:
        verify_dependency(app, base, base_revision, "lean/" + name)
    for name, digest in hashes.items():
        verify_dependency(app, base, base_revision, "lean/" + name.replace(".", "/") + ".lean", digest)
    if dry_run:
        return None, path, content

    latest = pull_request(app, number)
    if (not current_head(latest, head) or latest["state"] != "open" or latest["draft"]
            or latest["base"]["sha"] != base_revision):
        raise ValueError("The pull request changed before its merge")
    result = app.request("PUT", f"{REPO}/pulls/{number}/merge",
                         {"sha": head, "merge_method": "squash"})
    if not result.get("merged") or not SHA.fullmatch(result.get("sha", "")):
        raise ValueError("GitHub did not merge the exact verified revision")
    if metadata(app, path, result["sha"])["sha"] != git_blob(content):
        raise ValueError("GitHub merge did not preserve the verified source")
    return result["sha"], path, content


def publish_source(store, base, revision, path, content):
    previous = base / path
    if previous.is_file() and previous.read_bytes() == content:
        return
    if previous.exists():
        raise ValueError("Refusing to overwrite an existing trusted proof")
    with tempfile.TemporaryDirectory(prefix="stage-", dir=store) as folder:
        snapshot = Path(folder) / "base"
        subprocess.run(["cp", "-al", base, snapshot], check=True, timeout=90)
        (snapshot / path).parent.mkdir(parents=True, exist_ok=True)
        (snapshot / path).write_bytes(content)
        # The copied files are hard-linked. Replace any marker before writing.
        marker = snapshot / "PROOF_MERGE_REVISION"
        marker.unlink(missing_ok=True)
        marker.write_text(revision + "\n", encoding="ascii")
        target = store / f"{revision}-{Path(folder).name}"
        snapshot.rename(target)
        link = Path(folder) / "current"
        link.symlink_to(target)
        os.replace(link, store / "current")


def eligible(db, first_job_id):
    return db.execute("""SELECT j.id,j.pr,j.sha,o.payload,coalesce(m.attempts,0)
        FROM ci_jobs j JOIN desk_runs r ON r.job_id=j.id
        JOIN desk_outbox o ON o.run=r.run_id AND o.attempt=1
        JOIN jenkins_dispatches d ON d.job_id=j.id AND d.result='SUCCESS'
        LEFT JOIN proof_merges m ON m.job_id=j.id
        WHERE j.kind='authoritative' AND j.pr>0 AND j.id>=? AND o.delivered=1
          AND json_extract(o.payload,'$.verdict')='ACCEPTED'
          AND (m.job_id IS NULL OR (m.state='retry' AND m.retry_at<=?))
        ORDER BY j.id LIMIT ?""", (first_job_id, int(time.time()), BATCH)).fetchall()


def drain(db, app, store, first_job_id, *, dry_run=False):
    db.execute("""CREATE TABLE IF NOT EXISTS proof_merges (
        job_id INTEGER PRIMARY KEY, state TEXT NOT NULL, revision TEXT,
        attempts INTEGER NOT NULL, retry_at INTEGER NOT NULL)""")
    for job_id, pr, head, payload, attempts in eligible(db, first_job_id):
        revision, retry_at = None, 0
        try:
            base = (store / "current").resolve(strict=True)
            revision, path, content = merge(app, pr, head, json.loads(payload), base, dry_run=dry_run)
            if dry_run:
                print(f"PR {pr} verified for merge: {path}", flush=True)
                continue
            publish_source(store, base, revision, path, content)
            state = "merged"
            logging.info("PR %s proof source published from %s", pr, revision)
        except RateLimited:
            logging.info("GitHub requested a cooldown")
            break
        except SkipMerge as error:
            state = "skipped"
            logging.info("PR %s: %s", pr, error)
        except (HTTPError, URLError, TimeoutError, OSError, ValueError, subprocess.SubprocessError) as error:
            state = "retry"
            retry_at = int(time.time()) + min(3600, 60 * 2 ** min(6, attempts))
            reason = f"HTTP {error.code}" if isinstance(error, HTTPError) else str(error)
            logging.warning("PR %s: %s", pr, reason)
        if not dry_run:
            with db:
                db.execute("""INSERT OR REPLACE INTO proof_merges VALUES (?,?,?,?,?)""",
                           (job_id, state, revision, attempts + 1, retry_at))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=Path)
    parser.add_argument("--private-key", required=True)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--first-job-id", required=True, type=int)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    permissions = {"contents": "read", "pull_requests": "read"} if args.dry_run else CONTENTS_WRITE
    app = GitHubApp(args.private_key, permissions=permissions, request_interval=0.35)
    if not args.dry_run:
        installation = app.app_request("GET", f"/app/installations/{INSTALLATION_ID}")
        if installation["permissions"].get("contents") != "write":
            logging.info("Waiting for GitHub installation Contents write approval")
            return
    with closing(sqlite3.connect(args.database.resolve().as_uri() + "?mode=rw", uri=True, timeout=15)) as db:
        drain(db, app, args.store.resolve(strict=True), args.first_job_id, dry_run=args.dry_run)


if __name__ == "__main__":
    main()
