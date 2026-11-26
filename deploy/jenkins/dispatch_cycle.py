"""Process a dispatch cycle against configured local Jenkins jobs."""

import argparse
import json
import sqlite3
import time
from contextlib import closing
from pathlib import Path

import jenkins_dispatch
from github_app import GitHubApp, RateLimited
from jenkins_client import Jenkins
from route_deliveries import process
from site_inputs import prepare_main_site


def cycle(db, github, jenkins, jobs, *, site_input_root=None, first_job_id=1,
          first_formal_job_id=1, formal_canary_pr=None):
    jenkins_dispatch.initialize(db)
    db.execute("""CREATE TABLE IF NOT EXISTS github_dispatch_cooldown (
        id INTEGER PRIMARY KEY CHECK (id=1), retry_at INTEGER NOT NULL
    )""")
    row = db.execute("SELECT retry_at FROM github_dispatch_cooldown WHERE id=1").fetchone()
    if row is None or row[0] <= time.time():
        try:
            process(db, github, grh_enabled="grh" in jobs or "grh-pr" in jobs)
        except RateLimited as error:
            with db:
                db.execute("""INSERT INTO github_dispatch_cooldown VALUES (1,?)
                              ON CONFLICT(id) DO UPDATE SET retry_at=max(retry_at,excluded.retry_at)""",
                           (error.retry_at,))
    jenkins_dispatch.reconcile(db, jenkins)

    def prepare(job_id, kind, sha, pr, name):
        if kind == "authoritative":
            if job_id < first_formal_job_id or (formal_canary_pr is not None and pr != formal_canary_pr):
                return False
        if name == "goldbach-site-revision":
            if site_input_root is None:
                raise ValueError("Site revision runner requires a prepared input root")
            if pr:
                return False
            prepare_main_site(github, job_id, sha, pr, site_input_root)
        return True

    jenkins_dispatch.dispatch(db, jenkins, jobs, prepare, first_job_id=first_job_id)
    jenkins_dispatch.collect(db, jenkins)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True)
    parser.add_argument("--github-key", required=True)
    parser.add_argument("--jenkins-url", required=True)
    parser.add_argument("--jenkins-user", required=True)
    parser.add_argument("--jenkins-credential", required=True, type=Path)
    parser.add_argument("--jobs", required=True, type=Path)
    parser.add_argument("--site-input-root", type=Path)
    parser.add_argument("--first-job-id", type=int, default=1)
    parser.add_argument("--first-formal-job-id", type=int, default=1)
    parser.add_argument("--formal-canary-pr", type=int)
    args = parser.parse_args()
    if min(args.first_job_id, args.first_formal_job_id) < 1:
        parser.error("Job cutoffs must be positive")
    if args.formal_canary_pr is not None and not 1 <= args.formal_canary_pr <= 9_999_999:
        parser.error("--formal-canary-pr must identify a pull request")

    jobs = json.loads(args.jobs.read_text())
    client = Jenkins(args.jenkins_url, args.jenkins_user, args.jenkins_credential.read_text().strip())
    with closing(sqlite3.connect(args.database, timeout=15)) as db:
        cycle(db, GitHubApp(args.github_key), client, jobs, site_input_root=args.site_input_root,
              first_job_id=args.first_job_id, first_formal_job_id=args.first_formal_job_id,
              formal_canary_pr=args.formal_canary_pr)


if __name__ == "__main__":
    main()
