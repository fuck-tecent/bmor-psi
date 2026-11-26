"""Translate completed advisory, website, catalogue, GRH and formal proof results into durable GitHub checks."""

import argparse
import sqlite3
from contextlib import closing
from pathlib import Path

from check_outbox import database, drain, enqueue
from github_app import GitHubApp

CONCLUSIONS = {
    "SUCCESS": "success", "FAILURE": "failure", "UNSTABLE": "failure",
    "ABORTED": "cancelled", "CANCELLED": "cancelled", "NOT_BUILT": "neutral",
}


def enqueue_build_checks(jobs, outbox, *, staging=False, first_job_id=1):
    rows = jobs.execute("""SELECT j.kind,j.sha,j.pr,d.jenkins_job,d.build_number,d.result
                          FROM ci_jobs j JOIN jenkins_dispatches d ON d.job_id=j.id
                          WHERE j.id>=? AND j.kind IN ('advisory','site','catalogue','grh')
                            AND d.result IS NOT NULL""", (first_job_id,))
    for kind, sha, pr, job, number, result in rows:
        if result not in CONCLUSIONS:
            continue
        if staging:
            if kind not in ("site", "advisory", "grh"):
                continue
            enqueue(outbox, kind + "-replay", sha, "neutral", f"Staging Jenkins {job} #{number}: {result}.", pr=pr)
        else:
            enqueue(outbox, kind + "-pr" if pr else kind, sha, CONCLUSIONS[result],
                    f"Jenkins {job} #{number}: {result}.", pr=pr)


def enqueue_formal_checks(jobs, outbox, *, first_job_id=1):
    rows = jobs.execute("""SELECT j.sha, j.pr, r.run_id,
                                  json_extract(CAST(o.payload AS TEXT), '$.lemma_id'),
                                  json_extract(CAST(o.payload AS TEXT), '$.verdict')
                           FROM ci_jobs j JOIN desk_runs r ON r.job_id=j.id
                           JOIN desk_outbox o ON o.run=r.run_id AND o.attempt=1
                           WHERE j.id>=? AND j.kind='authoritative' AND j.pr>0""", (first_job_id,))
    for sha, pr, run_id, gap, verdict in rows:
        conclusion = {"ACCEPTED": "success", "REJECTED": "failure"}[verdict]
        enqueue(outbox, "authoritative-pr", sha, conclusion,
                f"Lean verdict for {gap}: {verdict}. Task desk run {run_id}.", pr=pr, run_id=run_id)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs-db", required=True, type=Path)
    parser.add_argument("--outbox", required=True, type=Path)
    parser.add_argument("--private-key", required=True)
    parser.add_argument("--staging", action="store_true")
    parser.add_argument("--first-job-id", type=int, default=1)
    args = parser.parse_args()
    if args.first_job_id < 1:
        parser.error("--first-job-id must be positive")
    jobs_uri = args.jobs_db.resolve().as_uri() + "?mode=ro"
    with closing(sqlite3.connect(jobs_uri, uri=True, timeout=15)) as jobs, closing(database(args.outbox)) as outbox:
        enqueue_build_checks(jobs, outbox, staging=args.staging, first_job_id=args.first_job_id)
        if not args.staging:
            enqueue_formal_checks(jobs, outbox, first_job_id=args.first_job_id)
        drain(outbox, GitHubApp(args.private_key))


if __name__ == "__main__":
    main()
