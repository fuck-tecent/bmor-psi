"""Authorize a formal proof and durably record the kernel result."""

import json

from desk_outbox import enqueue, initialize
from desk_verdict import authorize
from event_jobs import desk_run_id
from github_revision import REPO, StaleDelivery, pull_request
from prepare_proof import prepare
from verify_proof import ProofRejected, verify


def judge(db, app, job_id, work, base, toolchain, ownership_check, *, desk_url, secret):
    row = db.execute(
        "SELECT sha,pr,trigger FROM ci_jobs WHERE id=? AND kind='authoritative'", (job_id,),
    ).fetchone()
    if row is None:
        raise ValueError("Expected a queued authoritative job")
    head, pr, trigger = row
    if not trigger.isascii() or not trigger.isdecimal() or int(trigger) < 1:
        raise ValueError("Expected a GitHub comment ID")

    run_id = desk_run_id(db, job_id)
    initialize(db)
    previous = db.execute(
        "SELECT delivered FROM desk_outbox WHERE run=? AND attempt=1", (run_id,),
    ).fetchone()
    if previous is not None:
        return run_id

    file = prepare(app, pr, head, base, work)
    gap = (work / "gap.id").read_text().strip()
    statement = (work / "statement.txt").read_bytes()
    prepared_base = json.loads((work / "pr.json").read_text(encoding="utf-8"))["base"]
    comment = app.request("GET", f"{REPO}/issues/comments/{trigger}")
    pull = pull_request(app, pr)
    current_base = pull["base"]
    if (pull["state"] != "open" or pull["head"]["sha"] != head
            or any(current_base[field] != prepared_base[field] for field in ("sha", "ref"))
            or current_base["repo"]["full_name"] != prepared_base["repo"]["full_name"]):
        raise StaleDelivery("The PR revision changed before desk authorization")
    handle = pull["user"]["login"]
    if (comment["issue_url"] != f"https://api.github.com{REPO}/issues/{pr}"
            or comment["user"]["type"] != "User"
            or comment["user"]["login"].casefold() != handle.casefold()
            or comment["body"].strip() != f"/goldbach-check {gap}"):
        raise StaleDelivery("The PR author did not authorize this proof and gap")
    authorize(desk_url, secret, pr=pr, head=head, handle=handle, gap=gap,
              run_id=run_id, statement=statement)
    try:
        manifest = verify(file, work, base / "lean", toolchain, ownership_check)
    except ProofRejected:
        verdict, manifest = "REJECTED", None
    else:
        verdict = "ACCEPTED"
    enqueue(db, {"lemma_id": gap, "head_sha": head, "verdict": verdict, "manifest": manifest,
                 "run_id": run_id, "run_attempt": 1})
    return run_id
