"""Persist Jenkins dispatches and collect results for queued CI tasks."""

import logging
from urllib.error import HTTPError, URLError


def initialize(db):
    db.execute("""CREATE TABLE IF NOT EXISTS jenkins_dispatches (
        job_id INTEGER PRIMARY KEY, jenkins_job TEXT NOT NULL,
        queue_id INTEGER, build_number INTEGER, result TEXT
    )""")


def dispatch(db, client, job_names, prepare=None, *, first_job_id=1):
    """Dispatch configured jobs. An ambiguous enqueue requires reconciliation."""
    rows = db.execute("""SELECT id,kind,sha,pr,trigger FROM ci_jobs j
                         WHERE j.id>=? AND NOT EXISTS (
                             SELECT 1 FROM jenkins_dispatches d WHERE d.job_id=j.id)
                         ORDER BY id""", (first_job_id,)).fetchall()
    for job_id, kind, sha, pr, trigger in rows:
        name = job_names.get(kind + '-pr', job_names.get(kind)) if pr else job_names.get(kind)
        if name is None:
            continue
        if prepare is not None and prepare(job_id, kind, sha, pr, name) is False:
            continue
        with db:
            claimed = db.execute(
                "INSERT OR IGNORE INTO jenkins_dispatches (job_id,jenkins_job) VALUES (?,?)",
                (job_id, name),
            ).rowcount
        if not claimed:
            continue
        try:
            queue = client.enqueue(name, {"CI_JOB_ID": job_id, "CI_HEAD": sha,
                                          "CI_PR": pr, "CI_TRIGGER": trigger})
        except HTTPError as error:
            if error.code in (400, 401, 403, 404, 405):
                # Jenkins explicitly refused the request. Retry after the job or access is fixed.
                with db:
                    db.execute("DELETE FROM jenkins_dispatches WHERE job_id=? AND queue_id IS NULL",
                               (job_id,))
            logging.warning("Jenkins enqueue for job %s returned HTTP %s", job_id, error.code)
            continue
        except (URLError, TimeoutError, RuntimeError) as error:
            # Jenkins may have received the request. Reconcile instead of submitting again.
            logging.warning("Jenkins enqueue for job %s is unconfirmed (%s)", job_id, type(error).__name__)
            continue
        with db:
            db.execute("UPDATE jenkins_dispatches SET queue_id=? WHERE job_id=?", (queue, job_id))


def collect(db, client):
    rows = db.execute("""SELECT job_id,jenkins_job,queue_id,build_number FROM jenkins_dispatches
                         WHERE queue_id IS NOT NULL AND result IS NULL ORDER BY job_id""").fetchall()
    for job_id, name, queue, build in rows:
        if build is None:
            try:
                item = client.queued(queue)
            except HTTPError as error:
                if error.code != 404:
                    raise
                # Jenkins expires queue items. Recover using the job's recorded queue ID.
                builds = client.get(f"{client.job_path(name)}/api/json?tree=builds[number,queueId]")["builds"]
                build = next((entry["number"] for entry in builds if entry["queueId"] == queue), None)
                if build is None:
                    continue
            else:
                if item.get("cancelled"):
                    with db:
                        db.execute("UPDATE jenkins_dispatches SET result='CANCELLED' WHERE job_id=?",
                                   (job_id,))
                    continue
                if not item.get("executable"):
                    continue
                build = item["executable"]["number"]
            with db:
                db.execute("UPDATE jenkins_dispatches SET build_number=? WHERE job_id=?", (build, job_id))
        result = client.result(name, build)
        if result["queueId"] != queue:
            raise ValueError("Jenkins build does not match the recorded queue item")
        if result.get("result"):
            with db:
                db.execute("UPDATE jenkins_dispatches SET result=? WHERE job_id=?",
                           (result["result"], job_id))


def reconcile(db, client):
    rows = db.execute("""SELECT d.job_id,d.jenkins_job,j.sha,j.pr,j.trigger
                         FROM jenkins_dispatches d JOIN ci_jobs j ON j.id=d.job_id
                         WHERE d.queue_id IS NULL ORDER BY d.job_id""").fetchall()
    if not rows:
        return
    queued = client.get("/queue/api/json?tree=items[id,task[name],actions[parameters[name,value]]]")["items"]

    def matches(item, expected):
        params = {param["name"]: str(param["value"])
                  for action in item.get("actions", ()) if action
                  for param in action.get("parameters", ())}
        return all(params.get(key) == value for key, value in expected.items())

    for job_id, name, sha, pr, trigger in rows:
        expected = {"CI_JOB_ID": str(job_id), "CI_HEAD": sha, "CI_PR": str(pr), "CI_TRIGGER": trigger}
        queues = {item["id"] for item in queued
                  if item.get("task", {}).get("name") == name and matches(item, expected)}
        builds = client.get(f"{client.job_path(name)}/api/json?tree=builds[number,queueId,actions[parameters[name,value]]]")["builds"]
        queues.update(item["queueId"] for item in builds if matches(item, expected))
        if len(queues) > 1:
            raise ValueError("Multiple Jenkins queue items match a single CI task")
        if queues:
            with db:
                db.execute("UPDATE jenkins_dispatches SET queue_id=? WHERE job_id=? AND queue_id IS NULL",
                           (queues.pop(), job_id))
