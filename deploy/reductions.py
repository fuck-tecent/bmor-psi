"""Persist checked reductions and their premises alongside a desk's lease ledger."""
import hashlib
import json
import re
import time

MAX_DEPTH = 2
MAX_LIVE = 3
CREDIT_POINTS = 1
KINDS = ("prove", "cut", "refute")
GENERATED_ID = re.compile(r"L-([a-z]+(?:-[a-z]+)*)-cut-([0-9a-f]{24})")
SCHEMA = """
CREATE TABLE IF NOT EXISTS cut_tasks (
    id TEXT PRIMARY KEY, descriptor TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS reductions (
    run INTEGER PRIMARY KEY, parent TEXT NOT NULL, module TEXT NOT NULL,
    state TEXT NOT NULL, reason TEXT
);
CREATE INDEX IF NOT EXISTS reductions_by_parent ON reductions(parent, state);
CREATE TABLE IF NOT EXISTS cut_premises (
    run INTEGER NOT NULL, position INTEGER NOT NULL, child TEXT NOT NULL,
    PRIMARY KEY(run, position), UNIQUE(run, child)
);
CREATE INDEX IF NOT EXISTS cuts_using_child ON cut_premises(child);
CREATE TABLE IF NOT EXISTS assembled_proofs (
    gap TEXT PRIMARY KEY, run INTEGER NOT NULL, certificate TEXT NOT NULL
);
"""


def digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def target(gap, module):
    return {**gap, "module": module, "file": "lean/" + module.replace(".", "/") + ".lean"}


def cut_reason(gap, live):
    if gap.get("reductions") is not True:
        return "cuts_disabled"
    if gap.get("depth", 0) >= MAX_DEPTH:
        return "cut_depth_limit"
    if live >= MAX_LIVE:
        return "cut_limit"
    return None


def inactive_tasks(conn):
    """Dynamic tasks stay active while reachable through any live cut."""
    return {key for key, in conn.execute("""
        WITH RECURSIVE reachable(gap) AS (
            SELECT DISTINCT parent FROM reductions
            WHERE state='live' AND parent NOT IN (SELECT id FROM cut_tasks)
            UNION
            SELECT p.child FROM reachable a
            JOIN reductions r ON r.parent=a.gap AND r.state='live'
            JOIN cut_premises p ON p.run=r.run
        )
        SELECT id FROM cut_tasks WHERE id NOT IN (SELECT gap FROM reachable)
    """)}


def catalogue(conn, static):
    return {**static, **{key: {**json.loads(data), "parallel": True} for key, data in conn.execute(
        "SELECT id,descriptor FROM cut_tasks")}}


def validate_children(children):
    if (not isinstance(children, list) or not 2 <= len(children) <= 4
            or any(not isinstance(s, str) or not s.strip() or len(s) > 2000 for s in children)
            or len(set(children)) != len(children)):
        raise ValueError("Invalid kernel reduction premises")


def register(conn, parent, lease, children, gaps, slug, refuted, proved, descriptions=None):
    validate_children(children)
    run = lease["run_id"]
    if conn.execute("SELECT 1 FROM reductions WHERE run=?", (run,)).fetchone():
        return
    live = conn.execute("SELECT count(*) FROM reductions WHERE parent=? AND state='live'",
                        (parent["id"],)).fetchone()[0]
    reason = ("settled" if parent["id"] in proved or parent["id"] in refuted or parent.get("refutation")
              else cut_reason(parent, live))
    if parent["id"] in inactive_tasks(conn):
        reason = "cut_inactive"
    by_statement = {g["statement"]: g for g in gaps.values()}
    forbidden = {key for key, in conn.execute("""
        WITH RECURSIVE ancestors(gap) AS (
          SELECT ? UNION SELECT r.parent FROM ancestors a
          JOIN cut_premises p ON p.child=a.gap JOIN reductions r ON r.run=p.run
        ) SELECT gap FROM ancestors""", (parent["id"],))}
    tasks = []
    for pos, statement in enumerate(children, 1):
        key = digest(slug + "\n" + statement)[:24]
        child = by_statement.get(statement)
        if child is None:
            child_id = f"L-{slug}-cut-{key}"
            if child_id in gaps:
                raise ValueError("Frozen child ID collides with an existing task")
            wording = descriptions[pos - 1] if descriptions else None
            child = target({
                "id": child_id, "statement": statement, "imports": parent.get("imports", []),
                "plain_statement": wording or {
                    "zh": f"{parent['id']} 的拆题前提 {pos}/{len(children)}",
                    "en": f"Premise {pos}/{len(children)} of a cut of {parent['id']}",
                },
                "program": parent.get("program", "foundation"), "track": parent.get("track"),
                "route_parent": parent.get("route_parent", parent["id"]),
                "cut_origin": {"run": run, "pr": lease["pr"], "head": lease["head"],
                               "position": pos, "contributor_wording": bool(wording)},
                "reductions": True, "depth": parent.get("depth", 0) + 1,
            }, "Conjectures.Cuts.Task" + key)
        if child["id"] in forbidden:
            reason = "cyclic_cut"
        tasks.append(child)
    existing = conn.execute(
        "SELECT run FROM reductions WHERE parent=? AND state='live'", (parent["id"],))
    ids = sorted(task["id"] for task in tasks)
    for old_run, in existing:
        if ids == sorted(row[0] for row in conn.execute("SELECT child FROM cut_premises WHERE run=?", (old_run,))):
            reason = "duplicate_cut"
            break
    state = "surplus" if reason else "live"
    if not reason and any(t["id"] in refuted or t.get("refutation", {}).get("status") == "verified" for t in tasks):
        state = "refuted"
        reason = "premise_refuted"
    conn.execute("INSERT INTO reductions VALUES (?,?,?,?,?)",
                 (run, parent["id"], lease["target_module"], state, reason))
    if reason:
        return
    for pos, task in enumerate(tasks):
        if task["id"] not in gaps:
            conn.execute("INSERT INTO goldbach_task_openings VALUES (?,?)", (task["id"], lease["finished_at"]))
            conn.execute("INSERT INTO cut_tasks VALUES (?,?)",
                         (task["id"], json.dumps(task, ensure_ascii=False)))
        conn.execute("INSERT INTO cut_premises VALUES (?,?,?)", (run, pos, task["id"]))


def refutations(conn):
    return {gap: {"status": "verified", "pr": pr, "head": head, "run_id": run, "handle": handle, "module": module}
            for gap, pr, head, run, handle, module in conn.execute("""
                SELECT gap, pr, head, run_id, handle, target_module FROM goldbach_leases
                WHERE kind='refute' AND verdict='ACCEPTED' ORDER BY run_id DESC""")}


# The initial adoption is durable even if a later refutation closes the cut.
# Unadopted attempts never have published premises.
AWARDED_CUTS = """
    FROM reductions AS r
    JOIN goldbach_leases AS l ON l.run_id = r.run
    WHERE l.kind = 'cut' AND l.verdict = 'ACCEPTED' AND r.reason IS NULL
      AND EXISTS (SELECT 1 FROM cut_premises AS p WHERE p.run = r.run)
"""


def public_records(conn, parent_id=None):
    records = {}
    where = "WHERE r.parent=?" if parent_id is not None else ""
    params = (parent_id,) if parent_id is not None else ()
    for run, parent, state, reason, handle, pr, head, child in conn.execute(f"""
        SELECT r.run,r.parent,r.state,r.reason,l.handle,l.pr,l.head,p.child
        FROM reductions r JOIN goldbach_leases l ON l.run_id=r.run
        LEFT JOIN cut_premises p ON p.run=r.run
        {where} ORDER BY r.run,p.position""", params):
        cut = records.setdefault(parent, {}).setdefault(run, {
            "run_id": run, "status": state, "reason": reason, "handle": handle,
            "pr": pr, "head": head, "children": [],
        })
        if child is not None:
            cut["children"].append(child)
            if reason is None:
                cut["points"] = CREDIT_POINTS
    return {gap: list(cuts.values()) for gap, cuts in records.items()}


def assembly_plans(conn, gaps, after=0):
    """Freeze the exact accepted modules for each complete alternative, in binder order."""
    live = conn.execute("SELECT run,parent FROM reductions WHERE state='live' AND run>? ORDER BY run",
                        (after,)).fetchall()
    if not live:
        return
    gaps = catalogue(conn, gaps)

    def evidence(record_row, gap):
        if record_row is None:
            return None
        body, handle, pr, head = record_row
        record = json.loads(body)
        module = record.get("module") or gaps[gap].get("module")
        sha = next((item["sha256"] for item in record["manifest"]["rests_on"] if item["module"] == module), None)
        if sha:
            return dict(gap=gap, run=record["run_id"], module=module, sha256=sha,
                        handle=handle, pr=pr, head=head or record.get("head_sha"))

    records = """SELECT v.body,l.handle,l.pr,l.head FROM verdicts v
                 LEFT JOIN goldbach_leases l ON l.run_id=v.run_id WHERE
                 json_extract(CAST(v.body AS TEXT),'$.verdict')='ACCEPTED' """
    ordinary = records + """AND json_extract(CAST(v.body AS TEXT),'$.lemma_id')=?
                            AND coalesce(json_extract(CAST(v.body AS TEXT),'$.kind'),'prove')='prove'
                            ORDER BY v.run_id, v.attempt LIMIT 1"""
    resolved = {}

    def child_proof(gap):
        if gap not in resolved:
            cert = conn.execute("SELECT certificate FROM assembled_proofs WHERE gap=?", (gap,)).fetchone()
            resolved[gap] = (json.loads(cert[0])["proof"] if cert else
                             evidence(conn.execute(ordinary, (gap,)).fetchone(), gap))
        return resolved[gap]

    inactive = inactive_tasks(conn)
    for run, parent in live:
        if parent in inactive or parent not in gaps or gaps[parent].get("refutation") or child_proof(parent):
            continue
        children = [key for key, in conn.execute(
            "SELECT child FROM cut_premises WHERE run=? ORDER BY position", (run,))]
        if not children or any(child not in gaps or gaps[child].get("refutation") for child in children):
            continue
        premises = [child_proof(child) for child in children]
        if all(premises):
            row = conn.execute(records + "AND v.run_id=? ORDER BY v.attempt LIMIT 1", (run,)).fetchone()
            cut = evidence(row, parent)
            if cut:
                yield {"parent": parent, "run": run, "statement": gaps[parent]["statement"],
                       "proof": {**cut, "premises": premises}}


def plan_hash(plan):
    return digest(json.dumps(plan, sort_keys=True, separators=(",", ":")))


def complete(conn, desk, result):
    """Compare the worker's pinned plan again inside the transaction recording completion."""
    run, parent = result["run"], result["parent"]
    if type(run) is not int or run <= 0 or not isinstance(result["plan_hash"], str):
        raise ValueError("Invalid assembly receipt")
    existing = conn.execute("SELECT certificate FROM assembled_proofs WHERE gap=?", (parent,)).fetchone()
    if existing:
        return json.loads(existing[0])["plan_hash"] == result["plan_hash"]
    plan = next((p for p in assembly_plans(conn, desk.gaps, run - 1) if p["run"] == run), None)
    if not plan or plan_hash(plan) != result["plan_hash"]:
        return False
    module = "Conjectures.Cuts.Assembly" + result["plan_hash"][:24]
    source, manifest = result["source"], result["manifest"]
    if not isinstance(source, str) or not isinstance(manifest, dict):
        raise ValueError("Missing assembly source or manifest")
    if not any(m["module"] == module and m["sha256"] == digest(source) for m in manifest["rests_on"]):
        raise ValueError("Missing checked assembly source")
    cert = {**result, "proof": plan["proof"], "module": module, "statement_sha256": digest(plan["statement"])}
    conn.execute("INSERT INTO assembled_proofs VALUES (?,?,?)", (parent, run, json.dumps(cert)))
    conn.execute("UPDATE reductions SET state='completed' WHERE run=?", (run,))
    desk.settle(conn, parent, "prove", int(time.time()))
    return True
