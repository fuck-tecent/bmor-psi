"""Read one desk's unsolved propositions and prepare a frozen reduction signature."""
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from graphlib import TopologicalSorter
from pathlib import Path
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[4]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def load_snapshot(problem, path):
    if path:
        data = path.read_bytes()
    else:
        prefix = "" if problem == "goldbach" else f"/problems/{problem}"
        with urlopen(f"https://www.goldbach.tech{prefix}/api/catalogue-status", timeout=30) as response:
            data = response.read()
    if data.startswith(b"\x1f\x8b"):
        data = gzip.decompress(data)
    return json.loads(data)


def prepare(gaps, snapshot, parent=None, inputs=()):
    catalogue = {g["id"]: g for g in gaps}
    static = [g for g in snapshot["gaps"] if not g.get("generated")]
    live = {g["id"]: g for g in static}
    if (len(live) != len(static) or set(catalogue) != set(live)
            or any(type(live[k]["proved"]) is not bool
                   or live[k].get("statement_sha256", hashlib.sha256(live[k].get("statement", "").encode()).hexdigest())
                      != hashlib.sha256(g["statement"].encode()).hexdigest() for k, g in catalogue.items())):
        raise ValueError("desk and Git catalogue differ or verdict data is incomplete; refresh both")
    assigned = snapshot["desk"]["assignments"]
    if not isinstance(assigned, dict):
        raise ValueError("missing assignment map")
    consumers = {k: [] for k in catalogue}
    for k, gap in catalogue.items():
        for dep in gap.get("depends_on", []):
            if not live[k]["proved"] and dep in consumers:
                consumers[dep].append(k)

    def describe(k):
        g = catalogue[k]
        return {"id": k, "title": g["plain_statement"]["zh"], "proved": live[k]["proved"],
                "assignment": assigned.get(k), "track": g.get("track"), "role": g.get("role"),
                "open_consumers": sorted(consumers[k])}

    if parent is None:
        if inputs:
            raise ValueError("--input requires --parent")
        candidates = [describe(k) for k in catalogue if not live[k]["proved"]]
        candidates.sort(key=lambda g: (g["assignment"] is not None, -len(g["open_consumers"]),
                                       g["role"] == "endpoint", g["id"]))
        return {"total": len(live), "open": len(candidates), "candidates": candidates}
    if parent not in live or live[parent]["proved"]:
        raise ValueError("parent must be an open proposition on this desk")
    if parent in inputs or len(set(inputs)) != len(inputs) or any(k not in live for k in inputs):
        raise ValueError("use distinct inputs from this desk and exclude the parent")

    def frozen(k):
        statement = catalogue[k]["statement"]
        return {**describe(k), "statement": statement,
                "statement_sha256": hashlib.sha256(statement.encode("utf-8")).hexdigest()}

    ancestors = set()
    stack = list(inputs)
    while stack:
        k = stack.pop()
        if k == parent:
            raise ValueError("an input depends on the proposed parent")
        if k not in ancestors:
            ancestors.add(k)
            stack.extend(catalogue[k].get("depends_on", []))
    result = {"parent": frozen(parent), "inputs": [frozen(k) for k in inputs]}
    if inputs:
        result["proposed_bridge_type"] = " → ".join(
            f"({catalogue[k]['statement']})" for k in [*inputs, parent])
    return result


def review_plan(plan, gaps, snapshot, problem, revision):
    """Check a v1 decomposition against this checkout and the desk snapshot."""
    if plan["version"] != 1 or (plan["problem"], plan["base_revision"]) != (problem, revision):
        raise ValueError("plan must target this desk and Git revision")
    parent = plan["parent"]["id"]
    evidence = prepare(gaps, snapshot, parent)
    if plan["parent"]["statement_sha256"] != evidence["parent"]["statement_sha256"]:
        raise ValueError("parent statement hash changed")

    statements = {g["id"]: g["statement"] for g in gaps}
    known_types = set(statements.values())
    dependencies = {g["id"]: set(g.get("depends_on", [])) for g in gaps}
    children = set()
    for task in plan["tasks"]:
        k = task["id"]
        if not k.startswith(f"L-{problem}-") or k in statements or task["statement"] in known_types:
            raise ValueError(f"wrong desk, duplicate ID or repeated statement: {k}")
        children.add(k)
        statements[k] = task["statement"]
        known_types.add(task["statement"])
        dependencies[k] = set(task["depends_on"])

    obligations = []
    for link in plan["links"]:
        output = link["output"]
        inputs = link["inputs"]
        if output not in statements or any(k not in statements for k in inputs):
            raise ValueError("link refers to an unknown proposition")
        dependencies[output].update(inputs)
        if link["kind"] == "sufficient_reduction":
            bridge = link["bridge"]
            if bridge not in statements or bridge in inputs:
                raise ValueError("reduction needs a separate, known bridge")
            dependencies[output].add(bridge)
            expected = " → ".join(f"({statements[k]})" for k in [*inputs, output])
            obligations.append({"bridge": bridge, "expected_type": expected,
                                "matches_literal_type": statements[bridge] == expected})

    for k, deps in dependencies.items():
        if not deps <= statements.keys():
            raise ValueError(f"unknown prerequisite of {k}")
    # A child that assumes its parent creates a cycle once the reduction link is included.
    list(TopologicalSorter(dependencies).static_order())
    reached = {parent}
    pending = [parent]
    while pending:
        upstream = dependencies[pending.pop()] - reached
        reached.update(upstream)
        pending.extend(upstream)
    if children - reached:
        raise ValueError(f"new tasks without a path to the parent: {sorted(children - reached)}")
    return {"parent": evidence["parent"], "new_tasks": len(children), "bridge_obligations": obligations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", default="goldbach")
    parser.add_argument("--snapshot", type=Path, help="saved API response (JSON or gzip)")
    parser.add_argument("--parent")
    parser.add_argument("--input", action="append", default=[])
    parser.add_argument("--check-plan", type=Path, help="check a v1 change set against the open parent")
    args = parser.parse_args()
    revision = git("rev-parse", "HEAD").decode().strip()
    if args.problem == "goldbach":
        desk = json.loads(git("show", f"{revision}:research/gaps.json"))
    else:
        desks = json.loads(git("show", f"{revision}:research/problems.json"))
        if args.problem not in desks:
            parser.error(f"unknown problem; choose goldbach or one of {', '.join(desks)}")
        desk = desks[args.problem]
    snapshot = load_snapshot(args.problem, args.snapshot)
    if args.check_plan:
        if args.input or args.parent:
            parser.error("--check-plan reads the parent and inputs from the plan")
        plan = json.loads(args.check_plan.read_bytes())
        result = review_plan(plan, desk["gaps"], snapshot, args.problem, revision)
    else:
        result = prepare(desk["gaps"], snapshot, args.parent, args.input)
    print(json.dumps({"problem": args.problem, "base_revision": revision,
                      "catalogue_revision": snapshot["catalogue_revision"],
                      "source": str(args.snapshot) if args.snapshot else "live",
                      "read_at_utc": datetime.now(timezone.utc).isoformat(),
                      **result}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"frontier: {error}")
