"""Seed global import permissions from official desk records and an exact main Git tree."""

import argparse
import hashlib
import json
import sqlite3
from contextlib import closing
from pathlib import Path

from merge_proofs import git_blob, snapshot_for
from verdict_manifest import PROOF_MODULE, module_path


def export_records(directory):
    records = {}
    for path in directory.glob("*.sqlite3"):
        with closing(sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)) as db:
            if not db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='verdicts'").fetchone():
                continue
            for body, in db.execute("SELECT body FROM verdicts WHERE json_extract(body,'$.verdict')='ACCEPTED'"):
                record = json.loads(body)
                for item in (record.get("manifest") or {}).get("rests_on", []):
                    if PROOF_MODULE.fullmatch(item["module"]):
                        records.setdefault(record["lemma_id"], {}).setdefault(item["module"], set()).add(item["sha256"])
    return {gap: {m: sorted(values) for m, values in modules.items()} for gap, modules in records.items()}


def seed(store, evidence, tree, revision):
    store = store.resolve(strict=True)
    base = (store / "current").resolve(strict=True)
    tasks = json.loads((base / "research/gaps.json").read_bytes())["gaps"]
    for desk in json.loads((base / "research/problems.json").read_bytes()).values():
        tasks.extend(desk["gaps"])
    index = {}
    for task in tasks:
        module = task["module"]
        if not PROOF_MODULE.fullmatch(module) or task["file"] != "lean/" + module_path(module):
            continue
        path = base / task["file"]
        if path.is_symlink() or not path.is_file():
            continue
        source = path.read_bytes()
        digest = hashlib.sha256(source).hexdigest()
        if digest in evidence.get(task["id"], {}).get(module, []) and tree.get(task["file"]) == git_blob(source):
            index[module] = digest
    if not index:
        raise ValueError("No matching accepted and merged modules")
    with snapshot_for(store, base, revision) as stage:
        path = stage / "verified-imports.json"
        path.unlink(missing_ok=True)
        path.write_text(json.dumps(index, sort_keys=True, indent=2) + "\n", encoding="ascii")
    return len(index)


if __name__ == "__main__":
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("export").add_argument("desk_databases", type=Path)
    load = sub.add_parser("seed")
    for arg in ("store", "evidence", "tree"):
        load.add_argument(arg, type=Path)
    load.add_argument("revision")
    args = parser.parse_args()
    if args.action == "export":
        json.dump(export_records(args.desk_databases), sys.stdout)
    else:
        print(seed(args.store, json.loads(args.evidence.read_bytes()), json.loads(args.tree.read_bytes()), args.revision))
