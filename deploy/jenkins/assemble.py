"""Replay one complete cut against an immutable snapshot of merged, accepted proofs."""
import hashlib
import json
import logging
import os
import subprocess
import tempfile
import time
from pathlib import Path

from desk_verdict import signed_post, signed_request
from prepare_proof import guard
from verdict_manifest import PROOF_MODULE, module_path
from verify_proof import verify


def prepare_assembly(plan, base, work):
    key = hashlib.sha256(json.dumps(plan, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    module = "Conjectures.Cuts.Assembly" + key[:24]
    imports = {}

    def application(node):
        name = node["module"]
        if not PROOF_MODULE.fullmatch(name):
            raise ValueError("Invalid certified proof module")
        if imports.setdefault(name, node["sha256"]) != node["sha256"]:
            raise ValueError("Conflicting certificates for one module")
        terms = [name, *(application(child) for child in node.get("premises", []))]
        return "(" + " ".join(terms) + ")" if len(terms) > 1 else name

    term = application(plan["proof"])
    for name, digest in imports.items():
        source = base / "lean" / module_path(name)
        if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Trusted snapshot differs from accepted {name}")
    source = ("import Mathlib\n" + "".join(f"import {name}\n" for name in imports)
              + f"\ntheorem {module} : ({plan['statement']}) :=\n  {term}\n")
    (work / "pr.module").write_text(module)
    (work / "statement.txt").write_text(plan["statement"])
    (work / "proof.lean").write_text(source)
    (work / "imports.json").write_text(json.dumps(list(imports)))
    file = "lean/" + module_path(module)
    return key, file, source


def assemble(plan, base, work, toolchain, ownership_check):
    key, file, source = prepare_assembly(plan, base, work)
    os.chown(work, 1000, 1000)
    guard(base, work, "assembly-closure", "/base", "/input/imports.json", file, "/input")
    manifest = verify(file, work, base / "lean", toolchain, ownership_check)
    return {"parent": plan["parent"], "run": plan["run"], "plan_hash": key,
            "source": source, "manifest": manifest}


def poll(slots, base, root, url, secret_file):
    cursor = ["", 0]
    while True:
        delay = 30
        try:
            secret = Path(secret_file).read_bytes().strip()
            reply = signed_request(url + "/assembly-next", secret, json.dumps({"after": cursor}).encode())
            plan, cursor = reply["plan"], reply["cursor"]
            if plan:
                delay = 1
                with slots, tempfile.TemporaryDirectory(prefix="goldbach-assembly-") as temporary:
                    result = assemble(plan, base.resolve(strict=True), Path(temporary),
                                      root / "toolchains/lean-4.36.0", root / "controller/build-ownership.sh")
                signed_post(url + "/assembly-complete", secret, json.dumps(result).encode(), {"status": "stored"})
        except (KeyError, TypeError, ValueError, OSError, RuntimeError, subprocess.SubprocessError):
            logging.exception("Deferred cut assembly at %s", cursor)
        time.sleep(delay)
