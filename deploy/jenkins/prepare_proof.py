"""Prepare a one-file GitHub proof against an immutable, trusted task catalogue."""

import json
import os
import subprocess
from pathlib import Path

from github_revision import REPO, SHA, StaleDelivery, pull_request
from proof_blob import proof_blob


def grh_enabled():
    return os.environ.get("GOLDBACH_GRH_ENABLED") == "1"


def check_grh_imports(modules):
    if not grh_enabled() and any(
        module in {"PEqualNP.GRH", "PEqualNP.GRHSource"} or module.startswith("PEqualNP.GRHSource.")
        for module in modules
    ):
        raise ValueError("GRH imports are temporarily unavailable for proof submissions")


def prepare(app, number, expected_head, base, work):
    if not SHA.fullmatch(expected_head):
        raise ValueError("Expected a full PR head SHA")
    pr = pull_request(app, number)
    if pr["head"]["sha"] != expected_head or pr["state"] != "open":
        raise StaleDelivery("PR is no longer open at the queued revision")
    if pr["changed_files"] != 1:
        raise ValueError("Proof PR must change exactly one file")
    files = app.request("GET", f"{REPO}/pulls/{number}/files?per_page=2")
    commit = app.request("GET", f"{REPO}/git/commits/{expected_head}")
    tree_sha = commit["tree"]["sha"]
    if commit["sha"] != expected_head or not SHA.fullmatch(tree_sha):
        raise ValueError("GitHub returned a different proof commit")
    tree = app.request("GET", f"{REPO}/git/trees/{tree_sha}?recursive=1")
    current = pull_request(app, number)
    if (current["head"]["sha"] != expected_head or current["state"] != "open"
            or current["base"]["sha"] != pr["base"]["sha"]):
        raise StaleDelivery("PR changed during proof preparation")

    research = base / "research"
    gaps = json.loads((research / "gaps.json").read_text(encoding="utf-8"))["gaps"]
    for problem in json.loads((research / "problems.json").read_text(encoding="utf-8")).values():
        gaps.extend(problem["gaps"])
    for name, data in {"pr": pr, "files": files, "tree": tree, "gaps": {"gaps": gaps}}.items():
        (work / f"{name}.json").write_text(json.dumps(data), encoding="utf-8")

    def guard(*args):
        subprocess.run([
            "docker", "run", "--rm", "--pull", "never", "--runtime", "runsc",
            "--network", "none", "--read-only", "--cap-drop", "ALL",
            "--security-opt", "no-new-privileges", "--memory", "512m",
            "--mount", f"type=bind,source={base},target=/base,readonly",
            "--mount", f"type=bind,source={work},target=/input",
            "--entrypoint", "node", "goldbach-site-agent:site-check",
            "/base/.github/scripts/outside-guard.mjs", *args,
        ], check=True, timeout=30)

    os.chown(work, 1000, 1000)
    guard("pr", "/input/pr.json", "/input/files.json", "/input/tree.json",
          "CGandGameEngineLearner/goldbach-proofs", "main", "/input")
    file = (work / "pr.file").read_text().strip()
    blob = (work / "pr.blob").read_text().strip()
    size = int((work / "pr.size").read_text())
    guard("gap-of-file", "/input/gaps.json", file, "/input")
    (work / "proof.lean").write_bytes(proof_blob(app, blob, size))
    guard("imports", "/input/proof.lean", "/input/imports.json", "/input/build-imports.json")
    check_grh_imports(json.loads((work / "build-imports.json").read_text(encoding="utf-8")))
    guard("closure", "/base", "/input/build-imports.json", file, "/input")
    check_grh_imports((work / "base-imports.txt").read_text(encoding="utf-8").splitlines())
    return file
