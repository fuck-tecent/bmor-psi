"""Prepare a one-file GitHub proof against an immutable, trusted task catalogue."""

import json
import os
import hashlib
import re
import subprocess
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import build_opener

from desk_verdict import NoRedirect

from github_revision import REPO, SHA, StaleDelivery, pull_request
from proof_blob import proof_blob
from verdict_manifest import PROOF_MODULE, module_path


class ProofRefused(ValueError):
    """The proof guard rejected the input before Lean ran."""


def grh_enabled():
    return os.environ.get("GOLDBACH_GRH_ENABLED") == "1"


def check_grh_imports(modules):
    if not grh_enabled() and any(
        module in {"PEqualNP.GRH", "PEqualNP.GRHSource"} or module.startswith("PEqualNP.GRHSource.")
        for module in modules
    ):
        raise ValueError("GRH imports are temporarily unavailable for proof submissions")


def allow_verified_imports(base, work):
    index = base / "verified-imports.json"
    if not index.exists():
        return
    verified = json.loads(index.read_bytes())
    permissions = work / "imports.json"
    allowed = set(json.loads(permissions.read_bytes()))
    # Select only requested modules. The guard still parses and validates the full file.
    for match in re.finditer(rb"^import ([A-Za-z0-9_.]+)[ \t]*\r?$",
                             (work / "proof.lean").read_bytes(), re.MULTILINE):
        name = match[1].decode("ascii")
        if name in allowed or not PROOF_MODULE.fullmatch(name) or name not in verified:
            continue
        source = base / "lean" / module_path(name)
        if source.is_symlink() or hashlib.sha256(source.read_bytes()).hexdigest() != verified[name]:
            raise ValueError(f"Verified import source differs from the accepted proof: {name}")
        allowed.add(name)
    permissions.write_text(json.dumps(sorted(allowed)), encoding="utf-8")


def generated_task(module):
    match = re.fullmatch(r"Conjectures\.Cuts\.(Task|Cut|Refute)[0-9a-f]{24}", module)
    if not match:
        raise ValueError("Invalid generated module")
    desk = os.environ.get("GOLDBACH_DESK_URL", "https://www.movan.tech/goldbach/api/desk")
    url = desk.rstrip("/") + "/task?" + urlencode({"module": module})
    with build_opener(NoRedirect()).open(url, timeout=15) as response:
        data = response.read(262145)
    if len(data) > 262144:
        raise ValueError("Oversized Desk task descriptor")
    receipt = json.loads(data)
    kind = {"Task": "prove", "Cut": "cut", "Refute": "refute"}[match[1]]
    if receipt["gap"]["module"] != module or receipt["kind"] != kind:
        raise ValueError("Invalid Desk task descriptor")
    return receipt


def guard(base, work, *args):
    subprocess.run([
        "docker", "run", "--rm", "--pull", "never", "--runtime", "runsc",
        "--network", "none", "--read-only", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges", "--memory", "512m",
        "--mount", f"type=bind,source={base},target=/base,readonly",
        "--mount", f"type=bind,source={work},target=/input",
        "--entrypoint", "node", "goldbach-site-agent:site-check",
        "/base/.github/scripts/outside-guard.mjs", *args,
    ], check=True, timeout=30)


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

    os.chown(work, 1000, 1000)
    guard(base, work, "pr", "/input/pr.json", "/input/files.json", "/input/tree.json",
          "CGandGameEngineLearner/goldbach-proofs", "main", "/input")
    file = (work / "pr.file").read_text().strip()
    blob = (work / "pr.blob").read_text().strip()
    size = int((work / "pr.size").read_text())
    kind = "prove"
    module = (work / "pr.module").read_text().strip()
    if module.startswith("Conjectures.Cuts.") and not any(g["file"] == file for g in gaps):
        receipt = generated_task(module)
        kind = receipt["kind"]
        (work / "gaps.json").write_text(json.dumps({"gaps": [receipt["gap"]]}))
    guard(base, work, "gap-of-file", "/input/gaps.json", file, "/input")
    (work / "task.kind").write_text(kind)
    (work / "proof.lean").write_bytes(proof_blob(app, blob, size))
    allow_verified_imports(base, work)
    guard(base, work, "imports", "/input/proof.lean", "/input/imports.json", "/input/build-imports.json")
    check_grh_imports(json.loads((work / "build-imports.json").read_text(encoding="utf-8")))
    guard(base, work, "closure", "/base", "/input/build-imports.json", file, "/input")
    check_grh_imports((work / "base-imports.txt").read_text(encoding="utf-8").splitlines())
    return file


def report_guard_result(result):
    if result.returncode == 1:
        refusal = next((line for line in result.stdout.splitlines() if line.startswith("REFUSED: ")), "")
        if refusal:
            # Keep the proof guard's diagnostic out of subprocess tracebacks and Markdown.
            raise ProofRefused("".join(c if c.isprintable() else " " for c in refusal[9:])[:1000])
    if result.stdout:
        print(result.stdout, end="", flush=True)
    result.check_returncode()
