"""Translate validated GitHub deliveries to Jenkins job candidates."""

import re

CATALOGUE_PR = {
    "deploy/publish_catalogue.py", "deploy/test_publish_catalogue.py",
    "research/check-statement-scope.lean", "research/strong-goldbach.lean",
    "research/ROADMAP.md", "research/build_catalogue.py",
    "research/test_route_sources.py", "research/gaps.json",
    "research/problems.json", ".github/workflows/catalogue.yml",
}
GRH_PATHS = {
    "lean/PEqualNP/GRH.lean", "lean/CheckLemma.lean", "lean/lean-toolchain",
    "deploy/jenkins/check-grh.sh", ".github/workflows/grh.yml",
}


def route(event, body, paths=(), *, grh_enabled=True):
    """Route the exact revision. An unknown diff runs all applicable path checks."""
    if event == "issue_comment":
        issue = body["issue"]
        comment = body["comment"]
        if (body.get("action") == "created" and issue.get("pull_request")
                and comment["user"]["type"] == "User"
                and comment["user"]["login"] == issue["user"]["login"]
                and re.fullmatch(r"/goldbach-check L-[a-z0-9]+(?:-[a-z0-9]+)*", comment["body"].strip())):
            return ["authoritative"]
        return []

    if event == "pull_request":
        if body.get("action") not in ("opened", "synchronize", "reopened"):
            return []
        jobs = []
        if paths is None or any(
            path.startswith(("lean/PEqualNP/Outside/", "lean/Conjectures/"))
            and path.endswith(".lean") for path in paths
        ):
            jobs.append("advisory")
        if grh_enabled and (paths is None or any(path in GRH_PATHS or path.startswith((
            "lean/PEqualNP/GRHSource/", "lean/CheckerSuite/GRHConsumer", "lean/lake",
        )) for path in paths)):
            jobs.append("grh")
    elif event == "push":
        if body.get("deleted"):
            return []
        ref = body.get("ref")
        if ref == "refs/heads/ci/grh-compact":
            return ["grh"] if grh_enabled else []
        if ref != "refs/heads/main":
            return []
        # The former CircleCI job checked every main push with the same commands.
        jobs = ["catalogue"]
    else:
        return []

    if event == "pull_request" and (paths is None or any(
            path in CATALOGUE_PR or path.startswith("research/problems/") for path in paths)):
        jobs.append("catalogue")
    if paths is None or any(path.startswith("deploy/") or path == ".github/workflows/site-release.yml"
           for path in paths):
        jobs.append("site")
    return jobs
