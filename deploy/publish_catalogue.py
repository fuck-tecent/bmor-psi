"""Publish catalogue PRs merged by authorized maintainers after exact-commit CI."""
import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen

REPO = "CGandGameEngineLearner/goldbach-proofs"
OWNER_ID = 103875245
STORE = Path("/opt/goldbach-catalogues")
APP = Path("/opt/goldbach-web")
CURRENT = STORE / "current"
FILES = ("gaps.json", "problems.json")
MISSING = object()


def git(*args):
    return subprocess.check_output(["git", "--git-dir", str(STORE / "git"), *args])


def api(path):
    request = Request("https://api.github.com/repos/" + REPO + path,
                      headers={"Accept": "application/vnd.github+json"})
    credentials = os.environ.get("CREDENTIALS_DIRECTORY")
    if credentials:
        token = Path(credentials) / "github-token"
        if token.is_file():
            request.add_unredirected_header("Authorization", f"Bearer {token.read_text().strip()}")
    with urlopen(request, timeout=15) as reply:
        return json.load(reply)


def select(directory):
    link = STORE / "next"
    link.unlink(missing_ok=True)
    link.symlink_to(directory)
    link.replace(CURRENT)


def finish(stage, sha):
    destination = STORE / sha
    (stage / "revision").write_text(sha)
    stage.chmod(0o755)
    if destination.exists():
        # A crash before activation can leave a fully prepared version.
        if any((stage / f).read_bytes() != (destination / f).read_bytes() for f in FILES):
            raise RuntimeError("Staged catalogue differs from prepared version")
    else:
        stage.rename(destination)
    return destination


def rendered(sha):
    try:
        with urlopen("https://www.goldbach.tech/health", timeout=6) as reply:
            return json.load(reply).get("catalogue_revision") == sha
    except (ValueError, OSError):
        return False


def reload_revision(sha):
    subprocess.run(["systemctl", "restart", "goldbach-web"], check=True)
    for _ in range(10):
        if rendered(sha):
            return
        time.sleep(1)
    raise RuntimeError("Production health did not confirm revision " + sha)


def circleci_api(path):
    request = Request("https://circleci.com/api/v2/" + path, headers={"Accept": "application/json"})
    with urlopen(request, timeout=15) as response:
        return json.load(response)


def circleci_release(sha):
    # A success on a contributor branch or a different revision cannot authorize publication.
    project = "gh/" + REPO
    source = "https://github.com/" + REPO
    pipelines = circleci_api(f"project/{project}/pipeline?branch=main")["items"]
    for pipeline in pipelines:
        vcs = pipeline.get("vcs", {})
        if (pipeline.get("project_slug") != project or vcs.get("branch") != "main"
                or vcs.get("revision") != sha or vcs.get("target_repository_url") != source):
            continue
        for workflow in circleci_api(f"pipeline/{pipeline['id']}/workflow")["items"]:
            if workflow["name"] != "catalogue-pilot" or workflow["status"] != "success":
                continue
            jobs = circleci_api(f"workflow/{workflow['id']}/job")["items"]
            if any(job["name"] == "lean-catalogue" and job["status"] == "success" for job in jobs):
                return {"id": int(pipeline["number"]), "provider": "circleci"}
    return None


def approved(sha):
    prs = api("/commits/" + sha + "/pulls")
    pr = next((p for p in prs if p["merge_commit_sha"] == sha and p["base"]["ref"] == "main"
               and p["base"]["repo"]["full_name"] == REPO and p.get("merged_at")), None)
    if not pr:
        raise RuntimeError("Expected a merged catalogue PR for " + sha)
    detail = api("/pulls/" + str(pr["number"]))
    allowed = {OWNER_ID, *(int(uid) for uid in os.environ.get("GOLDBACH_CATALOGUE_MERGER_IDS", "").split())}
    if (detail.get("merged_by") or {}).get("id") not in allowed:
        raise RuntimeError("Catalogue PR requires an authorized research task publisher")
    if os.environ.get("GOLDBACH_CATALOGUE_CI") == "circleci":
        run = circleci_release(sha)
        return (detail, run) if run else None
    if os.environ.get("GOLDBACH_CATALOGUE_CI") == "jenkins":
        run = jenkins_release(sha)
        return (detail, {"id": run["id"], "provider": "jenkins"}) if run else None
    runs = api("/actions/workflows/catalogue.yml/runs?event=push&branch=main&head_sha=" + sha)["workflow_runs"]
    return next(((detail, r) for r in runs if r["head_sha"] == sha and r["conclusion"] == "success"), None)


def jenkins_release(sha):
    name = "Goldbach CI / catalogue release"
    query = urlencode({"check_name": name, "app_id": 5932842, "per_page": 100})
    runs = api(f"/commits/{sha}/check-runs?{query}")["check_runs"]
    return next((run for run in runs
                 if run.get("head_sha") == sha
                 and run.get("name") == name
                 and (run.get("app") or {}).get("id") == 5932842
                 and run.get("external_id") == f"main:catalogue:{sha}"
                 and run.get("status") == "completed"
                 and run.get("conclusion") == "success"), None)


def merge_catalogue(base, live, candidate, path):
    if live == base or live == candidate:
        return candidate
    if candidate == base:
        return live
    values = (base, live, candidate)
    if all(isinstance(value, dict) for value in values):
        merged = {}
        for key in dict.fromkeys((*candidate, *live, *base)):
            value = merge_catalogue(base.get(key, MISSING), live.get(key, MISSING),
                                    candidate.get(key, MISSING), f"{path}.{key}")
            if value is not MISSING:
                merged[key] = value
        return merged
    if path.endswith((".gaps", ".tracks")) and all(isinstance(value, list) for value in values):
        indexed = []
        for records in values:
            by_id = {record["id"]: record for record in records}
            if len(by_id) != len(records):
                raise ValueError(f"Duplicate ID at {path}")
            indexed.append(by_id)
        return list(merge_catalogue(*indexed, path).values())
    raise ValueError(f"Conflicting catalogue changes at {path}")


def activate(sha, parent, pr, run):
    old = CURRENT.resolve(strict=True)
    with tempfile.TemporaryDirectory(dir=STORE) as tmp:
        stage = Path(tmp) / "release"
        stage.mkdir()
        for name in FILES:
            path = "research/" + name
            original, candidate = (git("show", rev + ":" + path) for rev in (parent, sha))
            live = (old / name).read_bytes()
            if candidate == original or candidate == live:
                result = live
            elif live == original:
                result = candidate
            else:
                merged = merge_catalogue(*(json.loads(data) for data in (original, live, candidate)), name)
                result = (json.dumps(merged, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
            json.loads(result)
            (stage / name).write_bytes(result)
        history = json.loads((old / "history.json").read_bytes())
        history.append(dict(sha=sha, pr=pr["number"], title=pr["title"], actor=pr["merged_by"]["login"],
                            run=run["id"], provider=run.get("provider", "github"), at=datetime.now(timezone.utc).isoformat(timespec="seconds")))
        (stage / "history.json").write_text(json.dumps(history, ensure_ascii=False), encoding="utf-8")
        prepared = finish(stage, sha)
        (STORE / "pending").write_text(sha)
        select(prepared)
    try:
        reload_revision(sha)
    except Exception:
        select(old)
        reload_revision(old.name)
        raise
    finally:
        (STORE / "pending").unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bootstrap", metavar="LIVE_BASE_SHA")
    args = parser.parse_args()
    STORE.mkdir(exist_ok=True)
    if not (STORE / "git").exists():
        subprocess.run(["git", "init", "--bare", STORE / "git"], check=True)
    git("-c", "http.version=HTTP/1.1", "-c", "protocol.version=0",
        "fetch", "--quiet", "https://github.com/" + REPO + ".git", "refs/heads/main")
    if args.bootstrap:
        sha = args.bootstrap
        if CURRENT.exists() or not re.fullmatch("[a-f0-9]{40}", sha):
            raise RuntimeError("Bootstrap requires a fresh store and a full baseline SHA")
        git("merge-base", "--is-ancestor", sha, "FETCH_HEAD")
        with tempfile.TemporaryDirectory(dir=STORE) as tmp:
            stage = Path(tmp) / "release"
            stage.mkdir()
            for name in FILES:
                shutil.copyfile(APP / name, stage / name)
            (stage / "history.json").write_text("[]")
            select(finish(stage, sha))
        reload_revision(sha)
        return
    base = CURRENT.resolve(strict=True).name
    git("merge-base", "--is-ancestor", base, "FETCH_HEAD")
    if (STORE / "pending").exists():
        if not rendered(base):
            reload_revision(base)
        (STORE / "pending").unlink()
    for sha in git("rev-list", "--first-parent", "--reverse", base+"..FETCH_HEAD").decode().splitlines():
        parent = sha+"^1"
        if not git("diff", "--name-only", parent, sha, "--", "research/ROADMAP.md", *["research/"+f for f in FILES]).strip():
            continue
        authorization = approved(sha)
        if authorization is None:
            return
        activate(sha, parent, *authorization)


if __name__ == "__main__":
    main()
