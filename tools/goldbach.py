#!/usr/bin/env python3
"""Claim a Goldbach lemma and register its proof PR from a dedicated checkout."""

import argparse
import json
import os
import re
import secrets
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path

HARNESS_NAMES = (
    'codex',
    'claude-code',
    'cursor',
    'gemini-cli',
    'opencode',
    'kimi-code',
    'minimax-code',
    'zcode',
    'qwen-code',
    'qoder',
    'qoder-cn',
    'lingma',
    'trae',
    'codebuddy',
    'comate',
    'codegeex',
    'iflycode',
    'github-copilot',
    'github-copilot-cli',
    'windsurf',
    'cline',
    'roo-code',
    'kilo-code',
    'continue',
    'aider',
    'goose',
    'openhands',
    'kiro',
    'amazon-q',
    'augment-code',
    'auggie',
    'devin',
    'devin-desktop',
    'jetbrains-ai',
    'jetbrains-air',
    'junie',
    'zed',
    'warp',
    'tabnine',
    'replit-agent',
    'factory-droid',
    'mistral-vibe',
    'pi',
    'antigravity',
    'hermes-agent',
    'swe-agent',
    'mini-swe-agent',
    'open-interpreter',
    'other',
    'unknown',
)

REPO = "CGandGameEngineLearner/goldbach-proofs"
SITE = "https://www.movan.tech/goldbach"
GAP_ID = re.compile(r"L-[a-z0-9]+(?:-[a-z0-9]+)*")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class DeskRefusal(SystemExit):
    def __init__(self, action, status, reason):
        self.reason = reason
        super().__init__(f"Desk {action} failed ({status}): {reason}")


def command(*args):
    return subprocess.check_output(args, encoding="utf-8").strip()


def desk(action, data, token=None, *, problem="goldbach"):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    headers = {"Content-Type": "application/json", "Accept": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    if action == "claim" and os.environ.get("GOLDBACH_FLEET_FILE"):
        headers["X-Goldbach-Fleet"] = Path(os.environ["GOLDBACH_FLEET_FILE"]).read_text(encoding="ascii").strip()
    request = urllib.request.Request(
        f"{SITE}{prefix}/api/desk/{action}", data=json.dumps(data).encode(), headers=headers
    )
    try:
        with urllib.request.build_opener(NoRedirect()).open(request, timeout=20) as response:
            return json.loads(response.read())
    except urllib.error.HTTPError as error:
        try:
            message = json.loads(error.read(4096)).get("error", "request refused")
        except (ValueError, AttributeError):
            message = "request refused"
        if token:
            message = str(message).replace(token, "[hidden]")
        raise DeskRefusal(action, error.code, message) from None
    except urllib.error.URLError as error:
        raise SystemExit(f"Could not reach the Goldbach desk: {error.reason}") from None


def save(path, state):
    # A private tempfile and atomic replacement protect the lease across retries.
    fd, temporary = tempfile.mkstemp(dir=path.parent, prefix=".goldbach-lease-")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def current_branch():
    return command("git", "branch", "--show-current")


def authenticated_login():
    return command("gh", "api", "user", "--jq", ".login")


def claim(path, requested, problem):
    if path.exists():
        raise SystemExit("This checkout already has a task. Finish it or use a fresh checkout.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Use a clean, dedicated clone of the upstream Goldbach repository.")
    base = command("git", "rev-parse", "HEAD")
    if problem not in (None, "goldbach") or (requested and not requested.startswith("L-goldbach-")):
        problems = json.loads(command("git", "show", f"{base}:research/problems.json"))
        if problem is None:
            problem = next((slug for slug, config in problems.items()
                            if any(task["id"] == requested for task in config["gaps"])), "goldbach")
        if problem != "goldbach" and problem not in problems:
            raise SystemExit("Unknown research problem.")
    problem = problem or "goldbach"
    registry = (json.loads(command("git", "show", f"{base}:research/gaps.json"))
                if problem == "goldbach" else problems[problem])
    handle = authenticated_login()
    request = {"handle": handle}
    if requested:
        request["gap"] = requested
    response = desk("claim", request, problem=problem)
    gap = response["gap"]
    lease = response["lease"]
    expected = next((item for item in registry["gaps"] if item["id"] == gap["id"]), None)
    fields = ("id", "file", "module", "statement", "imports")
    if not expected or not GAP_ID.fullmatch(gap["id"]) or any(
        gap.get(field) != expected.get(field) for field in fields
    ):
        desk("release", {"reason": "superseded"}, lease["token"], problem=problem)
        raise SystemExit("The desk and this checkout disagree. Clone the current default branch and retry.")

    branch = f"goldbach/{gap['id']}/{secrets.token_hex(4)}"
    state = {
        "base": base, "branch": branch, "handle": handle, "gap": expected,
        "token": lease["token"], "problem": problem, "route_id": response.get("route_id"),
    }
    try:
        save(path, state)
        subprocess.run(["git", "switch", "-c", branch], check=True)
    except (OSError, subprocess.CalledProcessError):
        desk("release", {"reason": "other"}, lease["token"], problem=problem)
        path.unlink(missing_ok=True)
        raise
    print(json.dumps({
        "gap": expected, "route_id": state["route_id"], "branch": branch, "handle": handle, "expires_at": lease["expires_at"],
    }, ensure_ascii=False, indent=2))


def open_pr(state):
    problem, route, gap = state["problem"], state.get("route_id"), state["gap"]["id"]
    if not route or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", route):
        raise SystemExit("This lease predates route receipts. Open the PR manually and submit its number as usual.")
    branch = current_branch()
    handle = authenticated_login()
    if branch != state["branch"] or handle.casefold() != state["handle"].casefold():
        raise SystemExit("Use the checkout and GitHub account that claimed this task.")
    head = branch if handle.casefold() == REPO.split("/")[0].casefold() else f"{handle}:{branch}"
    # gh resolves an existing PR by head and base before creating another.
    matches = json.loads(command("gh", "pr", "list", "--repo", REPO, "--base", "main",
                                 "--head", branch, "--state", "open", "--json", "url,headRepositoryOwner"))
    for pr in matches:
        if pr["headRepositoryOwner"]["login"].casefold() == handle.casefold():
            print(pr["url"])
            return
    title = f"[{problem}/{route}] Prove {gap}"
    body = f"Problem: {problem}\nRoute: {route}\nLemma: {gap}\nFile: {state['gap']['file']}\n"
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "proof-pr.md"
        path.write_text(body, encoding="utf-8")
        subprocess.run(["gh", "pr", "create", "--repo", REPO, "--base", "main", "--head", head,
                        "--title", title, "--body-file", str(path)], check=True)


def submit(path, state, number, agent=None):
    problem = state.get("problem", "goldbach")
    if current_branch() != state["branch"]:
        raise SystemExit(f"Switch to the task branch {state['branch']} before submitting.")
    if authenticated_login().casefold() != state["handle"].casefold():
        raise SystemExit("Use the same GitHub account that claimed this assignment.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Commit the assigned proof file and leave the task checkout clean.")
    head = command("git", "rev-parse", "HEAD")
    expected_diff = "A\0" + state["gap"]["file"] + "\0"
    diff = subprocess.check_output(
        ["git", "diff", "--name-status", "-z", state["base"], head, "--"], encoding="utf-8"
    )
    if diff != expected_diff:
        raise SystemExit("The task branch must add exactly the assigned Lean file.")
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    base = pr["base"]
    if (
        pr["state"] != "open"
        or pr["user"]["login"].casefold() != state["handle"].casefold()
        or pr["head"]["sha"] != head
        or base["repo"]["full_name"].casefold() != REPO.casefold()
        or base["ref"] != base["repo"]["default_branch"]
        or pr["changed_files"] != 1
    ):
        raise SystemExit("The PR must be yours, open, based on the Goldbach default branch, and match this one-file checkout.")
    if state.get("submitted_head") == head and state.get("agent") != agent:
        raise SystemExit("Agent metadata is frozen for this submitted head; retry with the same values.")
    if state.get("requested") == {"pr": number, "head": head}:
        print(f"Verification already requested for PR {number} ({head[:12]}).")
        return
    submission = {"pr": number, "head": head}
    if agent is not None:
        submission["agent"] = agent
    try:
        desk("submit", submission, state["token"], problem=problem)
    except DeskRefusal as refusal:
        if refusal.reason != "lease_completed" or state.get("requested", {}).get("pr") != number:
            raise
        # A corrected proof uses a new lease for the same gap and a new head on the same PR.
        current = desk("claim", {"handle": state["handle"], "gap": state["gap"]["id"]}, problem=problem)
        token = current["lease"]["token"]
        if any(current["gap"].get(k) != state["gap"].get(k) for k in ("id", "module", "file", "statement", "imports")):
            desk("release", {"reason": "superseded"}, token, problem=problem)
            raise SystemExit("The published lemma changed. Start again from the current default branch.")
        state["token"] = token
        save(path, state)
        desk("submit", submission, token, problem=problem)
    # Persist before posting a comment so a network retry keeps the same attribution.
    state.update(submitted_head=head, agent=agent)
    save(path, state)
    instruction = f"/goldbach-check {state['gap']['id']}"
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", REPO, "--body", instruction],
        check=True,
    )
    state["requested"] = {"pr": number, "head": head}
    save(path, state)
    print(f"Requested authoritative verification for PR {number} ({head[:12]}).")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="action", required=True)
    request = modes.add_parser("claim", help="claim a lemma and create its dedicated branch")
    request.add_argument("gap", nargs="?")
    request.add_argument("--problem", help="problem slug, e.g. no-three-in-line")
    modes.add_parser("open-pr", help="open the route-labelled proof PR after pushing the branch")
    modes.add_parser("beat", help="renew the current lease")
    release = modes.add_parser("release", help="return an unfinished lemma")
    release.add_argument("reason", nargs="?", default="abandoned")
    submission = modes.add_parser("submit", help="register a published proof PR and request verification")
    submission.add_argument("pr", type=int)
    submission.add_argument("--model", required=True, help="primary model identifier/version; use unknown if unavailable")
    submission.add_argument("--harness", required=True,
                            choices=HARNESS_NAMES)
    submission.add_argument("--harness-version", default="unknown", help="tool version, when known")
    args = parser.parse_args()
    git_dir = Path(command("git", "rev-parse", "--absolute-git-dir"))
    path = git_dir / "goldbach-lease.json"
    if args.action == "claim":
        if args.gap and not GAP_ID.fullmatch(args.gap):
            parser.error("invalid Goldbach lemma ID")
        claim(path, args.gap, args.problem)
        return
    if not path.is_file():
        parser.error("no lease in this checkout; run claim first")
    state = json.loads(path.read_text(encoding="utf-8"))
    if args.action == "open-pr":
        open_pr(state)
    elif args.action == "beat":
        response = desk("beat", {}, state["token"], problem=state.get("problem", "goldbach"))
        lease = response.get("lease", response)
        print("Lease renewed.", lease.get("expires_at", ""))
    elif args.action == "release":
        desk("release", {"reason": args.reason}, state["token"], problem=state.get("problem", "goldbach"))
        path.unlink()
        print("Unfinished assignment returned to the desk.")
    else:
        if args.pr < 1:
            parser.error("PR number must be positive")
        agent = {"model": args.model, "harness": args.harness, "harness_version": args.harness_version}
        for key, value in agent.items():
            if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", value):
                parser.error(f"{key} must be a 1–96 character ASCII identifier; use unknown if unavailable")
            agent[key] = " ".join(value.lower().split())
        submit(path, state, args.pr, agent)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(f"{error.cmd[0]} failed with exit status {error.returncode}.") from None

