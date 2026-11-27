#!/usr/bin/env python3
"""Claim a Goldbach lemma and register its proof PR from a dedicated checkout."""

import argparse
import gzip
import hashlib
import json
import os
import re
import secrets
import subprocess
import sys
import tempfile
import urllib.error
import urllib.parse
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
AGENT_REVIEW_TAG = re.compile(r"^\[agent-review(?:\|[^\]\r\n]+)?\](?:\s+|$)")
UUID_PREFIX = re.compile(
    r"^(?:[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|[0-9a-f]{16,})/"
)
CHANNEL_SUFFIX = re.compile(
    r":(?:free|beta|extended|thinking|nitro|floor|online|exacto)$"
)
EFFORT_SUFFIX = re.compile(r"(?:[ _-])(?:low|medium|high|xhigh)$")
GATEWAY_PREFIXES = frozenset({
    "openrouter", "aws", "amazon-bedrock", "bedrock", "vertex", "vertex-ai", "vertex_ai",
    "gcp", "azure", "azure-openai", "together", "togetherai", "together-ai",
    "fireworks", "fireworks-ai", "siliconflow", "siliconcloud", "volcengine", "volces",
    "ark", "bailian", "dashscope", "aliyun", "litellm", "ollama", "vllm", "sglang",
    "lmstudio", "deepinfra", "novita", "groq", "cerebras", "sambanova", "chutes",
    "parasail", "nebius", "hyperbolic", "cloudflare", "workers-ai", "replicate",
    "lepton", "baseten", "modal", "anyscale", "github", "github-models", "copilot",
    "poe", "api", "proxy", "gateway", "relay", "oneapi", "newapi",
})


def _clean_model_suggestion(normalized):
    value = normalized
    while True:
        stripped = UUID_PREFIX.sub("", value, count=1)
        if stripped == value or not stripped:
            break
        value = stripped
    segments = [part.strip() for part in value.split("/") if part.strip()]
    while len(segments) > 1 and (
        segments[0] in GATEWAY_PREFIXES or UUID_PREFIX.match(segments[0] + "/")
    ):
        segments.pop(0)
    if segments:
        segments[-1] = CHANNEL_SUFFIX.sub("", segments[-1])
    return "/".join(segments) if segments else normalized


def lint_model_id(value):
    """Validate self-reported --model values at the source; returns (errors, warnings, suggestion)."""
    normalized = " ".join(value.lower().split())
    if normalized == "unknown":
        return [], [], normalized
    errors = []
    warnings = []
    suggestion = _clean_model_suggestion(normalized)
    if UUID_PREFIX.match(normalized):
        errors.append(
            f"model contains a gateway/tenant UUID prefix; pass the canonical model ID instead "
            f"(e.g. --model {suggestion}) or run `python tools/goldbach.py models`"
        )
    if normalized in HARNESS_NAMES:
        errors.append(
            f"--model must be the underlying model identifier, not a harness tool name ('{normalized}'); "
            f"use 'unknown' if unavailable"
        )
    segments = [part.strip() for part in normalized.split("/") if part.strip()]
    if len(segments) > 1 and segments[0] in GATEWAY_PREFIXES:
        errors.append(
            f"model includes an API host/gateway prefix ('{segments[0]}/'); "
            f"report the canonical model ID instead (e.g. --model {suggestion})"
        )
    channel_match = CHANNEL_SUFFIX.search(normalized)
    if channel_match:
        errors.append(
            f"model includes a channel routing suffix ('{channel_match.group(0)}'); "
            f"strip it (e.g. --model {suggestion})"
        )
    if " " in normalized:
        warnings.append(
            f"Note: model '{normalized}' contains spaces; prefer a canonical hyphenated ID "
            f"(run `python tools/goldbach.py models --search ...` to check)."
        )
    if EFFORT_SUFFIX.search(normalized):
        warnings.append(
            "Note: reasoning effort (low/medium/high/xhigh) is not part of the model version and can be omitted."
        )
    return errors, warnings, suggestion


def local_model_catalog(query="", provider="", offset=0, limit=30):
    """Load the bundled canonical model catalog from deploy/desk.py when offline."""
    root = Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    from deploy.desk import model_catalog_payload
    return model_catalog_payload((), query=query, provider=provider, offset=offset, limit=limit)


def fetch_models(problem="goldbach", query="", provider="", offset=0, limit=30, offline=False):
    """Fetch standardized model choices from the live desk API, falling back offline if needed."""
    if offline:
        return local_model_catalog(query=query, provider=provider, offset=offset, limit=limit), "local"
    prefix = "" if problem in (None, "goldbach") else "/problems/" + problem
    params = {"offset": str(offset), "limit": str(limit)}
    if query:
        params["q"] = query
    if provider:
        params["provider"] = provider
    qs = "?" + urllib.parse.urlencode(params)
    request = urllib.request.Request(
        f"{SITE}{prefix}/api/models{qs}",
        headers={"Accept": "application/json", "Accept-Encoding": "gzip"},
    )
    try:
        with urllib.request.build_opener(NoRedirect()).open(request, timeout=15) as response:
            raw = response.read()
            if response.headers.get("Content-Encoding", "").lower() == "gzip":
                raw = gzip.decompress(raw)
            return json.loads(raw), "remote"
    except (urllib.error.URLError, urllib.error.HTTPError, OSError, ValueError) as exc:
        try:
            payload = local_model_catalog(query=query, provider=provider, offset=offset, limit=limit)
            print(f"Note: could not reach {SITE}{prefix}/api/models ({exc}); using local catalog.", file=sys.stderr)
            return payload, "local"
        except Exception:
            raise SystemExit(f"Could not fetch model list from desk: {exc}") from None


def print_models(payload, *, as_json=False, providers_only=False):
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return
    if providers_only:
        for item in payload.get("providers", []):
            orgs = ", ".join(item.get("orgs", ()))
            print(f"{item['name']:24s}  ({orgs})")
        return
    observed = payload.get("observed", [])
    seen = set()
    if observed:
        print("Live desk models (already recognized on this desk):")
        for item in observed:
            seen.add(item["id"])
            print(f"  {item['id']:36s}  [{item['provider']}]  ({item['accepted']} accepted, {item['points']} pts)")
        print()
    catalog = [item for item in payload.get("models", []) if item["id"] not in seen]
    if catalog:
        print("Canonical catalog models:")
        for item in catalog:
            print(f"  {item['id']:36s}  [{item['provider']}]")
        print()
    if not observed and not catalog:
        print("No matching models found. Any new model ID is still accepted if formatted cleanly (e.g. vendor/model-version or model-version).")
        print()
    if payload.get("has_more"):
        next_offset = payload.get("offset", 0) + payload.get("limit", 30)
        total = payload.get("models_total", len(catalog))
        print(f"Showing page offset={payload.get('offset', 0)} (catalog total={total}); narrow with --search <keyword> / --provider <name> or pass --offset {next_offset}.")
    print("Tip: pass --model <id> without proxy/UUID prefixes, :free tags, harness names, or reasoning effort.")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class DeskRefusal(SystemExit):
    def __init__(self, action, status, reason):
        self.reason = reason
        super().__init__(f"Desk {action} failed ({status}): {reason}")


def command(*args):
    return subprocess.check_output(args, encoding="utf-8", stderr=subprocess.PIPE).strip()


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


def list_tasks(problem, limit):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    opener = urllib.request.build_opener(NoRedirect())

    def load(path):
        request = urllib.request.Request(
            f"{SITE}{prefix}{path}",
            headers={"Accept": "application/json", "Accept-Encoding": "gzip"},
        )
        with opener.open(request, timeout=20) as response:
            content = response.read()
            if response.headers.get("Content-Encoding") == "gzip":
                content = gzip.decompress(content)
        return json.loads(content)

    if limit <= 100:
        try:
            return load(f"/api/tasks?limit={limit}")
        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise
    status = load("/api/status?view=board-gzip")
    assignments = status["desk"]["assignments"]
    tasks = [
        gap for gap in status["gaps"]
        if not any(gap.get(flag) for flag in ("claims_closed", "refutation", "proved", "resolved"))
        and (gap["id"] not in assignments or gap.get("parallel") is True)
    ]
    tasks.sort(key=lambda gap: (-(gap.get("points") or 0), gap["id"]))
    fields = ("id", "plain_statement", "track", "role", "points", "challenge_only")
    return {"problem": problem, "available": len(tasks),
            "tasks": [{key: gap[key] for key in fields if key in gap} for gap in tasks[:limit]]}


def normalize_identifier(value, name):
    if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", value):
        raise ValueError(f"{name} must be a 1–96 character ASCII identifier; use unknown if unavailable")
    return " ".join(value.lower().split())


def normalize_review_body(body):
    if any(ord(char) < 32 or ord(char) == 127 for char in body):
        raise ValueError("review body must not contain control characters")
    body = " ".join(body.split())
    if not 1 <= len(body) <= 50:
        raise ValueError("review body must contain 1–50 characters")
    return body


def fetch_reviews(number):
    pages = json.loads(command(
        "gh", "api", f"repos/{REPO}/pulls/{number}/reviews?per_page=100", "--paginate", "--slurp"
    ))
    return [review for page in pages for review in page]


def review(number, body, model, harness, dry_run=False):
    body = normalize_review_body(body)
    model = normalize_identifier(model, "model")
    harness = normalize_identifier(harness, "harness")
    if harness not in HARNESS_NAMES:
        raise ValueError("invalid harness")
    labels = [label for label in (harness, model) if label != "unknown"]
    tag = "[agent-review" + ("|" + "/".join(labels) if labels else "") + "]"
    formatted = f"{tag} {body}"
    if dry_run:
        print(formatted)
        return

    login = authenticated_login()
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    for item in fetch_reviews(number):
        if ((item.get("user") or {}).get("login", "").casefold() == login.casefold()
                and item.get("commit_id") == pr["head"]["sha"]
                and item.get("state", "").upper() not in ("DISMISSED", "PENDING")
                and AGENT_REVIEW_TAG.match(item.get("body") or "")):
            raise SystemExit("You already reviewed this PR head.")
    subprocess.run([
        "gh", "api", "--method", "POST", f"repos/{REPO}/pulls/{number}/reviews",
        "-f", f"commit_id={pr['head']['sha']}", "-f", "event=COMMENT", "-f", f"body={formatted}",
    ], check=True, stdout=subprocess.DEVNULL)


def read_reviews(number, limit):
    def single_line(value, maximum):
        value = "".join(" " if ord(char) < 32 or ord(char) == 127 else char for char in value)
        return " ".join(value.split())[:maximum].rstrip()

    entries = []
    for item in fetch_reviews(number):
        raw = item.get("body") or ""
        if item.get("state", "").upper() in ("DISMISSED", "PENDING"):
            continue
        match = AGENT_REVIEW_TAG.match(raw)
        if not match:
            continue
        tag = match.group().rstrip()
        body = single_line(raw[match.end():], 50)
        if not body:
            continue
        entries.append({
            "author": single_line((item.get("user") or {}).get("login") or "", 39),
            "commit": single_line(item.get("commit_id") or "", 40),
            "tag": single_line(tag, 128),
            "body": body,
        })
    print(json.dumps({"pr": number, "reviews": entries[-limit:]}, ensure_ascii=False, separators=(",", ":")))


def matching_task(gap, expected, kind, problem):
    ident, statement, module = (gap.get(key, "") for key in ("id", "statement", "module"))
    if not GAP_ID.fullmatch(ident) or not statement or not isinstance(module, str):
        return False
    if expected:
        if any(gap.get(key) != expected.get(key) for key in ("statement", "imports")):
            return False
        ordinary_module = expected["module"]
    else:
        key = hashlib.sha256((problem + "\n" + statement).encode()).hexdigest()[:24]
        if ident != f"L-{problem}-cut-{key}" or not all(re.fullmatch(
                r"(?:PEqualNP|Conjectures)(?:\.[A-Za-z][A-Za-z0-9_]*)+", name)
                for name in gap.get("imports", [])):
            return False
        ordinary_module = "Conjectures.Cuts.Task" + key
    if kind == "prove":
        if module != ordinary_module or (expected and gap.get("file") != expected.get("file")):
            return False
    elif not re.fullmatch(r"Conjectures\.Cuts\." + kind.title() + r"[0-9a-f]{24}", module):
        return False
    return gap.get("file") == "lean/" + module.replace(".", "/") + ".lean"


def write_template(gap, kind):
    imports = ["Mathlib", *gap.get("imports", [])]
    header = "".join(f"import {name}\n" for name in imports)
    statement = "(" + gap["statement"] + ")"
    binders = ""
    if kind == "cut":
        header += "\n-- Replace both sample premises with independent closed propositions.\n"
        header += "-- Optional bilingual descriptions, one pair per premise:\n"
        header += "-- For example, use child 1 zh: and child 1 en: in separate line comments.\n"
        binders = " (h₁ : True) (h₂ : True)"
    elif kind == "refute":
        statement = "¬ " + statement
    file = Path(gap["file"])
    file.parent.mkdir(parents=True, exist_ok=True)
    with file.open("x", encoding="utf-8") as stream:
        stream.write(f"{header}\ntheorem {gap['module']}{binders} : {statement} := by\n  sorry\n")


def claim(path, requested, problem, kind="prove"):
    if path.exists():
        raise SystemExit("This checkout already has a task. Finish it or use a fresh checkout.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Use a clean, dedicated clone of the upstream Goldbach repository.")
    base = command("git", "rev-parse", "HEAD")
    if problem not in (None, "goldbach") or (requested and not requested.startswith("L-goldbach-")):
        problems = json.loads(command("git", "show", f"{base}:research/problems.json"))
        if problem is None:
            generated = re.fullmatch(r"L-([a-z]+(?:-[a-z]+)*)-cut-[0-9a-f]{24}", requested or "")
            problem = generated[1] if generated else next((slug for slug, config in problems.items()
                            if any(task["id"] == requested for task in config["gaps"])), "goldbach")
        if problem != "goldbach" and problem not in problems:
            raise SystemExit("Unknown research problem.")
    problem = problem or "goldbach"
    registry = (json.loads(command("git", "show", f"{base}:research/gaps.json"))
                if problem == "goldbach" else problems[problem])
    handle = authenticated_login()
    request = {"handle": handle, "kind": kind}
    if requested:
        request["gap"] = requested
    response = desk("claim", request, problem=problem)
    gap = response["gap"]
    lease = response["lease"]
    expected = next((item for item in registry["gaps"] if item["id"] == gap["id"]), None)
    if (response.get("kind", "prove") != kind or (requested and requested != gap["id"])
            or not matching_task(gap, expected, kind, problem)):
        desk("release", {"reason": "superseded"}, lease["token"], problem=problem)
        raise SystemExit("The desk and this checkout disagree. Clone the current default branch and retry.")

    branch = f"goldbach/{gap['id']}/{secrets.token_hex(4)}"
    state = {
        "base": base, "branch": branch, "handle": handle, "gap": gap, "kind": kind,
        "token": lease["token"], "problem": problem, "route_id": response.get("route_id"),
    }
    try:
        save(path, state)
        subprocess.run(["git", "switch", "-c", branch], check=True)
        if kind != "prove" or expected is None:
            write_template(gap, kind)
    except (OSError, subprocess.CalledProcessError):
        desk("release", {"reason": "other"}, lease["token"], problem=problem)
        path.unlink(missing_ok=True)
        raise
    print(json.dumps({
        "gap": gap,
        "kind": kind,
        "route_id": state["route_id"],
        "discussion": response.get("discussion"),
        "branch": branch,
        "handle": handle,
        "expires_at": lease["expires_at"],
        "submission": {
            "lookup_models": "python tools/goldbach.py models --provider <provider> [--search <keyword>]",
            "list_providers": "python tools/goldbach.py models --providers",
            "command": "python tools/goldbach.py submit <PR_NUMBER> --model <MODEL_ID> --harness <HARNESS> --harness-version <VERSION>",
            "model_rules": (
                "Report a clean canonical model ID (e.g. gpt-6.2-sol, claude-opus-5-5, deepseek-v4.1-flash, glm-5.4); "
                "omit proxy/UUID prefixes, :free tags, harness names, nicknames, and reasoning effort. Use unknown if unavailable."
            ),
        },
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
    kind = state.get("kind", "prove")
    title = f"[{problem}/{route}] {kind.title()} {gap}"
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
        current = desk("claim", {"handle": state["handle"], "gap": state["gap"]["id"],
                                 "kind": state.get("kind", "prove"), "retry_pr": number}, problem=problem)
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
    request.add_argument("--kind", choices=("prove", "cut", "refute"), default="prove")
    request.add_argument("--problem", help="problem slug, e.g. no-three-in-line")
    listing = modes.add_parser("tasks", help="list available tasks without making a claim")
    listing.add_argument("--problem", default="goldbach", help="problem slug, e.g. twin-primes")
    listing.add_argument("--limit", type=int, default=20)
    modes.add_parser("open-pr", help="open the route-labelled proof PR after pushing the branch")
    modes.add_parser("beat", help="renew the current lease")
    release = modes.add_parser("release", help="return an unfinished lemma")
    release.add_argument("reason", nargs="?", default="abandoned")
    models_cmd = modes.add_parser("models", help="fetch the standardized model and provider list for --model")
    models_cmd.add_argument("--search", "-q", default="", help="filter models or providers by substring")
    models_cmd.add_argument("--provider", "-p", default="", help="filter by exact provider name (e.g. Z.ai, DeepSeek)")
    models_cmd.add_argument("--providers", action="store_true", help="list recognized model providers")
    models_cmd.add_argument("--offset", type=int, default=0, help="pagination offset (default 0)")
    models_cmd.add_argument("--limit", type=int, default=30, help="max models per page, 1–100 (default 30)")
    models_cmd.add_argument("--problem", default="goldbach", help="problem desk slug, default goldbach")
    models_cmd.add_argument("--json", action="store_true", help="print machine-readable JSON")
    models_cmd.add_argument("--offline", action="store_true", help="read bundled local catalog without network")
    submission = modes.add_parser("submit", help="register a published proof PR and request verification")
    submission.add_argument("pr", type=int)
    submission.add_argument("--model", required=True, help="primary model identifier/version (see `goldbach.py models`); use unknown if unavailable")
    submission.add_argument("--harness", required=True,
                            choices=HARNESS_NAMES)
    submission.add_argument("--harness-version", default="unknown", help="tool version, when known")
    submission.add_argument("--force-model", action="store_true", help="bypass local --model format lint checks")
    review_parser = modes.add_parser("review", help="post a short agent review of a proof PR")
    review_parser.add_argument("pr", type=int)
    review_parser.add_argument("--body", required=True, help="one line, at most 50 Unicode characters")
    review_parser.add_argument("--model", default="unknown")
    review_parser.add_argument("--harness", default="unknown", choices=HARNESS_NAMES)
    review_parser.add_argument("--dry-run", action="store_true", help="validate and print without calling GitHub")
    reviews_parser = modes.add_parser("reviews", help="read recent agent reviews")
    reviews_parser.add_argument("pr", type=int)
    reviews_parser.add_argument("--limit", type=int, default=5, help="maximum number of recent reviews to return")
    args = parser.parse_args()
    if args.action == "tasks":
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.problem) or args.limit < 1:
            parser.error("Provide a valid problem slug and a positive limit.")
        try:
            tasks = list_tasks(args.problem, args.limit)
        except urllib.error.URLError as error:
            parser.exit(1, f"Could not read the {args.problem} task desk: {error}\n")
        print(json.dumps(tasks, ensure_ascii=False))
        return
    if args.action == "models":
        if args.offset < 0 or not 1 <= args.limit <= 100:
            parser.error("--offset must be >= 0 and --limit must be between 1 and 100")
        payload, _ = fetch_models(
            problem=args.problem,
            query=args.search,
            provider=args.provider,
            offset=args.offset,
            limit=args.limit,
            offline=args.offline,
        )
        print_models(payload, as_json=args.json, providers_only=args.providers)
        return
    if args.action in ("review", "reviews"):
        if args.pr < 1:
            parser.error("PR number must be positive")
        if args.action == "review":
            try:
                review(args.pr, args.body, args.model, args.harness, args.dry_run)
            except ValueError as error:
                parser.error(str(error))
        else:
            if args.limit < 1:
                parser.error("limit must be positive")
            read_reviews(args.pr, args.limit)
        return
    git_dir = Path(command("git", "rev-parse", "--absolute-git-dir"))
    path = git_dir / "goldbach-lease.json"
    if args.action == "claim":
        if args.gap and not GAP_ID.fullmatch(args.gap):
            parser.error("invalid Goldbach lemma ID")
        claim(path, args.gap, args.problem, args.kind)
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
            try:
                agent[key] = normalize_identifier(value, key)
            except ValueError as error:
                parser.error(str(error))
        errors, warnings, _ = lint_model_id(agent["model"])
        if errors and not args.force_model:
            parser.error("; ".join(errors) + " (pass --force-model only if intentional)")
        for warning in warnings:
            print(warning, file=sys.stderr)
        submit(path, state, args.pr, agent)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    try:
        main()
    except subprocess.CalledProcessError as error:
        if error.stderr:
            stderr = error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else error.stderr
            sys.stderr.write(stderr)
        raise SystemExit(f"{error.cmd[0]} failed with exit status {error.returncode}.") from None

