#!/usr/bin/env python3
"""Offline maintenance tool to sync the canonical model catalog and audit unrecognized models."""

import argparse
import gzip
import json
import sqlite3
import sys
import urllib.request
from contextlib import closing
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from deploy.desk import (  # noqa: E402
    AGENT_LABEL,
    Desk,
    MODEL_CATALOG,
    MODEL_NAME_ALIASES,
    MODEL_REGISTRY,
    model_provider,
    model_ranking_name,
    parse_model_id,
)

DESK_PATH = ROOT / "deploy" / "desk.py"
BEGIN_MARKER = "# BEGIN MODEL_CATALOG"
END_MARKER = "# END MODEL_CATALOG"
OPENROUTER_URL = "https://openrouter.ai/api/v1/models"
MODELS_DEV_URL = "https://models.dev/api.json"
DEFAULT_STATUS_URL = "https://www.movan.tech/goldbach/api/status"


def fetch_json(url):
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "Accept-Encoding": "gzip",
            "User-Agent": "goldbach-model-sync/1.0",
        },
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        raw = response.read()
        if response.headers.get("Content-Encoding", "").lower() == "gzip":
            raw = gzip.decompress(raw)
        return json.loads(raw)


def extract_upstream_models(payload):
    """Extract (canonical_id, provider) entries from OpenRouter or models.dev JSON payloads."""
    discovered = {}
    # OpenRouter format: {"data": [{"id": "anthropic/claude-sonnet-4.5", ...}, ...]}
    if isinstance(payload, dict) and isinstance(payload.get("data"), list):
        raw_ids = [item.get("id", "") for item in payload["data"] if isinstance(item, dict)]
    # models.dev format: {"provider_slug": {"models": {"model_id": {...}}}}
    elif isinstance(payload, dict):
        raw_ids = []
        for slug, block in payload.items():
            if not isinstance(block, dict):
                continue
            models = block.get("models")
            if isinstance(models, dict):
                for model_id in models:
                    raw_ids.append(f"{slug}/{model_id}" if "/" not in model_id else model_id)
    else:
        raise ValueError("Unsupported upstream catalog format")

    for raw in raw_ids:
        if not isinstance(raw, str):
            continue
        cleaned = " ".join(raw.strip().lower().split())
        if not cleaned or not AGENT_LABEL.fullmatch(cleaned):
            continue
        provider = model_provider(cleaned)
        if provider == "unknown":
            continue
        _, leaf, _ = parse_model_id(cleaned)
        leaf = model_ranking_name(leaf)
        if not leaf or " " in leaf or leaf in MODEL_NAME_ALIASES or not AGENT_LABEL.fullmatch(leaf):
            continue
        # Only store bare leaf ID when it does not conflict with another provider.
        leaf_provider = model_provider(leaf)
        if leaf_provider in ("unknown", provider):
            discovered.setdefault(leaf, provider)
        else:
            _, _, stripped = parse_model_id(cleaned)
            stripped = model_ranking_name(stripped)
            if stripped and " " not in stripped and stripped not in MODEL_NAME_ALIASES and AGENT_LABEL.fullmatch(stripped):
                discovered.setdefault(stripped, provider)
    return discovered


def render_catalog_block(catalog):
    provider_order = {name: index for index, name in enumerate(MODEL_REGISTRY)}
    ordered = sorted(
        catalog.items(),
        key=lambda item: (provider_order.get(item[1], len(provider_order)), item[1], item[0]),
    )
    lines = [BEGIN_MARKER, "MODEL_CATALOG = {"]
    for model_id, provider in ordered:
        lines.append(f"    {json.dumps(model_id)}: {json.dumps(provider)},")
    lines.append("}")
    lines.append(END_MARKER)
    return "\n".join(lines)


def update_desk_catalog(catalog, *, desk_path=DESK_PATH, write=False):
    source = desk_path.read_text(encoding="utf-8")
    start = source.index(BEGIN_MARKER)
    end = source.index(END_MARKER) + len(END_MARKER)
    replacement = render_catalog_block(catalog)
    updated = source[:start] + replacement + source[end:]
    if write:
        desk_path.write_text(updated, encoding="utf-8")
    return updated != source, replacement


def live_models(status_url):
    base = status_url.removesuffix("/api/status").rstrip("/")
    entries = []
    offset = 0
    while True:
        page = fetch_json(f"{base}/api/rankings?mode=models&offset={offset}&limit=50")
        entries.extend(page["items"])
        if not page["has_more"]:
            return entries
        offset += len(page["items"])
        if not page["items"]:
            raise ValueError("Model rankings returned an empty page with more results")


def audit_models(entries):
    """Return unrecognized model entries sorted by (-points, -accepted, name)."""
    unrecognized = []
    for entry in entries:
        raw_name = entry.get("name", "")
        ranked = model_ranking_name(raw_name)
        provider = model_provider(ranked)
        if provider == "unknown":
            unrecognized.append({
                "name": raw_name,
                "ranked_name": ranked,
                "accepted": entry.get("accepted", 0),
                "points": entry.get("points", 0),
            })
    unrecognized.sort(key=lambda row: (-row["points"], -row["accepted"], row["name"]))
    return unrecognized


def load_models_from_db(db_path):
    with closing(sqlite3.connect(db_path)) as conn:
        conn.row_factory = sqlite3.Row
        import time
        return Desk.agent_rankings(conn, int(time.time()))["models"]


def load_models_from_status(payload):
    desk = payload.get("desk", payload)
    agent_rankings = desk.get("agent_rankings", {})
    return agent_rankings.get("models", [])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sync_cmd = sub.add_parser("sync", help="sync MODEL_CATALOG in deploy/desk.py from an upstream source")
    sync_cmd.add_argument("--source", choices=("openrouter", "models.dev", "file"), default="openrouter")
    sync_cmd.add_argument("--file", type=Path, help="local JSON snapshot when --source=file")
    sync_cmd.add_argument("--replace", action="store_true", help="replace existing entries instead of merging")
    sync_cmd.add_argument("--write", action="store_true", help="write updates to deploy/desk.py (default is dry-run)")

    audit_cmd = sub.add_parser("audit", help="report unrecognized models from a desk DB or status payload")
    audit_cmd.add_argument("--db", type=Path, help="path to desk SQLite database")
    audit_cmd.add_argument("--status-file", type=Path, help="path to saved /api/status JSON")
    audit_cmd.add_argument("--status-url", default=DEFAULT_STATUS_URL, help="live desk URL (also accepts a legacy /api/status URL)")
    audit_cmd.add_argument("--all-desks", action="store_true", help="audit Goldbach main desk plus all problem desks")
    audit_cmd.add_argument("--json", action="store_true", help="output JSON")

    args = parser.parse_args()
    if args.command == "sync":
        if args.source == "file":
            if not args.file:
                parser.error("--file is required when --source=file")
            payload = json.loads(args.file.read_text(encoding="utf-8"))
        elif args.source == "openrouter":
            payload = fetch_json(OPENROUTER_URL)
        else:
            payload = fetch_json(MODELS_DEV_URL)
        discovered = extract_upstream_models(payload)
        merged = dict(discovered) if args.replace else {**discovered, **MODEL_CATALOG}
        added = sorted(set(merged) - set(MODEL_CATALOG))
        changed, _ = update_desk_catalog(merged, write=args.write)
        mode = "Updated" if args.write else "Dry-run"
        print(f"{mode}: {len(merged)} catalog models ({len(added)} new, changed={changed}).")
        if added:
            print("New entries sample:", ", ".join(added[:20]))
        return

    if args.all_desks:
        base = args.status_url.removesuffix("/api/status").rstrip("/")
        problems = json.loads((ROOT / "research" / "problems.json").read_text(encoding="utf-8"))
        desk_urls = [("goldbach", f"{base}/api/status")] + [
            (slug, f"{base}/problems/{slug}/api/status") for slug in problems
        ]
        unrecognized = []
        for slug, url in desk_urls:
            for row in audit_models(live_models(url)):
                unrecognized.append({"desk": slug, **row})
        unrecognized.sort(key=lambda row: (-row["points"], -row["accepted"], row["desk"], row["name"]))
    elif args.db:
        unrecognized = audit_models(load_models_from_db(args.db))
    elif args.status_file:
        unrecognized = audit_models(load_models_from_status(json.loads(args.status_file.read_text(encoding="utf-8"))))
    else:
        unrecognized = audit_models(live_models(args.status_url))
    if args.json:
        print(json.dumps(unrecognized, ensure_ascii=False, indent=2))
        return
    if not unrecognized:
        print("All observed models are recognized.")
        return
    print(f"Unrecognized models ({len(unrecognized)}):")
    for row in unrecognized:
        prefix = f"[{row['desk']}] " if "desk" in row else ""
        print(f"  {prefix}{row['name']:44s}  {row['points']:5d} pts  {row['accepted']:3d} accepted")


if __name__ == "__main__":
    main()
