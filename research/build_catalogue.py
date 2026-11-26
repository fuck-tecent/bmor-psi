"""Build the compatibility catalogues from legacy entries and per-route sources."""
import argparse
import json
import re
from graphlib import TopologicalSorter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SLUG = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
MARK = "route_source"


def proof_location(slug, ident):
    prefix = f"L-{slug}-"
    suffix = ident.removeprefix(prefix)
    if suffix == ident or not SLUG.fullmatch(suffix):
        raise ValueError(f"Invalid task ID for {slug}: {ident}")

    def pascal(words):
        return "".join(word.capitalize() for word in words.split("-"))

    name = pascal(suffix)
    if name[0].isdigit():
        name = "Lemma" + name
    module = f"Conjectures.{pascal(slug)}.{name}"
    return {"module": module, "file": f"lean/{module.replace('.', '/')}.lean"}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def bilingual(value):
    return all(isinstance(value.get(k), str) and value[k].strip() for k in ("zh", "en"))


def build(root):
    gold = read(root / "gaps.json")
    others = read(root / "problems.json")
    desks = {"goldbach": gold, **others}
    seen = set()
    old_statements = {}
    old_locations = {}
    for slug, desk in desks.items():
        for g in desk["gaps"]:
            if MARK in g:
                old_statements[g["id"]] = g["statement"]
                old_locations[g["id"]] = {key: g[key] for key in ("file", "module")}
            else:
                seen.add(g["id"])
        desk["gaps"] = [g for g in desk["gaps"] if MARK not in g]
        key = "tracks" if slug == "goldbach" else "roadmap"
        desk[key] = [r for r in desk[key] if MARK not in r]
        if slug != "goldbach":
            for stage in desk[key]:
                stage["tasks"] = [t for t in stage["tasks"] if MARK not in t]
    tree = root / "problems"
    sources = set(tree.rglob("*.json"))
    consumed = set()
    for path in sorted(tree.glob("*/routes/*/route.json")):
        slug, _, route, _ = path.relative_to(tree).parts
        meta = read(path)
        if slug not in desks or not SLUG.fullmatch(route) or meta.get("id") != route:
            raise ValueError(f"Unknown problem or mismatched route: {path}")
        consumed.add(path)
        desk = desks[slug]
        entries = sorted((path.parent / "tasks").glob("*.json"))
        if not entries:
            raise ValueError(f"Empty route: {path}")
        if slug == "goldbach":
            existing = next((r for r in gold["tracks"] if r["id"] == route), None)
        else:
            stage = meta.get("existing_stage_en")
            existing = next((r for r in desk["roadmap"] if r["en"][0] == stage), None)
            if existing and existing.get("route_id", route) != route:
                raise ValueError(f"Use the existing stage route_id for {path}")
            if stage and not existing:
                raise ValueError(f"Unknown roadmap stage: {stage}")
        if existing is None:
            if not bilingual(meta.get("title", {})) or not bilingual(meta.get("description", {})):
                raise ValueError(f"New route requires bilingual title and description: {path}")
            if slug == "goldbach":
                existing = {k: meta[k] for k in ("id", "title", "description", "feeds")}
                gold["tracks"].append(existing)
            else:
                existing = {k: [meta["title"][k], meta["description"][k]] for k in ("en","zh")}
                existing["tasks"] = []
                desk["roadmap"].append(existing)
            existing[MARK] = route
        for task in entries:
            g = read(task)
            ident = task.stem
            if (ident != g.get("id") or not ident.startswith(f"L-{slug}-") or ident in seen
                    or not g.get("statement", "").strip() or g.get("track", route) != route):
                raise ValueError(f"Conflicting task ID, route or missing statement: {task}")
            if not bilingual(g.get("plain_statement", {})) or not bilingual(g.get("brief", {})):
                raise ValueError(f"Missing bilingual task description: {task}")
            if ident in old_statements and g["statement"] != old_statements[ident]:
                raise ValueError(f"Frozen statement changed: {ident}; create a new ID")
            location = old_locations.get(ident) or proof_location(slug, ident)
            for key, expected in location.items():
                # Old authoring tools may still emit the legacy path for a new ID.
                legacy_module = "PEqualNP.Outside." + ident.replace("-", "_")
                legacy = legacy_module if key == "module" else f"lean/{legacy_module.replace('.', '/')}.lean"
                if g.get(key, expected) not in (expected, legacy):
                    raise ValueError(f"Unexpected {key} for {ident}")
            g.update(location)
            seen.add(ident)
            consumed.add(task)
            g.update(track=route, route_source=route)
            desk["gaps"].append(g)
            if slug != "goldbach":
                existing["tasks"].append({"id": ident, **g["plain_statement"], MARK: route})
    if sources != consumed:
        raise ValueError(f"Unclassified JSON: {sources - consumed}")
    if old_statements.keys() - seen:
        raise ValueError("A published task source was removed")
    for key in ("file", "module"):
        paths = [g[key].casefold() for desk in desks.values() for g in desk["gaps"] if key in g]
        if len(paths) != len(set(paths)):
            raise ValueError(f"Conflicting proof {key} in the catalogue")
    for desk in desks.values():
        ids = {g["id"] for g in desk["gaps"]}
        graph = TopologicalSorter()
        for g in desk["gaps"]:
            deps = g.get("depends_on", [])
            if MARK in g and not set(deps) <= ids:
                raise ValueError(f"Unknown dependency in {g['id']}")
            graph.add(g["id"], *deps)
        tuple(graph.static_order())
    track_ids = {r["id"] for r in gold["tracks"]}
    for route in gold["tracks"]:
        if MARK in route and not set(route["feeds"]) <= track_ids:
            raise ValueError(f"Unknown downstream track: {route['id']}")
    return {"gaps.json": gold, "problems.json": others}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    compiled = build(ROOT)
    for name, data in compiled.items():
        path = ROOT / name
        if data == read(path):
            continue
        if not args.write:
            parser.exit(1, f"{name} needs regeneration: python research/build_catalogue.py --write\n")
        path.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + "\n").encode())


if __name__ == "__main__":
    main()
