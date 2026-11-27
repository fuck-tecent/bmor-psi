"""Open a reviewed catalogue PR for newly available direct proof imports."""

import base64
import json
import logging
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

from build_catalogue import build, read, register_community_imports, write

BRANCH = "automation/proof-imports"


def pending_imports(base):
    paths = [base / "research/gaps.json", base / "research/problems.json"]
    gaps = read(paths[0])["gaps"] + [
        gap for desk in read(paths[1]).values() for gap in desk["gaps"]
    ]
    available = {g["id"]: g["module"] for g in gaps if (base / g["file"]).is_file()}
    return any(g["id"] not in available and any(
        dep in available and available[dep] not in g.get("imports", [])
        for dep in g.get("depends_on", [])
    ) for g in gaps)


def open_import_pr(app, store, root, repo, revision_tree, git_blob):
    base = (store / "current").resolve(strict=True)
    if not pending_imports(base):
        return
    refs = app.request("GET", f"{repo}/git/matching-refs/heads/{BRANCH}-")
    owner = repo.split("/")[0]
    for ref in refs:
        branch = ref["ref"].removeprefix("refs/heads/")
        if app.request("GET", f"{repo}/pulls?state=open&base=main&head={owner}:{branch}"):
            return
    main = app.request("GET", f"{repo}/git/ref/heads/main")["object"]["sha"]
    tree = revision_tree(app, main)

    def available(path):
        proof = base / path
        return proof.is_file() and not proof.is_symlink() and tree.get(path, {}).get("sha") == git_blob(proof.read_bytes())

    with tempfile.TemporaryDirectory(prefix="proof-imports-", dir=store) as folder:
        stage = Path(folder)
        subprocess.run(["bash", root / "controller/prepare-site-revision.sh", main, stage,
                        root / "site-replay/check-site.sh"], check=True, timeout=120)
        before = {}
        with tarfile.open(stage / "source.tar") as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                if not member.isfile() or path.suffix != ".json" or path.parts[0] != "research":
                    continue
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError("Invalid catalogue archive path")
                before[member.name] = archive.extractfile(member).read()
                target = stage / member.name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(before[member.name])
        research = stage / "research"
        data = build(research)
        register_community_imports(research, data, proof_available=available)
        for name, catalogue in data.items():
            path = research / name
            if catalogue != read(path):
                write(path, catalogue)
        entries = []
        for name, old in before.items():
            new = (stage / name).read_bytes()
            if old == new:
                continue
            previous, updated = json.loads(old), json.loads(new)
            if "/tasks/" in name:
                previous["imports"] = updated.get("imports", [])
            else:
                old_desks = [previous] if name.endswith("/gaps.json") else previous.values()
                new_desks = [updated] if name.endswith("/gaps.json") else updated.values()
                for old_desk, new_desk in zip(old_desks, new_desks, strict=True):
                    for old_gap, new_gap in zip(old_desk["gaps"], new_desk["gaps"], strict=True):
                        if old_gap.get("imports", []) != new_gap.get("imports", []):
                            old_gap["imports"] = new_gap["imports"]
            if previous != updated:
                raise ValueError(f"Automatic import registration would change other fields: {name}")
            blob = app.request("POST", f"{repo}/git/blobs",
                               {"content": base64.b64encode(new).decode(), "encoding": "base64"})
            entries.append({"path": name, "mode": "100644", "type": "blob", "sha": blob["sha"]})
    if not entries:
        return
    parent = app.request("GET", f"{repo}/git/commits/{main}")
    updated = app.request("POST", f"{repo}/git/trees",
                          {"base_tree": parent["tree"]["sha"], "tree": entries})
    commit = app.request("POST", f"{repo}/git/commits",
                         {"message": "Register verified community proof imports",
                          "tree": updated["sha"], "parents": [main]})
    branch = f"{BRANCH}-{main[:12]}"
    if not any(ref["ref"] == f"refs/heads/{branch}" for ref in refs):
        app.request("POST", f"{repo}/git/refs", {"ref": f"refs/heads/{branch}", "sha": commit["sha"]})
    pr = app.request("POST", f"{repo}/pulls", {
        "head": branch, "base": "main", "title": "Register verified community proof imports",
        "body": "Registers direct catalogue dependencies whose proof source matches GitHub main and the Jenkins trusted snapshot. Review and merge through the catalogue release workflow.",
    })
    logging.info("Opened automatic proof import PR #%s", pr["number"])
