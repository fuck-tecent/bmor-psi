"""Build an accepted verdict manifest from the separate trusted verifier result."""

import hashlib
import re

MODULE = re.compile(r"(?:PEqualNP|Conjectures)(?:\.[A-Za-z][A-Za-z0-9_]*)+")
PROOF_MODULE = re.compile(r"(?:PEqualNP\.Outside\.L_[a-z0-9_]+|Conjectures\.[A-Z][A-Za-z0-9]*\.[A-Z][A-Za-z0-9]*)")


def module_path(module):
    return module.replace(".", "/") + ".lean"


def build_manifest(output, module, proof, read_trusted_source, kind="check"):
    lines = output.splitlines()
    if kind not in {"check", "refute", "reduce"} or not lines or not lines[-1].startswith(f"ACCEPTED ({kind}): {module};"):
        raise ValueError("Verifier did not accept the expected module")

    def modules(label):
        rows = [line.split()[1:] for line in lines if line.startswith(label + " ")]
        if len(rows) != 1 or not rows[0] or not all(MODULE.fullmatch(name) for name in rows[0]):
            raise ValueError(f"Invalid verifier {label} list")
        return rows[0]

    def manifest_entries(names):
        return [
            {"module": name, "sha256": hashlib.sha256(
                proof if name == module else read_trusted_source(name)).hexdigest()}
            for name in names
        ]

    rests_on = modules("MODULES")
    if module not in rests_on:
        raise ValueError("Verifier did not list the submitted proof")
    manifest = {"rests_on": manifest_entries(rests_on), "defs": manifest_entries(modules("DEFS"))}
    child_lines = [line for line in lines if line.startswith("CHILD")]
    if kind == "reduce":
        n = len(child_lines) - 1
        if not 2 <= n <= 4 or child_lines[0] != f"CHILDREN {n}":
            raise ValueError("Invalid number of verified premises")
        children = []
        for i, line in enumerate(child_lines[1:], 1):
            prefix = f"CHILD {i} "
            if not line.startswith(prefix) or not 0 < len(line[len(prefix):]) <= 2000:
                raise ValueError("Invalid verified premise")
            children.append(line[len(prefix):])
        manifest["children"] = children
        descriptions = [{} for _ in children]
        for match in re.finditer(r"^-- child ([1-4]) (zh|en): ([^\r\n]{1,500})$", proof.decode(), re.MULTILINE):
            position, lang, words = match.groups()
            if int(position) <= n:
                descriptions[int(position) - 1][lang] = words.strip()
        if any(d.keys() == {"zh", "en"} and all(d.values()) for d in descriptions):
            manifest["child_descriptions"] = [
                d if d.keys() == {"zh", "en"} and all(d.values()) else None for d in descriptions
            ]
    elif child_lines:
        raise ValueError("Unexpected reduction premises")
    return manifest
