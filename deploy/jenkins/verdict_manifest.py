"""Build an accepted verdict manifest from the separate trusted verifier result."""

import hashlib
import re

MODULE = re.compile(r"PEqualNP(?:\.[A-Za-z][A-Za-z0-9_]*)+")


def build_manifest(output, module, proof, read_trusted_source):
    lines = output.splitlines()
    if not lines or not lines[-1].startswith(f"ACCEPTED (check): {module};"):
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
    return {"rests_on": manifest_entries(rests_on), "defs": manifest_entries(modules("DEFS"))}
