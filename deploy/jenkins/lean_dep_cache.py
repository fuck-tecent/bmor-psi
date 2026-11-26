"""Share compiled community dependencies across isolated proof checks."""

import hashlib
import logging
import os
import re
import shutil
import tempfile
from pathlib import Path

OUTSIDE_IMPORT = re.compile(rb"^import (PEqualNP\.Outside\.[A-Za-z0-9_]+)[ \t]*\r?$", re.MULTILINE)
LOCK_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


def context(project, work, build_id):
    digest = hashlib.sha256(build_id)
    for name in LOCK_FILES:
        digest.update(hashlib.sha256((project / name).read_bytes()).digest())
    for module in sorted((work / "base-imports.txt").read_text().splitlines()):
        artifact = project.joinpath(".lake", "build", "lib", "lean", *module.split(".")).with_suffix(".olean")
        digest.update(module.encode() + b"\0")
        with artifact.open("rb") as stream:
            digest.update(hashlib.file_digest(stream, "sha256").digest())
    return digest.digest()


def key(context_digest, module, source, earlier_keys):
    digest = hashlib.sha256(context_digest + module.encode() + b"\0")
    digest.update(hashlib.sha256(source).digest())
    # The guard only accepts one bare import per line in outside sources.
    for name in OUTSIDE_IMPORT.findall(source):
        digest.update(bytes.fromhex(earlier_keys[name.decode("ascii")]))
    return digest.hexdigest()


def compile_cached(cache, module, cache_key, artifact, build):
    import fcntl

    stored = cache / (cache_key + ".olean")
    with (cache / (cache_key + ".lock")).open("a+b") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if stored.is_file():
            shutil.copyfile(stored, artifact)
            logging.info("Lean dependency cache hit: %s", module)
            return
        logging.info("Lean dependency cache miss: %s", module)
        build()
        with tempfile.NamedTemporaryFile(dir=cache) as pending:
            shutil.copyfile(artifact, pending.name)
            os.chmod(pending.name, 0o444)
            # Link only a complete artifact, leaving no partially written cache entry.
            os.link(Path(pending.name), stored)
