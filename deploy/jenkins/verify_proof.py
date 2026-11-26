"""Compile a prepared proof and verify its statement in a separate sandbox."""

import os
import re
import subprocess
from pathlib import Path

from lean_dep_cache import compile_cached, context as cache_context, key as cache_key
from verdict_manifest import MODULE, PROOF_MODULE, build_manifest, module_path

PROOF_CPUS = 8
IMAGE = "docker.m.daocloud.io/jenkins/jenkins@sha256:4d85f6cf5a8939647921564952d12a5a761f32a3bc520c2f4e5c3cafa7ea660f"


class ProofRejected(ValueError):
    """The trusted verifier returned a proof rejection."""


def verifier_manifest(result, module, proof, read_source):
    lines = result.stdout.splitlines()
    if result.returncode == 1 and lines and re.match(r"^REJECTED \([a-z-]+\): ", lines[-1]):
        raise ProofRejected(lines[-1])
    result.check_returncode()
    return build_manifest(result.stdout, module, proof, read_source)


def check_cache(project, work):
    build = project / ".lake/build"
    if not (build / "bin/checklemma").is_file():
        raise FileNotFoundError("The trusted Lean cache has no checklemma executable")
    for module in (work / "base-imports.txt").read_text().splitlines():
        if not MODULE.fullmatch(module):
            raise ValueError("Invalid trusted dependency module")
        artifact = (build / "lib/lean").joinpath(*module.split(".")).with_suffix(".olean")
        if not artifact.is_file():
            raise FileNotFoundError(f"The trusted Lean cache is missing {module}")


def verify(file, work, project, toolchain, ownership_check):
    check_cache(project, work)
    dependencies = (work / "outside-build-order.txt").read_text().splitlines()
    if any(not PROOF_MODULE.fullmatch(name) for name in dependencies):
        raise ValueError("Invalid outside dependency module")
    module = (work / "pr.module").read_text().strip()
    leaf = module_path(module)
    if not PROOF_MODULE.fullmatch(module) or file != "lean/" + leaf:
        raise ValueError("Invalid registered proof module or path")
    proof = work / "source"
    (proof / leaf).parent.mkdir(parents=True)
    (proof / leaf).write_bytes((work / "proof.lean").read_bytes())
    (proof / "statement.txt").write_bytes((work / "statement.txt").read_bytes())
    out = work / "build"
    out.mkdir()
    os.chown(out, 1000, 1000)
    marker = work / "marker"
    marker.touch()

    # Resolve the search path against the prepared project cache once per build.
    lean_path = subprocess.check_output(
        [str(toolchain / "bin/lake"), "env", "printenv", "LEAN_PATH"],
        cwd=project, text=True, timeout=30,
    ).strip().replace(str(project), "/project")
    flags = [
        "docker", "run", "--rm", "--pull", "never", "--runtime", "runsc",
        "--network", "none", "--read-only", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges", "--pids-limit", "128",
        "--memory", "16g", "--memory-swap", "16g", "--cpus", str(PROOF_CPUS),
        "--ulimit", "fsize=536870912:536870912", "--ulimit", "core=0:0", "--log-driver", "none",
        "--tmpfs", "/tmp:rw,nosuid,nodev,size=256m",
        "--mount", f"type=bind,source={toolchain},target=/toolchain,readonly",
        "--mount", f"type=bind,source={project},target=/project,readonly",
        "--mount", f"type=bind,source={proof},target=/input,readonly",
        "--env", f"LEAN_PATH={lean_path}", "--env", "LEAN_SYSROOT=/toolchain",
        "--env", "PATH=/toolchain/bin:/usr/bin:/bin",
    ]
    # Only the guarded closure is visible to the submission and independent replay.
    compiled = work / "compiled"
    for root in ("PEqualNP/Outside", "Conjectures"):
        (compiled / root).mkdir(parents=True)
        flags += ["--mount", f"type=bind,source={compiled / root},target=/project/.lake/build/lib/lean/{root},readonly"]

    def compile_module(source, seconds, *, submission=False):
        artifact = Path(source).with_suffix(".olean").name
        result = subprocess.run(flags + [
            "--mount", f"type=bind,source={out},target=/output",
            "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", str(seconds),
            "/toolchain/bin/lean", f"--threads={PROOF_CPUS}", "--root=/input", "-o", f"/output/{artifact}", f"/input/{source}",
        ], stdout=subprocess.PIPE if submission else None,
           stderr=subprocess.STDOUT if submission else None, text=True)
        if submission and result.returncode == 1 and re.search(
                rf"^/input/{re.escape(source)}:[0-9]+:[0-9]+: error(?:\[[^]]+\])?:",
                result.stdout, re.MULTILINE):
            raise ProofRejected("Lean reported a compilation error in the submitted file")
        result.check_returncode()
        subprocess.run([
            "bash", str(ownership_check), str(out), str(marker), str(out / artifact), "0", "1000",
        ], check=True, timeout=30)
        destination = compiled / Path(source).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        (out / artifact).replace(destination)

    cache_dir = os.environ.get("GOLDBACH_LEAN_DEP_CACHE")
    cache = Path(cache_dir) if cache_dir and dependencies else None
    context = cache_context(project, work, f"goldbach-olean-v2:{IMAGE}:{PROOF_CPUS}".encode()) if cache else None
    keys = {}
    for name in dependencies:
        source = module_path(name)
        content = (project / source).read_bytes()
        (proof / source).parent.mkdir(parents=True, exist_ok=True)
        (proof / source).write_bytes(content)
        if cache is None:
            compile_module(source, 240)
            continue
        keys[name] = cache_key(context, name, content, keys)
        artifact = compiled / Path(source).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        compile_cached(cache, name, keys[name], artifact, lambda: compile_module(source, 240))
    compile_module(leaf, 1200, submission=True)
    verification = subprocess.run(flags + [
        "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", "1200",
        "/project/.lake/build/bin/checklemma", module, "/input/statement.txt", "check",
    ], stdout=subprocess.PIPE, text=True)

    def read_source(name):
        return project.joinpath(*name.split(".")).with_suffix(".lean").read_bytes()

    return verifier_manifest(verification, module, (proof / leaf).read_bytes(), read_source)
