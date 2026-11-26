"""Replay historical PR 2643 through the prepared-proof runner."""

import json
import tempfile
from pathlib import Path

from github_app import GitHubApp
from prepare_proof import prepare
from verify_proof import verify

root = Path("/opt/goldbach-ci")
base = root / "lean-replay"
app = GitHubApp("/etc/goldbach-ci/github-app.pem")
with tempfile.TemporaryDirectory() as directory:
    work = Path(directory)
    file = prepare(app, 2643, "bc9371b5c21dc09d0037dcb31a36e8b65b4b72f2", base, work)
    manifest = verify(file, work, base / "lean", root / "toolchains/lean-4.36.0",
                      root / "controller/build-ownership.sh")
    print(json.dumps({"rests_on": len(manifest["rests_on"]), "defs": len(manifest["defs"])}))
