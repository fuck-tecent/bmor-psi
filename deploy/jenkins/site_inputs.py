"""Prepare trusted main-branch website inputs before Jenkins queues the check."""

import subprocess
import tempfile
from pathlib import Path

from github_revision import REPO, SHA


def prepare_main_site(app, job_id, sha, pr, root):
    if type(job_id) is not int or job_id < 1 or pr != 0 or not SHA.fullmatch(sha):
        raise ValueError("The trusted website runner requires a main-branch task")
    comparison = app.request("GET", f"{REPO}/compare/{sha}...main?per_page=1")
    if comparison["status"] not in ("ahead", "identical") or comparison["merge_base_commit"]["sha"] != sha:
        raise ValueError("Website revision is not in main history")

    base = Path(root)
    jobs = base / "site-replay" / "jobs"
    jobs.mkdir(parents=True, exist_ok=True)
    dest = jobs / str(job_id)
    if not dest.is_dir():
        with tempfile.TemporaryDirectory(dir=jobs, prefix=".prepare-") as scratch:
            staged = Path(scratch) / "site"
            staged.mkdir(mode=0o755)
            subprocess.run(["bash", str(base / "controller" / "prepare-site-revision.sh"),
                            sha, str(staged), str(base / "site-replay" / "check-site.sh")],
                           check=True, timeout=120)
            staged.rename(dest)

    with (dest / "source.tar").open("rb") as archive:
        archived_sha = subprocess.check_output(["git", "get-tar-commit-id"], stdin=archive,
                                                text=True, timeout=10).strip()
    if archived_sha != sha:
        raise ValueError("Prepared website source does not match the requested revision")
