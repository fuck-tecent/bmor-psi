#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 || ! $1 =~ ^[a-f0-9]{40}$ ]]; then
  echo "Usage: $0 <full commit SHA> <empty output directory> <trusted check-site.sh>" >&2
  exit 2
fi
sha=$1
output=$(realpath "$2")
checker=$(realpath "$3")
test -f "$checker"
test -z "$(ls -A -- "$output")"
archive=$(mktemp)
trap 'rm -f -- "$archive"' EXIT
curl --fail --silent --show-error --proto '=https' --connect-timeout 10 --max-time 80 \
  --output "$archive" "https://codeload.github.com/CGandGameEngineLearner/goldbach-proofs/tar.gz/$sha"

# Keep the layout and commit header expected by the existing Jenkins jobs.
python3 - "$sha" "$archive" "$output/source.tar" <<'PY'
import sys
import tarfile
from pathlib import PurePosixPath

sha, archive, output = sys.argv[1:]
prefix = "goldbach-proofs-" + sha
with tarfile.open(archive, "r:gz") as source:
    if source.pax_headers.get("comment") != sha:
        raise SystemExit("GitHub archive does not identify the requested commit")
    with tarfile.open(output, "w", pax_headers={"comment": sha}) as destination:
        for member in source:
            parts = PurePosixPath(member.name).parts
            if not parts or parts[0] != prefix or ".." in parts:
                raise SystemExit("Invalid GitHub archive path")
            if len(parts) == 1 and member.isdir():
                continue
            if len(parts) == 1 or not (member.isfile() or member.isdir() or member.issym()):
                raise SystemExit("Unsupported GitHub archive entry")
            contents = source.extractfile(member) if member.isfile() else None
            member.name = "/".join(parts[1:])
            member.pax_headers.pop("path", None)
            destination.addfile(member, contents)
PY
test "$(git get-tar-commit-id < "$output/source.tar")" = "$sha"
install -m 644 "$checker" "$output/check-site.sh"
