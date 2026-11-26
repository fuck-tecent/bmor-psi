#!/usr/bin/env bash
set -euo pipefail

[[ $# -eq 1 ]] || { echo "Usage: $0 <prepared source archive>" >&2; exit 2; }
archive=$(realpath "$1")
base=/opt/goldbach-ci
tc=$base/toolchains/lean-4.36.0
project=$(realpath "${GOLDBACH_TRUSTED_BASE:-$base/lean-replay}/lean")
renderer=$base/controller/render-catalogue.py
path=$(cd "$project" && PATH="$tc/bin:$PATH" lake env printenv LEAN_PATH)
path=${path//"$project"/\/project}

docker run --rm --pull never --runtime runsc --network none --read-only \
  --cap-drop ALL --security-opt no-new-privileges --pids-limit 128 \
  --cpus 4 --memory 16g --memory-swap 16g \
  --tmpfs /tmp:rw,nosuid,nodev,size=512m,mode=1777 \
  --mount "type=bind,source=$archive,target=/source.tar,readonly" \
  --mount "type=bind,source=$renderer,target=/render-catalogue.py,readonly" \
  --mount "type=bind,source=$tc,target=/toolchain,readonly" \
  --mount "type=bind,source=$project,target=/project,readonly" \
  --env "LEAN_PATH=$path" --entrypoint /usr/bin/timeout goldbach-site-agent:site-check 1800 bash -euc '
    cd "$(mktemp -d)"
    tar -xf /source.tar
    for name in lean-toolchain lake-manifest.json; do
      if ! cmp -s <(sed "s/\r$//" "lean/$name") <(sed "s/\r$//" "/project/$name"); then
        echo "Prepared Lean cache does not match $name" >&2
        exit 3
      fi
    done
    python3 -B - << "PY"
import tomllib
from pathlib import Path


def catalogue_config(project):
    config = tomllib.loads((Path(project) / "lakefile.toml").read_text(encoding="utf-8"))
    # Catalogue statements use Mathlib. The GRH build target is unused here.
    config["lean_lib"] = [target for target in config["lean_lib"] if target["name"] != "GRHCompact"]
    return config


if catalogue_config("lean") != catalogue_config("/project"):
    raise SystemExit("Prepared Lean cache does not match the catalogue Lake configuration")
PY
    python3 -B research/build_catalogue.py
    python3 -B -m unittest research.test_route_sources research.test_catalogue deploy.test_landau deploy.test_publish_catalogue
    python3 -B /render-catalogue.py Catalogue.lean
    /toolchain/bin/lean Catalogue.lean
  '
