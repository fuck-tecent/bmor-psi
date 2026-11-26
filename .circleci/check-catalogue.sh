#!/usr/bin/env bash
set -euo pipefail
printf "Catalogue commit %s\n" "$(git rev-parse HEAD)"
python3 -B research/build_catalogue.py
python3 -B -m unittest research.test_route_sources research.test_catalogue deploy.test_landau deploy.test_publish_catalogue -v
export RUNNER_TEMP="$(mktemp -d)"
trap 'rm -rf -- "$RUNNER_TEMP"' EXIT
cd lean
curl --retry 4 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat lean-toolchain)"
time lake exe cache get
(cd .. && python3 -B deploy/jenkins/render-catalogue.py "$RUNNER_TEMP/Catalogue.lean")
time "$HOME/.elan/bin/lake" env lean "$RUNNER_TEMP/Catalogue.lean"
