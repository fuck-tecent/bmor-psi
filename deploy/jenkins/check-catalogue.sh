#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "Usage: $0 <Lean toolchain directory> <prepared Lake project> <Catalogue.lean>" >&2
  exit 2
fi

toolchain=$(realpath "$1")
project=$(realpath "$2")
catalogue=$(realpath "$3")
test -x "$toolchain/bin/lean"
test -f "$catalogue"
test -r "$project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"

cd "$project"
lean_path=$(PATH="$toolchain/bin:$PATH" lake env printenv LEAN_PATH)
lean_path=${lean_path//"$project"/\/project}
docker run --rm --pull never --runtime runsc --network none --read-only \
  --cap-drop ALL --security-opt no-new-privileges --pids-limit 128 \
  --cpus 4 --memory 16g --memory-swap 16g \
  --tmpfs /tmp:rw,nosuid,nodev,size=256m,mode=1777 \
  --mount "type=bind,source=$toolchain,target=/toolchain,readonly" \
  --mount "type=bind,source=$project,target=/project,readonly" \
  --mount "type=bind,source=$catalogue,target=/input/Catalogue.lean,readonly" \
  --env "LEAN_PATH=$lean_path" --entrypoint /toolchain/bin/lean \
  docker.m.daocloud.io/jenkins/jenkins@sha256:4d85f6cf5a8939647921564952d12a5a761f32a3bc520c2f4e5c3cafa7ea660f \
  /input/Catalogue.lean
