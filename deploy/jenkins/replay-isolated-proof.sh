#!/usr/bin/env bash
set -euo pipefail

base=/opt/goldbach-ci
project=$base/lean-replay/lean
tc=$base/toolchains/lean-4.36.0
image=docker.m.daocloud.io/jenkins/jenkins@sha256:4d85f6cf5a8939647921564952d12a5a761f32a3bc520c2f4e5c3cafa7ea660f
module=PEqualNP.Outside.L_goldbach_prime_weight_extraction
file=${module//./\/}
cd "$project"
scratch=$(mktemp -d)
trap 'rm -f "$scratch/in/statement.txt" "$scratch/build/$file.olean" "$scratch/marker"; rmdir "$scratch/build/PEqualNP/Outside" "$scratch/build/PEqualNP" "$scratch/build" "$scratch/in" "$scratch"' EXIT
install -d -m 755 "$scratch/in"
install -d -m 755 "$scratch/build/PEqualNP"
install -d -m 755 -o 1000 -g 1000 "$scratch/build/PEqualNP/Outside"
python3 - "$scratch/in/statement.txt" <<'PY'
import json, pathlib, sys
gaps = json.loads(pathlib.Path("../research/gaps.json").read_text(encoding="utf-8"))["gaps"]
statement = next(g["statement"] for g in gaps if g["id"] == "L-goldbach-prime-weight-extraction")
pathlib.Path(sys.argv[1]).write_text(statement, encoding="utf-8")
PY

path=$(PATH="$tc/bin:$PATH" lake env printenv LEAN_PATH)
path=${path//"$project"/\/project}
flags=(--rm --pull never --runtime runsc --network none --read-only --cap-drop ALL
       --security-opt no-new-privileges --pids-limit 128 --memory 16g --cpus 4
       --tmpfs /tmp:rw,nosuid,nodev,size=256m
       --mount "type=bind,source=$tc,target=/toolchain,readonly"
       --mount "type=bind,source=$project,target=/project,readonly"
       --env "LEAN_SYSROOT=/toolchain" --env "PATH=/toolchain/bin:/usr/bin:/bin")

touch "$scratch/marker"
docker run "${flags[@]}" --workdir /project --env "LEAN_PATH=$path" \
  --mount "type=bind,source=$scratch/build,target=/result" \
  --entrypoint /toolchain/bin/lean "$image" -o "/result/$file.olean" "$file.lean"
bash "$base/controller/build-ownership.sh" "$scratch/build" "$scratch/marker" "$scratch/build/$file.olean" 0 1000
sha256sum "$scratch/build/$file.olean"

docker run "${flags[@]}" --env "LEAN_PATH=$path" \
  --mount "type=bind,source=$scratch/build/$file.olean,target=/project/.lake/build/lib/lean/$file.olean,readonly" \
  --mount "type=bind,source=$scratch/in,target=/input,readonly" \
  --entrypoint /project/.lake/build/bin/checklemma "$image" "$module" /input/statement.txt check
