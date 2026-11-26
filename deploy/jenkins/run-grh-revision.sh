#!/usr/bin/env bash
set -euo pipefail

[[ $# -eq 1 ]] || { echo "Usage: $0 <prepared source archive>" >&2; exit 2; }
archive=$(realpath "$1")
base=/opt/goldbach-ci
project=$(realpath "${GOLDBACH_TRUSTED_BASE:-$base/lean-replay}/lean")
tc=$base/toolchains/lean-4.36.0

docker run --rm --pull never --runtime runsc --network none --read-only \
  --user 0:0 --cap-drop ALL --security-opt no-new-privileges --pids-limit 256 --log-driver none \
  --cpus 16 --memory 48g --memory-swap 48g \
  --tmpfs /tmp:rw,exec,nosuid,nodev,size=20g,mode=1777 \
  --mount "type=bind,source=$archive,target=/source.tar,readonly" \
  --mount "type=bind,source=$base/controller/check-grh.sh,target=/check-grh.sh,readonly" \
  --mount "type=bind,source=$tc,target=/toolchain,readonly" \
  --mount "type=bind,source=$project,target=/cache,readonly" \
  --env PATH=/toolchain/bin:/usr/bin:/bin --env LEAN_NUM_THREADS=16 \
  --entrypoint /usr/bin/timeout goldbach-site-agent:site-check --kill-after=15 1800 bash -euc '
    work=$(mktemp -d)
    cd "$work"
    tar -xf /source.tar -- lean
    for name in lean-toolchain lake-manifest.json lakefile.toml; do
      if ! cmp -s <(sed "s/\r$//" "lean/$name") <(sed "s/\r$//" "/cache/$name"); then
        echo "Prepared Lean cache does not match $name" >&2
        exit 3
      fi
    done
    mkdir -p lean/.lake
    # Lake checks source and import traces before reusing the read-only seed.
    cp -a --no-preserve=ownership /cache/.lake/packages lean/.lake/packages
    if [[ -d /cache/.lake/build ]]; then
      cp -a --no-preserve=ownership /cache/.lake/build lean/.lake/build
    fi
    export HOME="$work" GIT_CONFIG_NOSYSTEM=1
    export GOLDBACH_GRH_PROJECT="$work/lean"
    bash /check-grh.sh
  '
