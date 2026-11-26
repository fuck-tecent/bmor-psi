#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <directory with source.tar and check-site.sh>" >&2
  exit 2
fi
input=$(realpath "$1")
test -f "$input/source.tar"
test -f "$input/check-site.sh"

docker run --rm --pull never --runtime runsc --network none --read-only \
  --cap-drop ALL --security-opt no-new-privileges --pids-limit 128 \
  --cpus 2 --memory 2g --memory-swap 2g \
  --tmpfs /tmp:rw,nosuid,nodev,size=512m,mode=1777 \
  --mount "type=bind,source=$input,target=/input,readonly" \
  --entrypoint bash goldbach-site-agent:site-check -euc '
    test ! -e /var/run/docker.sock
    test ! -e /run/agent-secret
    work=$(mktemp -d)
    tar -xf /input/source.tar -C "$work"
    install -D /input/check-site.sh "$work/deploy/jenkins/check-site.sh"
    bash "$work/deploy/jenkins/check-site.sh"
  '
