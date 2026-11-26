#!/usr/bin/env bash
set -euo pipefail

cd "${GOLDBACH_GRH_PROJECT:-$(dirname "$0")/../../lean}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
# Users may import modules beyond the consumer's transitive dependencies.
mapfile -t modules < <(find PEqualNP/GRHSource -type f -name '*.lean' -print | LC_ALL=C sort)
if (( ${#modules[@]} == 0 )); then
  echo "No GRH source modules found" >&2
  exit 3
fi
for i in "${!modules[@]}"; do
  module=${modules[i]%.lean}
  modules[i]=+${module//\//.}
done
lake build checklemma +CheckerSuite.GRHConsumer "${modules[@]}"
lake env .lake/build/bin/checklemma CheckerSuite.GRHConsumer CheckerSuite/GRHConsumer.statement check
