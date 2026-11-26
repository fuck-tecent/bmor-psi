#!/usr/bin/env bash
set -euo pipefail
LEAN_ROOT="${LEAN_ROOT:-$HOME/github.com/fuck-tencent/goldback-work/lean}"
cd "$(dirname "$0")"
export PATH="$(cd "$LEAN_ROOT" && lake env printenv PATH)"
export LEAN_PATH="$PWD/build:$(cd "$LEAN_ROOT" && lake env printenv LEAN_PATH)"
mkdir -p build
lean -o build/finite_large_sieve.olean finite_large_sieve.lean
lean -o build/separated_large_sieve.olean separated_large_sieve.lean
lean -o build/rational.olean rational.lean
lean -o build/vaughan.olean vaughan.lean
lean type1_bound.lean
echo "vinogradov-local: OK"
