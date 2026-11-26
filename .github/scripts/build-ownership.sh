#!/usr/bin/env bash
# Run as the checker account after the isolated compile and its cleanup.
set -eu
build=$1
marker=$2
expected_olean=$3
checker_code=$4
compiler_user=${5:-outsider}

# Emit a fixed flag. Build paths can contain text supplied by the compile.
if ! foreign=$(find "$build" -type f -newer "$marker" ! -user "$compiler_user" -printf x -quit 2>/dev/null); then
  echo "Could not inspect the build tree for file ownership." >&2
  exit 3
fi
if [ -n "$foreign" ]; then
  echo "A new or modified build file belongs to an account other than outsider." >&2
  exit 3
fi

# A rejected proof may produce no object. A successful check must have compiled
# this submission's module under the locked account. find does not follow links.
if [ "$checker_code" = 0 ]; then
  if ! owned=$(find "$expected_olean" -maxdepth 0 -type f -user "$compiler_user" -newer "$marker" -printf x 2>/dev/null) || [ "$owned" != x ]; then
    echo "Missing a fresh compiled proof object owned by the compiler account." >&2
    exit 3
  fi
fi
