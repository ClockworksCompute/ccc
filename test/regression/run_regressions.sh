#!/bin/bash
# Run CCC-BUG regression fixtures. Exit non-zero if any fail.
set -uo pipefail
cd "$(dirname "$0")/../.."

PASS=0; FAIL=0

for test in test/regression/*Repro.lean; do
  name="$(basename "$test" .lean)"
  if lake env lean --run "$test" 2>&1; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "Regression results: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ] || exit 1
