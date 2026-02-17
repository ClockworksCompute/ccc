#!/bin/bash
# Gate script for CCC demo programs.
# Validates all 7 demos through the full pipeline.
# Note: does NOT use set -e — we capture non-zero exit codes intentionally.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CCC_DIR="$REPO_ROOT/ccc"
CCC="$CCC_DIR/.lake/build/bin/ccc"
PASS=0
FAIL=0

if [[ ! -f "$CCC" ]]; then
  echo "ERROR: CCC binary not found at $CCC"
  echo "Run: cd ccc && lake build ccc"
  exit 1
fi

echo "CCC Gate Script — 7 Demo Programs"
echo "=================================="
echo ""

# Must be REJECTED (ccc exits non-zero)
for prog in heartbleed_mini buffer_overflow use_after_free double_free null_deref; do
  output=$("$CCC" "$CCC_DIR/test/demo/${prog}.c" 2>&1)
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "PASS: ${prog}.c REJECTED ✓"
    PASS=$((PASS+1))
  else
    echo "FAIL: ${prog}.c should have been REJECTED"
    echo "  Output: $output"
    FAIL=$((FAIL+1))
  fi
done

# Must be ACCEPTED (verify-only on all platforms)
for prog in heartbleed_fixed safe_server; do
  output=$("$CCC" "$CCC_DIR/test/demo/${prog}.c" 2>&1)
  rc=$?
  if [ $rc -eq 0 ]; then
    echo "PASS: ${prog}.c ACCEPTED ✓"
    PASS=$((PASS+1))
  else
    echo "FAIL: ${prog}.c should have been ACCEPTED"
    echo "  Output: $output"
    FAIL=$((FAIL+1))
  fi
done

echo ""
echo "=================================="
echo "Results: $PASS passed, $FAIL failed out of 7"

if [ "$FAIL" -ne 0 ]; then
  exit 1
fi
echo "ALL PASS ✓"
