#!/bin/bash
# Classify GCC torture tests as APPLICABLE or EXCLUDED
# Usage: ./classify.sh <torture-test-dir>
#
# Output: torture/classification.csv

set -e

TORTURE_DIR="${1:-gcc/testsuite/gcc.c-torture/execute}"

if [ ! -d "$TORTURE_DIR" ]; then
  echo "ERROR: Torture test directory not found: $TORTURE_DIR"
  echo "Download GCC sources or point to existing checkout."
  exit 1
fi

TOTAL=0
APPLICABLE=0
EXCLUDED_EXT=0
EXCLUDED_FEATURE=0

echo "file,classification,reason" > torture/classification.csv

for f in "$TORTURE_DIR"/*.c; do
  name=$(basename "$f")
  TOTAL=$((TOTAL + 1))

  # Check for GCC extensions
  if grep -qE '__builtin_|__attribute__\(\(cleanup|__extension__|__typeof__|__asm__|__label__|__auto_type' "$f" 2>/dev/null; then
    echo "$name,EXCLUDED_EXT,gcc_extension" >> torture/classification.csv
    EXCLUDED_EXT=$((EXCLUDED_EXT + 1))
    continue
  fi

  # Check for nested functions (GCC extension)
  if grep -qE '^\s+\w+\s+\w+\s*\([^)]*\)\s*\{' "$f" 2>/dev/null; then
    # Rough heuristic — may have false positives
    :
  fi

  # Check for unsupported C features
  if grep -qE '_Complex|_Atomic|__int128|alloca\b|_Alignas|_Generic|_Static_assert|_Noreturn' "$f" 2>/dev/null; then
    echo "$name,EXCLUDED_FEATURE,unsupported_c_feature" >> torture/classification.csv
    EXCLUDED_FEATURE=$((EXCLUDED_FEATURE + 1))
    continue
  fi

  # Check for VLAs
  if grep -qE 'int\s+\w+\[n\]|char\s+\w+\[\w+\]' "$f" 2>/dev/null; then
    # Rough VLA detection — may need refinement
    :
  fi

  echo "$name,APPLICABLE," >> torture/classification.csv
  APPLICABLE=$((APPLICABLE + 1))
done

echo ""
echo "=== Torture Test Classification ==="
echo "Total:            $TOTAL"
echo "APPLICABLE:       $APPLICABLE ($(( APPLICABLE * 100 / TOTAL ))%)"
echo "EXCLUDED_EXT:     $EXCLUDED_EXT ($(( EXCLUDED_EXT * 100 / TOTAL ))%)"
echo "EXCLUDED_FEATURE: $EXCLUDED_FEATURE ($(( EXCLUDED_FEATURE * 100 / TOTAL ))%)"
echo ""
echo "Target: 90%+ pass rate on $APPLICABLE applicable tests"
