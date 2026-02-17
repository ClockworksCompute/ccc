#!/bin/bash
# CCC Linux x86-64 runtime validation.
# Requires: Colima + Docker CLI (or Podman).
#
# Exit codes:
#   0 = all tests pass
#   1 = semantic failure (wrong exit code, link error, segfault)
#   2 = infra-blocked (no container runtime)
set -uo pipefail
cd "$(dirname "$0")/../.."

echo "=== CCC Linux x86-64 Runtime Validation ==="

# Detect container runtime
RUNTIME=""
for cmd in docker nerdctl podman; do
  if command -v "$cmd" &>/dev/null; then
    # Check daemon is reachable
    if $cmd info >/dev/null 2>&1; then
      RUNTIME="$cmd"
      break
    fi
  fi
done

if [ -z "$RUNTIME" ]; then
  echo "SKIP: no container runtime with running daemon"
  echo "  Install: brew install colima docker qemu lima-additional-guestagents"
  echo "  Start:   colima start --arch x86_64 --cpu 2 --memory 4 --runtime docker"
  exit 2
fi
echo "Runtime: $RUNTIME"

# Generate assembly (macOS side, via Lean)
echo ""
echo "Generating assembly..."
mkdir -p .gate_staging
lake env lean -q --run /dev/stdin <<'LEAN'
import CCC
def main : IO Unit := do
  for (name, file) in [("heartbleed_fixed", "test/demo/heartbleed_fixed.c"),
                        ("safe_server", "test/demo/safe_server.c"),
                        ("trivial", "INLINE:int main() { return 42; }"),
                        ("fibonacci", "../factory/holdout/ccc/fibonacci.c")] do
    let src ← if file.startsWith "INLINE:" then
      pure (file.drop 7)
    else
      IO.FS.readFile file
    let result := CCC.compile src s!"{name}.c"
    match result.assembly with
    | some asm => IO.FS.writeFile s!".gate_staging/{name}.s" asm
    | none => IO.eprintln s!"FAIL: {name} did not produce assembly"; IO.Process.exit 1
  IO.println "Assembly generated."
LEAN
[ $? -eq 0 ] || { echo "FAIL: assembly generation"; exit 1; }

# Run validation in Linux container
echo ""
echo "Running in Linux x86-64 container..."
CCC_DIR="$(pwd)"

RESULT=$($RUNTIME run --rm --platform linux/amd64 \
  -v "$CCC_DIR:/ccc:ro" \
  ubuntu:22.04 bash -c '
apt-get update -qq >/dev/null 2>&1
apt-get install -y -qq gcc binutils file >/dev/null 2>&1
cd /tmp
gcc -c -o rt.o /ccc/runtime/ccc_runtime.c 2>&1

for spec in "trivial:42:none" "fibonacci:55:none" "heartbleed_fixed:13:rt" "safe_server:2:rt"; do
  name=$(echo "$spec" | cut -d: -f1)
  expected=$(echo "$spec" | cut -d: -f2)
  needs_rt=$(echo "$spec" | cut -d: -f3)

  as -o ${name}.o /ccc/.gate_staging/${name}.s 2>&1 || { echo "RESULT:${name}:ASM_FAIL"; continue; }

  if [ "$needs_rt" = "rt" ]; then
    gcc -o ${name} ${name}.o rt.o -no-pie 2>&1 || { echo "RESULT:${name}:LINK_FAIL"; continue; }
  else
    gcc -o ${name} ${name}.o -no-pie 2>&1 || { echo "RESULT:${name}:LINK_FAIL"; continue; }
  fi

  file ${name} >&2

  set +e; ./${name}; actual=$?; set -e
  echo "RESULT:${name}:${actual}:${expected}"
done
' 2>&1)

echo "$RESULT"

# Parse and report
echo ""
echo "=== Results ==="
FAIL=0
PASS=0
for spec in "trivial:42" "fibonacci:55" "heartbleed_fixed:13" "safe_server:2"; do
  name="${spec%%:*}"; expected="${spec##*:}"
  line=$(echo "$RESULT" | grep "^RESULT:${name}:" | tail -1)

  if echo "$line" | grep -q "ASM_FAIL\|LINK_FAIL"; then
    status=$(echo "$line" | cut -d: -f3)
    echo "✗ FAIL  $name  $status"
    FAIL=$((FAIL + 1))
  elif [ -n "$line" ]; then
    actual=$(echo "$line" | cut -d: -f3)
    if [ "$actual" = "$expected" ]; then
      echo "✓ PASS  $name  exit=$actual (expected $expected)"
      PASS=$((PASS + 1))
    else
      echo "✗ FAIL  $name  exit=$actual (expected $expected)"
      FAIL=$((FAIL + 1))
    fi
  else
    echo "✗ FAIL  $name  no result from container"
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "═══════════════════════════════════════════"
echo "  Linux validation: $PASS passed, $FAIL failed"
echo "═══════════════════════════════════════════"
[ "$FAIL" -eq 0 ] || exit 1
