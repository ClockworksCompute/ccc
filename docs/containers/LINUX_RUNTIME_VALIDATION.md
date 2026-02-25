# Linux x86-64 Runtime Validation for CCC

CCC emits x86-64 Linux assembly. On macOS/arm64, the verifier and emitter work
but linking and running binaries requires a real Linux x86-64 environment.

## Setup: Colima + Docker CLI (free, no Docker Desktop)

### Install (one-time)

```bash
brew install colima docker qemu lima-additional-guestagents
```

### Start VM

```bash
colima start --arch x86_64 --cpu 2 --memory 4 --runtime docker
```

### Stop VM

```bash
colima stop
```

## Running Validation

### Quick validation script

```bash
cd ccc
bash scripts/runtime/linux_validate.sh
```

### Manual validation

```bash
cd ccc

# 1. Generate assembly (runs on macOS via Lean)
lake env lean -q --run /dev/stdin <<'LEAN'
import CCC
def main : IO Unit := do
  for (name, file) in [("heartbleed_fixed", "test/demo/heartbleed_fixed.c"),
                        ("safe_server", "test/demo/safe_server.c")] do
    let src ← IO.FS.readFile file
    let result := CCC.compile src s!"{name}.c"
    match result.assembly with
    | some asm => IO.FS.writeFile s!".gate_staging/{name}.s" asm
    | none => IO.Process.exit 1
LEAN

# 2. Run in Linux container (Colima mounts home dir by default)
docker run --rm --platform linux/amd64 \
  -v "$(pwd):/ccc:ro" \
  ubuntu:22.04 bash -c '
apt-get update -qq >/dev/null 2>&1
apt-get install -y -qq gcc binutils >/dev/null 2>&1
cd /tmp
gcc -c -o rt.o /ccc/runtime/ccc_runtime.c
for spec in "heartbleed_fixed:13" "safe_server:2"; do
  name="${spec%%:*}"; expected="${spec##*:}"
  as -o ${name}.o /ccc/.gate_staging/${name}.s
  gcc -o ${name} ${name}.o rt.o -no-pie
  set +e; ./${name}; actual=$?; set -e
  if [ "$actual" -eq "$expected" ]; then
    echo "PASS: $name exit=$actual"
  else
    echo "FAIL: $name exit=$actual expected=$expected"
  fi
done'
```

## Known Results (2026-02-18, first-ever Linux runtime validation)

| Program | Expected exit | Actual | Status | Notes |
|---------|-------------|--------|--------|-------|
| `return 42` (trivial) | 42 | 42 | ✅ | |
| `fibonacci.c` | 55 | 55 | ✅ | Pure int arithmetic + branches |
| pointer deref | 10 | 10 | ✅ | Stack pointer |
| malloc/free | 7 | 7 | ✅ | Heap allocation + runtime |
| struct (int fields) | 7 | 7 | ✅ | Stack struct, field access |
| struct pointer passing | 7 | 7 | ✅ | Cross-function struct* |
| **struct + char array** | 3 | **segfault** | ❌ | struct-with-inline-array codegen bug |
| **heartbleed_fixed** | 13 | **segfault** | ❌ | struct-with-inline-array codegen bug |
| **safe_server** | 2 | **segfault** | ❌ | struct-with-inline-array codegen bug |

Root cause: emitter dereferences inline array field base address as a pointer
(`movq (%rax), %rax` instead of using `%rax` directly). See `struct-with-inline-array codegen bug`.

## Architecture notes

- Colima runs a QEMU x86-64 Linux VM on Apple Silicon (~3-5x slower than native).
- Docker CLI (`brew install docker`) is the client only — no Docker Desktop needed.
- Colima auto-mounts the user home directory via virtiofs.
- `/tmp` is NOT shared between macOS and the VM — stage files inside home dir.

## Fallback: Podman

```bash
brew install podman
podman machine init --cpus 2 --memory 4096
podman machine start
# Use `podman` in place of `docker` in commands above
podman machine stop
```
