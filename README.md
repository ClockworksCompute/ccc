# CCC — Clockworks C Compiler

A verified C compiler that proves memory safety at compile time.
Written in Lean 4. Catches Heartbleed-class bugs structurally.

## Versioning and Changelog

- Version source of truth: [`VERSION`](./VERSION)
- Current release: `v0.1.0`
- Release notes: [`CHANGELOG.md`](./CHANGELOG.md)

## Setup (if Lean is not installed)

CCC uses the Lean 4 toolchain (`lean` + `lake`).
Install it once with [`elan`](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

lean --version
lake --version
```

`lake` will then automatically download the exact Lean version pinned in
`lean-toolchain`.

## Quick Start

```bash
# Build
lake build ccc

# Option 1: Use directly
.lake/build/bin/ccc my_program.c

# Option 2: Use like gcc — add to PATH
export PATH="$(pwd)/bin:$PATH"
ccc my_program.c                     # verify only (macOS)
ccc my_program.c -o my_program       # verify + link (Linux x86-64)
```

The `bin/ccc` wrapper auto-builds on first use — just add it to your PATH
and go.

## Try It

```bash
./examples/run
```

This runs all 7 example programs and shows CCC catching real bugs:
use-after-free, buffer overflow, null deref, double free, and the
Heartbleed pattern — then accepting the safe versions.

## Hello World

CCC works with a **safe subset of C** — no preprocessor, no `printf`, no
string literals. The simplest valid program:

```c
// hello.c — returns exit code 42
int main() {
    return 42;
}
```

```
$ ccc hello.c
Compiling hello.c...
  ✓ 1 functions analyzed
  ✓ 0 pointer operations verified
  ✓ 0 array accesses verified (0 static, 0 runtime-bounded)
  ✓ 0 memory safety violations
  ✓ Assembled: hello (8KB)
```

A more interesting example with heap allocation:

```c
// point.c — allocate a struct, use it safely, free it
struct Point {
    int x;
    int y;
};

int main() {
    struct Point *p = malloc(sizeof(struct Point));
    if (p == 0) { return -1; }   // null check required!
    p->x = 3;
    p->y = 4;
    int sum = p->x + p->y;
    free(p);
    return sum;                   // exits 7
}
```

CCC verifies this is safe: the null check promotes `p` from nullable to
checked-live, all dereferences happen while `p` is live, and `free` is
called exactly once. Remove the `if (p == 0)` check and CCC will reject it.

## What CCC Catches

CCC proves 5 memory safety properties at compile time:

### 1. Buffer Overflow (CWE-120, CWE-787)

```c
int main() {
    int arr[4];
    arr[4] = 99;   // ← index 4 exceeds capacity 4
    return 0;
}
```

```
ERROR: Memory safety violation at line 3:
  arr[4] = 99;
  Index may exceed array bounds (capacity=4, required<5)
  Fix: Add or strengthen bounds checks before this access
```

### 2. Use-After-Free (CWE-416)

```c
int main() {
    int *p = malloc(sizeof(int));
    if (p == 0) { return -1; }
    *p = 42;
    free(p);
    int val = *p;   // ← p was freed!
    return val;
}
```

```
ERROR: Memory safety violation at line 6:
  int val = *p;
  Dereference of pointer after it was freed
  Fix: Do not use the pointer after free; set it to null and avoid dereference
```

This also works through **pointer aliases**:

```c
int *q = p;
free(q);     // frees the allocation
int val = *p; // ← CCC catches this: p aliases q, also freed
```

### 3. Double Free (CWE-415)

```c
free(p);
free(p);   // ← already freed!
```

```
ERROR: Double free detected
```

### 4. Null Dereference (CWE-476)

```c
int *p = malloc(sizeof(int));
*p = 42;   // ← p might be null (no null check)
```

```
ERROR: Dereference of potentially-null pointer 'p'
Fix: Check 'p' against null (e.g., if (p != 0) { ... }) before dereference
```

### 5. The Heartbleed Pattern (CWE-126)

The headline demo — CCC catches the same class of bug as Heartbleed:

```c
struct Request {
    int payload_length;
    char payload[64];
};

void process(struct Request *req) {
    char response[64];
    // Bug: uses req->payload_length without bounds check
    // Could read beyond payload buffer
    memcpy(response, req->payload, req->payload_length);
}
```

```
ERROR: memcpy length exceeds buffer size
Fix: Prove len is bounded by both source and destination buffer sizes
```

The fixed version adds a bounds check:

```c
void process(struct Request *req) {
    if (req->payload_length < 0 || req->payload_length > 64) {
        return;
    }
    char response[64];
    memcpy(response, req->payload, req->payload_length);  // ✓ safe
}
```

## Supported C Subset

### Types

| Type | Example | Notes |
|------|---------|-------|
| `int` | `int x = 42;` | 32-bit signed integer |
| `char` | `char c = 65;` | 8-bit character |
| `long` | `long n = 100;` | 64-bit signed integer |
| Pointer | `int *p = malloc(sizeof(int));` | Heap or stack pointer |
| Array | `int arr[10];` | Fixed-size stack array |
| Struct | `struct Point { int x; int y; };` | Named structs with fields |
| `void` | `void do_thing() { ... }` | Void return type |

### Statements

| Statement | Example |
|-----------|---------|
| Variable declaration | `int x = 5;` |
| Expression statement | `x = x + 1;` |
| Return | `return x;` |
| If/else | `if (x > 0) { ... } else { ... }` |
| While loop | `while (i < n) { ... }` |
| For loop | `for (int i = 0; i < n; i = i + 1) { ... }` |
| Block | `{ int temp = x; x = y; y = temp; }` |

### Expressions

| Expression | Example |
|-----------|---------|
| Integer literal | `42`, `-1`, `0` |
| Character literal | `'A'`, `'0'` |
| Variable | `x`, `arr` |
| Binary operators | `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `&&`, `\|\|` |
| Unary operators | `-x`, `!flag`, `*ptr`, `&var` |
| Array index | `arr[i]` |
| Member access | `point.x` |
| Arrow access | `ptr->field` |
| Function call | `square(x)` |
| Assignment | `x = 5`, `arr[i] = val`, `ptr->field = val` |
| sizeof | `sizeof(int)`, `sizeof(struct Point)` |

### Built-in Functions

| Function | Signature | Notes |
|----------|-----------|-------|
| `malloc` | `malloc(size)` → pointer | Returns nullable pointer |
| `free` | `free(ptr)` → void | Must be heap pointer, not previously freed |
| `memcpy` | `memcpy(dst, src, len)` → void | Bounds checked against both buffers |

## Limitations

CCC compiles a **safe subset of C**, not full C. These are deliberate scope
boundaries, not bugs. If you hit one, the table below shows the workaround.

### Language features not supported

| You write | What happens | Write this instead |
|-----------|-------------|-------------------|
| `#include <stdio.h>` | Parse error: `Unexpected character '#'` | Remove — write self-contained programs |
| `printf("hello")` | Parse error (variadic) or undefined function | No I/O in the C subset |
| `"hello"` | Parse error (string literals) | Byte-by-byte: `msg[0] = 72; msg[1] = 101;` |
| `float x = 3.14;` | Parse error | Use `int` arithmetic only |
| `i++` or `i--` | Parse error: `Expected expression, found +` | `i = i + 1` or `i = i - 1` |
| `for (int i = 0; i < n; i++)` | Parse error (same `++` issue) | `for (int i = 0; i < n; i = i + 1)` |
| `a ? b : c` | Parse error | `if (a) { x = b; } else { x = c; }` |
| `(char)x` | Parse error (casts) | Assign directly: `char c = x;` |
| `do { ... } while (x);` | Parse error | `while (x) { ... }` |
| `break` | Emitter error: `unknown variable 'break'` | Restructure loop with flag variable |
| `continue` | Emitter error: `unknown variable 'continue'` | Restructure with if/else |
| `switch / case` | Parse error | Use if/else chain |
| `union`, `enum`, `goto` | Parse error | Not in the C subset |
| `void (*fp)(int)` | Parse error (function pointers) | Not supported |
| `typedef struct` | Parse error | Use `struct Name` directly |
| `(a, b)` | Parse error (comma operator) | Use separate statements |
| Global variables | Not supported | All state is local or heap-allocated |
| Multi-file (`#include "other.c"`) | Parse error | One `.c` file at a time |

### Verifier limitations

| Limitation | What it means | Severity |
|-----------|--------------|----------|
| No inter-procedural analysis | If function `cleanup(p)` calls `free(p)`, the caller won't know `p` was freed | **High** — only known false-negative pattern |
| No symbolic arithmetic | Can't prove `a + b < c` from separate bounds on `a` and `b` | Medium |
| Alias depth limit (8) | `p=q=r=s=t=u=v=w=x` — chains deeper than 8 may not track | Low — unrealistic in practice |
| No heap shape analysis | `s->ptr = p; free(s->ptr); *p` — aliasing through struct fields not tracked | Medium |

### Platform limitations

| Platform | Verify | Compile to binary |
|----------|--------|------------------|
| macOS (any arch) | ✓ Full | ✗ Verify-only (x86-64 asm can't link on ARM) |
| Linux x86-64 | ✓ Full | ✓ Full (`ccc input.c -o output`) |

## Writing Safe C for CCC

### Rule 1: Always null-check after malloc

```c
int *p = malloc(sizeof(int));
if (p == 0) { return -1; }   // required!
*p = 42;                       // now safe
```

### Rule 2: Bounds-check before array access in loops

```c
void process(int *data, int count, int capacity) {
    if (count > capacity) { return; }   // establish bound
    int i = 0;
    while (i < count) {
        data[i] = data[i] + 1;          // safe: i < count ≤ capacity
        i = i + 1;
    }
}
```

### Rule 3: Don't use pointers after free

```c
free(p);
// p = 0;     // good practice (not required by CCC)
// *p = 42;   // ← CCC will catch this
```

### Rule 4: Free heap memory exactly once

```c
int *p = malloc(sizeof(int));
if (p == 0) { return -1; }
*p = 42;
free(p);
// free(p);   // ← CCC will catch this (double free)
```

### Rule 5: Use sizeof for malloc

```c
struct Point *p = malloc(sizeof(struct Point));  // ✓ correct size
```

## Error Messages

CCC error messages include:

- **Line number** and **source context** (the offending line)
- **What went wrong** (violation type and details)
- **Which function** the error is in
- **How to fix it** (concrete suggestion)

Example:

```
Compiling my_program.c...

ERROR: Memory safety violation at line 12:
  total = total + g->scores[i];
  Cannot verify dynamic index is within bounds
  function: sum_grades
  Fix: Add or strengthen bounds checks before this access

1 memory safety violation(s) found. Compilation aborted.
```

## How It Works

CCC compiles in three phases:

```
Source (.c) → [Parser] → AST → [Verifier] → VerifiedProgram → [Emitter] → Assembly (.s)
```

1. **Parser** — Recursive-descent with Pratt precedence. Tokenizes then
   builds a deep-embedded AST (no string templates, ever).

2. **Verifier** — Flow-sensitive analysis that tracks:
   - Pointer states (uninitialized → nullable → checked-live → freed)
   - Array bounds (capacity vs index, static and dynamic)
   - Null checks (if/else branch analysis promotes nullable to live)
   - Alias relationships (pointer copies propagate freed state)
   - Symbol validity (function existence, arity matching)

3. **Emitter** — Generates x86-64 assembly from a deep-embedded x86 AST.
   The emitter **cannot accept unverified code** — `VerifiedProgram.mk` is
   a private constructor that requires a Lean proof that all safety checks passed.

## Building from Source

Requirements:
- Lean 4 toolchain (installed via `elan`; see setup section above)
- ~3 minutes to build on modern hardware

```bash
lake build ccc          # build the compiler
lake build              # build everything (including tests)
```

## Running Tests

```bash
# All 7 demo programs (5 reject, 2 accept)
lake env lean --run test/E2EAllDemos.lean

# All 24 holdout programs (6 accept, 18 reject)
lake env lean --run test/HoldoutTest.lean
```

## Public Repository Notes

This public mirror intentionally excludes internal directories:

- `claims/`
- `bugs/`
- `docs/bugs/`

## Project Structure

```
.
├── CCC/
│   ├── Syntax/          # AST, PtrState, Build helpers
│   ├── Parse/           # Tokenizer + recursive-descent parser
│   ├── Verify/          # Flow-sensitive safety verifier
│   ├── Emit/            # Deep-embedded x86-64 code generator
│   ├── Error/
│   ├── Contracts.lean   # VerifiedProgram (private mk)
│   └── Pipeline.lean    # parse → verify → emit
├── Main.lean            # CLI main
├── CCC.lean             # Root import
├── bin/ccc              # user-friendly wrapper
├── examples/            # demo C programs + run script
├── test/                # demo, holdout, regression tests
├── docs/containers/     # runtime/container validation docs
├── CHANGELOG.md
├── VERSION
├── lakefile.lean
└── lean-toolchain
```

## License

This project is licensed under the **Business Source License 1.1**.
See [`LICENSE`](./LICENSE).
