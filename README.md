# CCC — Clockworks C Compiler

A proof-of-concept C compiler written entirely in
[Lean 4](https://lean-lang.org/), with a built-in memory-safety verifier.
The compiler catches buffer overflows, use-after-free, double free, and null
dereference bugs at compile time — and Lean's type system guarantees that
**no assembly is ever emitted for an unverified program**.

## CCC catching a Heartbleed-class bug

The [Heartbleed vulnerability](https://en.wikipedia.org/wiki/Heartbleed)
(CVE-2014-0160) leaked passwords and private keys from 17% of the internet's
servers. The root cause was a `memcpy` with an attacker-controlled, unchecked
length. CCC catches this pattern at compile time:

```c
// examples/06_heartbleed.c (simplified)
memcpy(response, req->payload, req->payload_length);
//     ^^^^^^^^               ^^^^^^^^^^^^^^^^^^^^
//     64-byte buffer          attacker-controlled, never bounds-checked
```

```
$ ccc examples/06_heartbleed.c

ERROR: Memory safety violation at line 30:
  memcpy(response, req->payload, req->payload_length);
  Cannot verify memcpy length against buffers (dst=64, src=64)
  Fix: Prove len is bounded by both source and destination buffer sizes

1 memory safety violation(s) found. Compilation aborted.
```

Add a bounds check — the same one-line fix that would have prevented
Heartbleed — and CCC accepts it:

```
$ ccc examples/07_heartbleed_fixed.c

  ✓ 1 functions analyzed
  ✓ 21 pointer operations verified
  ✓ 8 array accesses verified (7 static, 1 runtime-bounded)
  ✓ 0 memory safety violations
  ✓ Verified: 07_heartbleed_fixed (assembly generated)
```

There are 7 example programs in [`examples/`](./examples). Run them all with
`./examples/run`.

## Quick Start

```bash
# Install Lean 4 (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# Build
lake build ccc

# Try it — verify a program, compile it, run it
./.lake/build/bin/ccc test/demo/safe_server.c -o /tmp/safe_server
/tmp/safe_server
```

`lake` fetches the exact Lean version pinned in `lean-toolchain` automatically.

## Why Lean 4?

Lean is a dependently-typed programming language, best known as a theorem
prover. CCC uses it as a systems programming language — but the type system
gives us one property that would be hard to enforce in C++ or Rust:

```lean
-- CCC/Contracts.lean

structure VerifiedProgram where
  private mk ::                              -- private constructor
  program  : Syntax.Program
  evidence : Syntax.ProgramVerifyResult

def mkVerified (prog : Syntax.Program)
    (evidence : Syntax.ProgramVerifyResult)
    (_h : evidence.isSafe = true)            -- proof obligation
    : VerifiedProgram := ...

def emitProgram (vprog : VerifiedProgram)    -- only accepts VerifiedProgram
    : Except String String := ...
```

`VerifiedProgram` has a **private constructor**. The only way to create one is
through `mkVerified`, which requires a **proof term** that `evidence.isSafe =
true`. The emitter's type signature only accepts `VerifiedProgram`. This means
the Lean compiler itself statically rejects any code path where assembly could
be emitted for an unverified program — not by convention, not by runtime
assertion, but by the type checker.

The rest of the compiler is ordinary functional programming: pattern matching,
monads, recursive descent. Lean 4 compiles to native C and is fast enough to
build real compilers.

## What it checks

CCC runs a flow-sensitive, per-function safety analysis over the parsed AST.
It currently tracks four memory-safety properties:

| Property | Example |
|----------|---------|
| **Buffer bounds** | `data[i]` where `i` may exceed capacity |
| **Use-after-free** | dereference after `free()` |
| **Double free** | calling `free()` twice on the same pointer |
| **Null dereference** | dereference without a null-guard |

The verifier reports per-function status (`verified` / `degraded` / `exempt`)
and pinpoints each violation with source line, explanation, and suggested fix.

## CLI

```
ccc <input.c>                          # verify only (prints report)
ccc <input.c> -o <output>              # verify + emit + assemble + link
ccc -c <input.c> -o <output.s>         # verify + emit assembly only
ccc --verify-report <input.c>          # compact per-function status
```

## Language coverage

The parser and emitter handle a practical subset of C, validated by the test
suites:

- **Control flow:** `if`/`else`, `for`, `while`, `do-while`, `switch`,
  `break`, `continue`, `goto`
- **Expressions:** ternary, bitwise ops, shifts, compound assignment,
  pre/post increment/decrement
- **Declarations:** typedefs, enums, structs, qualifiers, storage-class
  specifiers, multi-declarators
- **Pointers/structs:** address-of, dereference, `.` and `->`, array access
- **Preprocessor:** `#include`, `#define`/`#undef`, `#ifdef`/`#ifndef`/`#if`,
  include guards

**Not yet supported:** `union` types, `float`/`double` arithmetic, variadic
functions, and function pointers are parsed but will panic at codegen. This is
a proof-of-concept — the test suites define the validated surface.

## Backend

The primary backend is **AArch64** (Apple Silicon), with 34 end-to-end
execution tests that compile C to assembly, assemble, link, run, and check
exit codes. An x86-64 emitter (`EmitX86`) also exists in tree.

## Tests

```bash
lake build ccc

lake env lean --run test/AArch64Test.lean         # 34/34 — backend execution
lake env lean --run test/IntegrationTest.lean      # 22/22 — E2E programs
lake env lean --run test/HardeningTest.lean        #  8/8  — edge cases
lake env lean --run test/Phase2Features.lean       # 37/37 — language features
lake env lean --run test/PreprocessTest.lean       # 14/14 — preprocessor
lake env lean --run test/TypedefTest.lean          # 10/10 — typedef resolution
lake env lean --run test/VerifierAccuracyTest.lean # 10/10 — false-positive guard
lake env lean --run test/E2EAllDemos.lean          # demo programs
```

## Project structure

```
CCC/
├── Parse/          # lexer + recursive-descent parser
├── Preprocess/     # C preprocessor
├── Verify/         # flow-sensitive safety verifier
├── Emit/           # code emitters (AArch64, x86-64)
├── Contracts.lean  # VerifiedProgram type + pipeline contracts
└── Pipeline.lean   # top-level compile orchestration
Main.lean           # CLI entry point
test/               # all test suites
examples/           # 7 demo C programs with ./examples/run
```

## Version

Current release: **v0.1.2** — see [`CHANGELOG.md`](./CHANGELOG.md).

## License

[Business Source License 1.1](./LICENSE)
