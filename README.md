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

Add a bounds check — the same fix that would have prevented Heartbleed —
and CCC accepts it:

```
$ ccc examples/07_heartbleed_fixed.c

  ✓ 1 functions analyzed
  ✓ 21 pointer operations verified
  ✓ 8 array accesses verified (7 static, 1 runtime-bounded)
  ✓ 0 memory safety violations
  ✓ Verified: 07_heartbleed_fixed (assembly generated)
```

There are 7 example programs in [`examples/`](./examples).

## Quick Start

```bash
# Install Lean 4 (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# Build
lake build ccc

# Run all 7 examples — CCC accepts the safe ones, rejects the buggy ones
./examples/run

# Compile a verified program to a native binary
./.lake/build/bin/ccc test/demo/safe_server.c -o /tmp/safe_server
```

`lake` fetches the exact Lean version pinned in `lean-toolchain` automatically.

## Why Lean 4?

Lean is a dependently-typed programming language, best known as a theorem
prover. CCC uses it as a systems programming language — but the type system
gives us one property that would be hard to enforce in C++ or Rust:

```lean
-- The emitter only accepts VerifiedProgram, which has a private constructor.
-- You can't create one without a proof that the verifier passed.

structure VerifiedProgram where
  private mk ::
  program  : Syntax.Program
  evidence : Syntax.ProgramVerifyResult

def mkVerified (prog    : Syntax.Program)
               (evidence : Syntax.ProgramVerifyResult)
               (_h      : evidence.isSafe = true)       -- proof required
    : VerifiedProgram := { program := prog, evidence := evidence }

def emitProgram (vprog : VerifiedProgram) : Except String String := ...
```

Where does the proof come from? It falls out of a normal `if` check — no
manual proof writing, no tactic blocks:

```lean
def verifyProgram (prog : Syntax.Program) : ... := do
  let report := Verify.verifyProgramReport prog
  if h : report.isSafe then                -- `h` is now a proof that isSafe = true
    return mkVerified prog report h        -- proof passed to constructor
  else
    throw report.allViolations             -- no VerifiedProgram possible here
```

`if h : expr then` is Lean's *dependent if*. When `expr` evaluates to `true`
at runtime, `h` becomes a compile-time proof of `expr = true` in the `then`
branch. So the runtime boolean check **is** the proof — the type checker
just tracks it through the control flow. Any code path that tries to call
`emitProgram` without going through this branch won't type-check.

The rest of the compiler is ordinary functional programming: pattern matching,
monads, recursive descent. The dependent types only show up at this one
critical boundary.

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

**Not yet supported:** `union` types are parsed but sized as 0 bytes.
`float`/`double` arithmetic parses and emits, but every float literal and
operation currently computes as `0` — this does not panic, it silently
produces the wrong answer, so don't rely on floating point yet.
Function pointers work for the common patterns — a callback parameter
called by name, an explicit `(*fp)(...)` call, a global holding a
function pointer, an array-of-function-pointers dispatch table — see
`test/FuncPtrTest.lean`. `--target x86_64` is parsed but not wired up;
the x86-64 emitter (`EmitX86`) exists in tree but is unverified and has
its own, separate 8-argument call limit. This
is a proof-of-concept — the test suites define the validated surface,
and the gaps above are tracked as the "emitter completeness" work in
the project's Linear tracker.

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
lake env lean --run test/SignednessTest.lean       #  8/8  — signed int/short/char codegen
lake env lean --run test/Phase2Features.lean       # 37/37 — language features
lake env lean --run test/PreprocessTest.lean       # 14/14 — preprocessor
lake env lean --run test/TypedefTest.lean          # 10/10 — typedef resolution
lake env lean --run test/VerifierAccuracyTest.lean # 10/10 — false-positive guard
lake env lean --run test/VerifierFixesTest.lean    # 28/28 — verifier soundness/precision regressions
lake env lean --run test/HardenTest.lean           #  5/5  — --harden runtime bounds checks
lake env lean --run test/StructLayoutTest.lean     # 10/10 — struct alignment, sizeof(expr)
lake env lean --run test/StackArgsTest.lean        #  6/6  — AAPCS64 stack args (>8 params)
lake env lean --run test/GlobalArrayTest.lean      # 10/10 — global array declarations/initializers
lake env lean --run test/EnumResolveTest.lean      # 11/11 — enum constant resolution
lake env lean --run test/FuncPtrTest.lean          # 10/10 — function pointers / indirect calls
lake env lean --run test/JsonReportTest.lean       #  4/4  — --report=json structured output
lake env lean --run test/E2EAllDemos.lean          # demo programs

bash test/regression/run_regressions.sh             # numbered CCC-BUG-NNN repros
bash test/run_demos.sh                               # gate script: 7 demos, verify accept/reject
scripts/corpus.sh                                    # CVE corpus scoreboard (see below)
```

### CVE corpus

`test/corpus/` is a small, growing regression corpus of real-world CVE
shapes (libheif's overlay heap overflow behind the hacktron.ai "Hacking
OpenAI" writeup, libwebp CVE-2023-4863, libpng CVE-2015-8126 and
CVE-2018-13785), each ported to standalone C with a `vulnerable.c` /
`fixed.c` pair and verified independently to actually crash under
AddressSanitizer pre-fix and run clean post-fix. `scripts/corpus.sh` runs
`ccc` against every entry and prints a `detected` / `missed` /
`false-positive` / `parse-failed` / `timeout` scoreboard; run it any time
with:

```bash
lake build ccc
scripts/corpus.sh
```

Baseline status (see [`docs/corpus-results.md`](./docs/corpus-results.md)
for the full writeup): **0 of 4 entries detected.** `libwebp-cve-2023-4863`
is **missed** — `ccc` accepts the vulnerable version outright, since the
verifier does not yet track integer overflow. The other three
(`libheif-overlay-85e21ad`, `libpng-cve-2015-8126`, `libpng-cve-2018-13785`)
are **false-positive** — `ccc` rejects the vulnerable version, but rejects
the fixed version identically, unable to relate a runtime clamp/bounds
check to the buffer it protects. This is not a typo or an oversight — the
corpus exists precisely to make that number improve (or regress)
measurably as the verifier changes, not to claim it's already good.

An earlier version of this scoreboard briefly showed `libheif-overlay-85e21ad`
as "detected", via a scoped heuristic that reasoned over unbounded
integers. Six one-to-three-line mutations of the fixed source that
reintroduce a real, AddressSanitizer-confirmed heap overflow were all
still accepted by that heuristic with 0 violations, so it was removed
rather than shipped as a false sense of soundness — see
`test/corpus/libheif-overlay-85e21ad/must-reject/` for those mutants
(every corpus entry marked "detected" must also reject everything under
its own `must-reject/` directory, which `scripts/corpus.sh` now checks)
and the "libheif overlay" write-up in `docs/corpus-results.md` for the
full account.

### Mutation fuzzer (FEL-69)

The six libheif `must-reject/` mutants above were found by hand — each a
1-3 line edit, each fooling the verifier at the time. `scripts/mutation_fuzz.py`
makes that a machine's job for one mutation class so far: for every
corpus entry's `fixed.c`, it generates every single-comparison-operator
flip (`<` &harr; `<=`, `>` &harr; `>=`, one flip per mutant) and runs a
differential oracle on each — `cc -fsanitize=address -fsanitize=undefined`
as ground truth, `ccc` (verify-only) as the candidate. A mutant the
sanitizer flags as broken but `ccc` still ACCEPTS is a genuine soundness
bug: it's auto-filed into that entry's `must-reject/NNN_autofuzz_*.c` with
a header recording the exact mutation, so `scripts/corpus.sh` picks it up
on the next run. Run it any time with:

```bash
lake build ccc
python3 scripts/mutation_fuzz.py
```

Like `scripts/corpus.sh`, this is a measurement, not a gate — it always
exits 0, but prints a `::warning::` (visible in the CI job summary) when
it files a new must-reject case, since that's a genuinely new finding
worth a human's attention rather than an already-known scoreboard number.
Runs in well under a minute against the current 4-entry corpus. Only the
comparison-operator-flip class is implemented — the rest of FEL-69's
mutation catalogue (delete a guard, narrow a cast, ±1/×2 a literal, swap
statements, a second smaller call site, reassign a size variable) needs
real C-aware transformations a token-regex mutator can't do safely, and
is tracked as follow-up work under that same ticket.

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
