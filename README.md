# CCC — Clockworks C Compiler

CCC is a Lean 4 C frontend/compiler with built-in static safety analysis.

It runs a full pipeline:

```
source.c → preprocess → parse → verify → emit assembly → (optional) as/cc link
```

The verifier produces per-function status (`verified`, `degraded`, `exempt`) and
detailed violations. The compiler can still emit assembly in degraded paths so
integration/program-compatibility work can continue while safety gaps are visible.

## Versioning and Changelog

- Version source of truth: [`VERSION`](./VERSION)
- Current release: `v0.1.1`
- Release notes: [`CHANGELOG.md`](./CHANGELOG.md)

## Setup (if Lean is not installed)

CCC uses the Lean 4 toolchain (`lean` + `lake`). Install once with
[`elan`](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

lean --version
lake --version
```

`lake` will automatically fetch the exact Lean version pinned in
`lean-toolchain`.

## Quick Start

```bash
lake build ccc

# 1) Verification status report (no assembly needed)
./.lake/build/bin/ccc --verify-report test/demo/safe_server.c

# 2) Compile to assembly only
./.lake/build/bin/ccc -c test/demo/heartbleed_fixed.c -o /tmp/heartbleed_fixed.s

# 3) Compile + assemble + link (requires as + cc/gcc)
./.lake/build/bin/ccc test/demo/safe_server.c -o /tmp/safe_server
/tmp/safe_server; echo $?
```

## CLI Modes

```text
ccc <input.c> [-o <output>]
ccc -c <input.c> -o <output.s>
ccc --verify-report <input.c>
```

- `--verify-report`: prints per-function verification status lines.
- `-c`: emits assembly only.
- `-o` without `-c`: emits, assembles, and links a binary.
- no `-o`: verify-only run (prints report).

## What CCC Can Do Today (validated)

These are from the current test suites in `ccc/test`:

- **Phase-2 feature acceptance:** `37/37` (`test/Phase2Features.lean`)
- **Preprocessor:** `14/14` (`test/PreprocessTest.lean`)
- **Typedef resolution:** `10/10` (`test/TypedefTest.lean`)
- **Integration programs:** `22/22` (`test/IntegrationTest.lean`)
- **AArch64 backend execution:** `34/34` (`test/AArch64Test.lean`)
- **Lua 5.4 parse parity:** `34/34 files` (`test/LuaScoreTest.lean`)
- **Emitter hardening:** `8/8` (`test/HardeningTest.lean`)
- **Holdout suite:** `24/24` (`test/HoldoutTest.lean`)
- **Verifier false-positive guard:** `10/10` (`test/VerifierAccuracyTest.lean`)

## Safety Analysis

CCC tracks and reports memory-safety classes including:

- buffer bounds
- use-after-free
- double free
- null dereference

Use `--verify-report` to get a compact per-function view, e.g.:

```text
main: degraded (2 violations: bounds at line 15, bounds at line 15)
```

### Important behavior: verified vs degraded

CCC currently supports **force-emit** paths for integration work:

- verified programs: no violations, standard success report
- degraded programs: violations are reported, assembly may still be emitted

So treat verifier output (status + violations) as the safety signal, not only
process exit code.

## Language Coverage Snapshot

The current parser/emitter pipeline handles broad C syntax used by the test and
integration suites, including:

- control flow: `if/else`, `for`, `while`, `do-while`, `switch`, `break`, `continue`, `goto`
- expressions: ternary, bitwise ops, shifts, compound assignment, pre/post inc-dec
- declarations: typedefs, enums, unions, qualifiers, storage-class forms, multi-decls
- pointers/structs: address/deref, `.` and `->`, struct/array access patterns
- preprocessing: `#include`, macro define/undef, conditionals, include guards

## Architecture / Backend Status

- Primary emitted backend in current pipeline: **AArch64** (`EmitAArch64`),
  with end-to-end execution tests.
- **x86-64 emitter** exists (`EmitX86`) and remains in tree.
- `Backend/{X86_64,AArch64,RISCV,X86_32}` module trees exist as architecture
  scaffolding for ongoing backend work.

## Running Tests

```bash
# Core compiler build
lake build ccc

# Safety + compatibility suites
lake env lean --run test/E2EAllDemos.lean
lake env lean --run test/HoldoutTest.lean
lake env lean --run test/Phase2Features.lean
lake env lean --run test/PreprocessTest.lean
lake env lean --run test/TypedefTest.lean
lake env lean --run test/VerifierAccuracyTest.lean

# Backend + integration suites
lake env lean --run test/AArch64Test.lean
lake env lean --run test/IntegrationTest.lean
lake env lean --run test/HardeningTest.lean

# Lua parse parity gate (expects Lua source in /tmp/lua-5.4.7/src)
lake env lean --run test/LuaScoreTest.lean
```

## Public Repository Notes

This public mirror intentionally excludes internal directories:

- `claims/`
- `bugs/`
- `docs/bugs/`

## Project Structure

```text
.
├── CCC/
│   ├── Parse/           # lexer + parser
│   ├── Preprocess/      # preprocessor
│   ├── Verify/          # verifier and safety reporting
│   ├── Emit/            # code emitters (AArch64, x86)
│   ├── IR/              # intermediate representation scaffolding
│   ├── Features/        # per-feature parse/verify/lower/test scaffolding
│   ├── Backend/         # per-arch backend scaffolding
│   ├── Contracts.lean
│   └── Pipeline.lean
├── Main.lean            # CLI entry
├── test/                # integration, backend, holdout, regression suites
├── examples/            # demo programs
├── CHANGELOG.md
├── VERSION
├── lakefile.lean
└── lean-toolchain
```

## License

This project is licensed under the **Business Source License 1.1**.
See [`LICENSE`](./LICENSE).
