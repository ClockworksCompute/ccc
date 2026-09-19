# Changelog

All notable changes to CCC are documented in this file.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed
- A function marked `degraded` (uses `goto`/labels, or has a switch case that can fall through) now actually blocks `ccc` from exiting 0 — previously this status was computed but never checked anywhere; `--verify-report` said "verified" for such a function and a program with an unanalysed use-after-free across a `goto` back-edge could silently link. Pass `--allow-degraded` to opt back in. `--verify-report` and the success report now also print which function(s) are degraded and why.
- Struct layout now uses real C ABI alignment padding instead of packing fields with no padding at all. `struct P { char c; int x; long y; }` now sizes as 16 bytes at offsets 0/4/8 (confirmed to match `cc`'s own layout), not 13 bytes at 0/1/5. This was internally consistent for a CCC-only program but wrong the moment such a struct's memory is shared with real C code — the scenario the whole project is working toward. Shared between both emitters via the new `CCC.Syntax.Layout` module. Union sizing is still a known gap (unchanged, tracked separately).
- `sizeof(expr)` (as opposed to `sizeof(type)`) previously discarded the parsed expression entirely and approximated its size as `sizeof(int)` regardless of what the expression actually was. Now resolves the operand's real inferred type (`long` → 8, `char` → 1, a struct field → its own type's size, etc.) via a new `Expr.sizeOfExpr` AST node. The operand is correctly never evaluated for safety-checking purposes (matching C semantics: `sizeof(*null_ptr)` is well-defined and is not a null-pointer dereference).

- Calls with more than 8 arguments (and function DEFINITIONS with more than 8 parameters) used to throw "too many arguments" at the call site, and — separately and more seriously — silently drop the 9th+ parameter's spill code entirely at the definition site, leaving its local variable slot as uninitialized stack garbage. Implemented AAPCS64's stack-argument passing for both directions. Getting this conformant to the REAL ABI (as opposed to merely self-consistent) needed two rounds, both driven by tests that link CCC-compiled code against real `cc`-compiled code rather than only against itself: Apple's arm64 ABI packs each stack argument at its own natural size (not padded to a uniform 8 bytes, unlike the base AAPCS64 spec), and stack-argument sizing must come from the callee's *declared* parameter type when a prototype is visible, not from the caller expression's inferred type (a bare integer literal infers as `.long` elsewhere in this codebase, which is harmless for register-passed arguments but wrong for packing).

- A top-level `int table[8];` (with or without a brace initializer) used to vanish from the compiled program entirely — the parser branch for global array declarations never registered the symbol at all, not merely its initial values. Real C code (lookup tables, CRC tables, coefficient tables) relies on this pattern heavily. Now registers a real `.array` global with its actual size, and a brace initializer's element values are kept and emitted to a proper `.data` section, width-correct per element type (`char`=1 byte, `short`=2, `int`=4, `long`=8) with C's zero-padding rule for elements the initializer list doesn't provide. Cross-checked directly against `cc` compiling the identical source.

### Added
- `test/StructLayoutTest.lean` (10 cases) for the struct-alignment and `sizeof(expr)` fixes above.
- `test/StackArgsTest.lean` (6 cases) for the stack-argument fix, including three that link CCC-compiled code against real `cc` output on one side of the call.
- `test/GlobalArrayTest.lean` (7 cases) for the global array fix, including one cross-checked directly against `cc`.

## [0.2.0] - 2026-09-19

### Fixed
- **Force-emit removed.** `ccc program.c -o out` no longer assembles and links a program the verifier rejected. Previously the CLI printed "Compilation aborted" and still produced a working, exit-0 binary. The escape hatch (`CCC.compileIgnoringViolations`) is now explicit and only reachable via `--harden`.
- Verifier no longer drops violations found inside an if-branch that ends in `return`.
- Array/pointer bound facts are now invalidated on assignment, increment, and field writes instead of surviving reassignment.
- `while`/`for`/`do-while` loop bodies are now analyzed to a bounded fixpoint (3 rounds) instead of a single pass, so a use-after-free that only appears on the second iteration is caught. Functions containing `goto`/labels are now marked `degraded` (surfacing this status end-to-end is tracked separately).
- Any pointer dereference whose base cannot be resolved to a tracked variable or struct field (pointer arithmetic, an unresolved call result, a double dereference) is now a "cannot verify" violation instead of a silent accept; dereferencing an `uninitialized` pointer is now also caught.
- Bounds checking now covers `strcpy`/`strcat`/`sprintf`/`gets`/`memset`/`memmove`/`strncpy`/`snprintf`, not just `memcpy`.
- `malloc`/`calloc`/`realloc`/`strdup`/`aligned_alloc` calls whose size does not resolve to a compile-time constant are now tracked as live (nullable) pointers instead of falling back to `uninitialized`, removing a class of false "invalid free" reports.
- A first cut of interprocedural free-tracking: `release(p); *p = 1;` is now caught even though `free` is called inside `release`, not at the call site.
- False positives fixed: `if (!p)` / `if (p)` idioms, `p == NULL` / `p != NULL` (both the `NULL` macro and the literal), `switch` statements with `break`-terminated cases, `*s.p` (a parser precedence bug: unary prefix operators were binding tighter than postfix `.`/`->`/`[]`, so `*p->field` parsed as `(*p)->field`).
- AArch64 emitter: signed `int`/`short`/`char` values are now sign-extended on load instead of zero-extended, fixing miscompilation of negative values, signed division/modulo/comparison, and 32-bit `int` overflow wraparound. Unsigned comparison/shift/division now use the unsigned instruction forms. A related bug in `resolveType` not stripping `const`/`volatile`/`restrict` before typedef resolution (corrupting the indexing stride of any qualified typedef'd pointer, e.g. `const uint8_t *`) was found and fixed while building `--harden`.
- `test/regression/StructArrayRepro.lean` now assembles, links, and runs the compiled program to check its exit code, instead of pattern-matching x86-64 assembly text against a pipeline that now emits AArch64 by default.

### Added
- `ccc --harden`: an experimental, explicitly opt-in flag that emits a binary even when the verifier could not clear every access, inserting a real runtime bounds check (via a new allocation-size registry in `runtime/ccc_runtime.c`) before every array/pointer subscript whose base is exactly a tracked `malloc`/`calloc` pointer value. Coverage is intentionally narrow (see `ccc --harden` usage text and `Main.lean`) — pointer arithmetic, struct field access, and bare dereference are not yet covered.
- `division`/`modulo` by a value that cannot be proven nonzero is now a reported violation (`noDivByZero`).
- A CVE regression corpus (`test/corpus/`) with real, AddressSanitizer-verified `vulnerable.c`/`fixed.c` pairs for the libheif overlay heap overflow (the bug behind the hacktron.ai "Hacking OpenAI" report), libwebp CVE-2023-4863, and libpng CVE-2015-8126/CVE-2018-13785, plus a `scripts/corpus.sh` scoreboard wired into CI (`.github/workflows/ci.yml`).
- `must-reject/` convention for corpus entries: a set of known-overflowing mutants that an entry must also reject to be scored `detected`. Seeded for the libheif entry after a scoped relational-analysis mechanism was found to accept several of them (see `docs/corpus-results.md`'s "fourth update" and the FEL-64 ticket) — that mechanism now always reports the pattern it recognizes as unprovable rather than accepting it.
- `test/SignednessTest.lean` (8 cases), `test/VerifierFixesTest.lean` (22 cases), `test/HardenTest.lean` (5 cases).

### Changed
- Parser: `typedef struct NAME { ... } NAME;` now actually parses the field list (previously skipped entirely, so any use of such a struct's fields failed with "unknown field").

## [0.1.2] - 2026-02-25

### Fixed
- AArch64 emitter: `emitLoadLocal`/`emitStoreLocal` now use scratch register `x9` for frame offsets exceeding the unscaled addressing range (|offset| > 255). Fixes assembler errors on programs with large stack frames (e.g. `safe_server.c`).
- `examples/run` script now detects violations via output content instead of exit code, fixing incorrect ACCEPTED labels on rejected programs.

### Removed
- Removed `test/HoldoutTest.lean` (referenced private `../factory/` directory not in public mirror).
- Removed Lua test files (`LuaParseTest`, `LuaScoreTest`, `LuaSingleTest`) that depended on external `/tmp/lua-5.4.7/` sources.
- Removed `OBSERVATION.md` internal development log.
- Removed `changes/` internal schema-change protocol directory.
- Removed `torture/` GCC torture test scaffolding (no actual test content).
- Removed private path references from `CCC/Contracts.lean` and `scripts/runtime/linux_validate.sh`.
- Removed README references to Lua parse-parity and holdout test suites not included in the public repository.
- Replaced internal bug tracker IDs in docs with descriptive text.

## [0.1.1] - 2026-02-18

### Fixed
- Corrected stack slot base offset assignment in `EmitX86.assignOffsets` so local struct/object slots are based at the lowest address in their reserved region.
- Prevented field-address computation from extending above `%rbp` into caller-frame memory for larger local structs.
- Fixed `scripts/runtime/linux_validate.sh` Lean runner path to avoid `String.Slice`/`String` mismatch issues on Lean 4.27.

### Validation
- Revalidated Linux x86-64 runtime flow (`trivial`, `fibonacci`, `heartbleed_fixed`, `safe_server`) via containerized runtime checks.

## [0.1.0] - 2026-02-18

### Added
- Initial public release of the CCC compiler.
- Lean 4 parser for the supported C subset.
- Flow-sensitive memory-safety verifier (null checks, bounds checks, alias tracking, pointer lifetime checks).
- x86-64 emitter and end-to-end compile pipeline.
- Demo and holdout test suites.
- `bin/ccc` wrapper and `examples/run` one-command demo.
- Public BUSL-1.1 licensing and release packaging workflow.
