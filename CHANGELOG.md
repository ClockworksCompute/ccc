# Changelog

All notable changes to CCC are documented in this file.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed
- A fixed-capacity array (or struct-field array) indexed inside a loop bounded by an ordinary, unbounded parameter (`void fill(int arr[10], int n) { for (i=0;i<n;i++) arr[i]=i; }`) was silently accepted with a `runtime-bounded` verdict and zero violations — confirmed with `cc -fsanitize=address` to genuinely overflow. Root cause: the loop-fixpoint analysis's bounded-fuel warm-up loop had no widening step, so a loop counter's carried-forward range just grew by the step's fixed increment each round and froze at whatever value it reached when fuel ran out, instead of correctly recognizing non-convergence and treating the bound as unknown. Fixed with a standard abstract-interpretation widening operator; an ordinary loop bounded by a literal (or otherwise independently-known value) is completely unaffected, since that case is already re-derived fresh from the condition every iteration. This is the first genuinely new corpus detection since the FEL-64 unsound heuristic was removed — `libpng-cve-2015-8126` (CVE-2015-8126) now scores `detected` rather than `missed`, verified against its own `must-reject/` mutants and both fuzzers.
- A division whose divisor is a variable initialized to a sum that unconditionally includes `+ 1` (`size_t row_factor = (size_t)width * (size_t)channels * (bit_depth>8?2:1) + 1 + (interlaced?6:0);`, libpng's own CVE-2018-13785 fix) was flagged as an unconditional "cannot verify the division divisor is nonzero" false positive, since `width`/`channels`/etc. are runtime parameters and the whole expression can never constant-fold. Fixed by recognizing C's own "usual arithmetic conversions": a multiplication is trusted to be free of realistic 32-bit wraparound only when at least one operand is already explicitly widened to 64 bits, matching the real fix's own pattern — the identical shape computed in native 32-bit arithmetic (the actual vulnerable code, which really does wrap `row_factor` to exactly zero) is deliberately still rejected. A first version of this fix, which trusted the sum based on type (unsigned) alone with no regard for wraparound, was caught as unsound before shipping by testing it against the vulnerable version, not just the fixed one — it would have silently accepted the real bug too. `libpng-cve-2018-13785` (CVE-2018-13785) now scores `detected` rather than `false-positive`.
- A top-level construct the parser could not parse (an unsupported keyword, an unrecognized declaration shape, etc.) was silently DROPPED with zero trace anywhere — not in the parsed program, not in any report, not even a count — via the parser's own `skipToTopLevel` error-recovery. A file with 3 unparseable functions out of 10 would produce a report only about the other 7, with nothing distinguishing that from a file that genuinely only had 7 functions. Every report mode (the default compile path, `--verify-report`, `--report=json`) now surfaces exactly what was skipped and where; the default compile path refuses to proceed (matching the existing `degraded`/`exempt` gate) unless `--allow-degraded` is passed.
- FEL-45 (reopened): a memcpy-shaped sink whose destination (or, for the two-buffer sinks, source) byte size could not be determined statically — most commonly a bare pointer parameter, e.g. `void copy(char *dst, char *src, int n) { memcpy(dst, src, n); }` — silently passed with 0 violations instead of reporting "cannot verify", exactly as dangerous as an unmodelled sink. Also added `fread`/`read`/`recv`/`fgets`/`vsnprintf` to the checked-sink table (same destination+length shape as `memset`/`strncpy`/`snprintf`), and `strncat`, which is always flagged since its destination needs room for its *existing* content plus `n+1` bytes — a quantity this verifier does not track at all — so there is no sound way to accept it.
- FEL-52: an active `#error` directive silently became a harmless comment (`/* CCC #error: ... */`) instead of failing preprocessing, so a file that hit an unsupported-configuration guard (extremely common in real headers) "preprocessed" successfully and the verifier reported on whatever nonsense followed it. Now genuinely fails compilation with the error message surfaced, matching real C preprocessor semantics; an `#error` inside an untaken `#if 0` branch correctly remains a no-op.

### Added
- 7 new cases in `test/VerifierFixesTest.lean` (now 38) for the two fixes above, including a regression guard confirming a literal-bounded loop still verifies clean, and an adversarial pair distinguishing an explicitly-widened sum (trusted) from the identical narrow-arithmetic shape (correctly still rejected).
- `SafetyViolation` gains an optional structured `witness` field (a real `capacity`/`requiredLessThan`/`op` value, not just prose embedded in `message`) for buffer-bounds and div-by-zero violations, exposed as a `witness` object in `--report=json` — first slice of the structured-report work; other violation properties still carry `witness: null`, same as before. 3 new cases in `test/JsonReportTest.lean` (now 8).
- `Program` gains a `parseWarnings` field naming every skipped top-level construct, threaded through the CLI's degraded/exempt gate and both report modes. `test/regression/ParseSkipGateRepro.lean` (5 checks) exercises the actual CLI binary end-to-end, matching `DegradedGateRepro.lean`'s pattern.
- 8 new cases in `test/VerifierFixesTest.lean` (now 46) for the FEL-45 sink-table fixes above, including a regression guard confirming a fully statically-sized `memcpy` within bounds still verifies clean.
- `scripts/generated_fuzz.py` (FEL-69 item 3): every well-defined-behavior generated instance (ccc accepts it, the sanitizer run doesn't crash) is now also compiled with ccc's real emitter and run, comparing its exit code against the sanitizer binary's — an emitter differential, extending `SignednessTest`'s CCC-vs-`cc` comparison method to random programs, the way the FEL-50 signed-load bug class would have been found automatically. Reported as a separate `EMITTER_MISMATCH`/`emitter_inconsistent` bucket, distinct from the existing soundness-bug bucket. 150+ instances run locally across two seeds found zero emitter differentials; the detection path itself was sanity-checked against a deliberately-forced mismatch to confirm it actually fires.
- `test/regression/PreprocessErrorRepro.lean` (2 checks) for the `#error` fix above: an active `#error` fails compilation with the message surfaced, and one inside an untaken `#if 0` branch correctly does not fire.

## [0.3.0] - 2026-09-19

### Fixed
- A function marked `degraded` (uses `goto`/labels, or has a switch case that can fall through) now actually blocks `ccc` from exiting 0 — previously this status was computed but never checked anywhere; `--verify-report` said "verified" for such a function and a program with an unanalysed use-after-free across a `goto` back-edge could silently link. Pass `--allow-degraded` to opt back in. `--verify-report` and the success report now also print which function(s) are degraded and why.
- Struct layout now uses real C ABI alignment padding instead of packing fields with no padding at all. `struct P { char c; int x; long y; }` now sizes as 16 bytes at offsets 0/4/8 (confirmed to match `cc`'s own layout), not 13 bytes at 0/1/5. This was internally consistent for a CCC-only program but wrong the moment such a struct's memory is shared with real C code — the scenario the whole project is working toward. Shared between both emitters via the new `CCC.Syntax.Layout` module. Union sizing is still a known gap (unchanged, tracked separately).
- `sizeof(expr)` (as opposed to `sizeof(type)`) previously discarded the parsed expression entirely and approximated its size as `sizeof(int)` regardless of what the expression actually was. Now resolves the operand's real inferred type (`long` → 8, `char` → 1, a struct field → its own type's size, etc.) via a new `Expr.sizeOfExpr` AST node. The operand is correctly never evaluated for safety-checking purposes (matching C semantics: `sizeof(*null_ptr)` is well-defined and is not a null-pointer dereference).

- Calls with more than 8 arguments (and function DEFINITIONS with more than 8 parameters) used to throw "too many arguments" at the call site, and — separately and more seriously — silently drop the 9th+ parameter's spill code entirely at the definition site, leaving its local variable slot as uninitialized stack garbage. Implemented AAPCS64's stack-argument passing for both directions. Getting this conformant to the REAL ABI (as opposed to merely self-consistent) needed two rounds, both driven by tests that link CCC-compiled code against real `cc`-compiled code rather than only against itself: Apple's arm64 ABI packs each stack argument at its own natural size (not padded to a uniform 8 bytes, unlike the base AAPCS64 spec), and stack-argument sizing must come from the callee's *declared* parameter type when a prototype is visible, not from the caller expression's inferred type (a bare integer literal infers as `.long` elsewhere in this codebase, which is harmless for register-passed arguments but wrong for packing).

- A top-level `int table[8];` (with or without a brace initializer) used to vanish from the compiled program entirely — the parser branch for global array declarations never registered the symbol at all, not merely its initial values. Real C code (lookup tables, CRC tables, coefficient tables) relies on this pattern heavily. Now registers a real `.array` global with its actual size, and a brace initializer's element values are kept and emitted to a proper `.data` section, width-correct per element type (`char`=1 byte, `short`=2, `int`=4, `long`=8) with C's zero-padding rule for elements the initializer list doesn't provide. Cross-checked directly against `cc` compiling the identical source.

- An enum constant used as an expression (`enum Color { RED, GREEN, BLUE }; return RED;`) previously failed emission outright with "unknown variable 'RED'" — `enum` member values were computed correctly but nothing ever consulted that table when a member name appeared in an expression. Enums are everywhere in real C headers (error codes, flags, state machines), so this was a hard, immediate compile failure for most real libraries that declare one. Fixed by `CCC.Syntax.EnumResolve`, a post-parse rewrite (run automatically at the end of `Parse.parseProgram`, so every caller sees it uniformly) that replaces every enum-constant-name expression with its resolved integer literal, following C's "0, then previous+1 unless overridden" value rule.

- `switch` case labels (`case RED:`) and array sizes (`char buf[BUF_SIZE];`) now also resolve enum constants — both need a resolved value DURING parsing, before `EnumResolve`'s post-parse whole-program pass ever runs, so `ParseState` now carries a live `enumValues` table populated as each `enum` is parsed.

- A string-literal initializer for a global char array with no explicit size (`char msg[] = "hi";`) used to register the symbol with NO initializer at all: `[]` parses as an 8-byte pointer slot left uninitialized in BSS, so every access through it dereferenced garbage and **segfaulted**, while the verifier still reported the function "verified". Now converts the string into the same initializer-list shape a brace initializer already produces, deducing the array size as `strlen+1` when omitted.

- Function pointers now work end-to-end for every common idiom: a bare function name used as a value, a callback parameter called directly, an explicit `(*fp)(...)` call, an array-of-function-pointers dispatch table, and a global variable holding a function pointer. This closed five separate bugs: (1) a bare function name failed emission outright with "unknown variable" since functions were never registered as values; (2) calling through a local variable/parameter holding a function pointer always compiled to a direct call to a same-named top-level function instead of an indirect call; (3) once (1)/(2) made indirect calls with real arguments reachable, a register-clobber bug silently corrupted the first argument on every such call; (4) the verifier never resolved typedefs before its dereference check, so `(*fp)(...)` on a typedef'd function-pointer type was rejected as a false-positive "non-pointer variable" violation; (5) a global variable holding a function pointer compiled and linked successfully but crashed at runtime, both because indirect calls only checked local variables and because the global's own initializer (a bare function name) was silently stored as null.

- `ccc --harden`'s runtime bounds-check registry only matched an access's base pointer against a tracked allocation's own starting address exactly — an interior pointer produced by pointer arithmetic (`row = p + y*stride; row[x];`) was never itself registered, so the check silently no-opped for it, confirmed to genuinely heap-overflow under AddressSanitizer. The registry lookup is now range-based (does the address fall within some tracked allocation's byte range), so interior-pointer overruns are caught too.

- `VerifyStatus.exempt` (for functions using `setjmp`, whose multiple-return control flow the structural analysis cannot model) was fully designed but never actually implemented anywhere — a function calling `setjmp` was silently analysed as ordinary control flow and reported fully "verified". Now genuinely detected and gated the same way a `degraded` function already was (`--allow-degraded` opts into both). `--report=json`'s `summary.safe` field and the CLI's exit code now share one `CCC.Error.isFullyVerified` check requiring zero degraded/exempt functions in addition to zero violations, so neither can independently claim "safe" for a program that wasn't actually fully verified.

- The `libpng-cve-2015-8126` CVE-corpus entry was scoring `false-positive` purely because of an unguarded `malloc` in its own test harness's `main()`, not the palette-overflow bug the entry exists to test. Adding the missing null check reclassifies it to `missed` — a more honest number — and unmasked a real general soundness gap (tracked separately, not fixed yet): a fixed-capacity array written in a loop bounded by an ordinary, unbounded parameter is silently accepted with no violation.

### Added
- `test/StructLayoutTest.lean` (10 cases) for the struct-alignment and `sizeof(expr)` fixes above.
- `test/StackArgsTest.lean` (6 cases) for the stack-argument fix, including three that link CCC-compiled code against real `cc` output on one side of the call.
- `test/GlobalArrayTest.lean` (10 cases) for the global array and string-literal-initializer fixes, including two cross-checked directly against `cc`.
- `test/EnumResolveTest.lean` (11 cases) for the enum-resolution fixes, including two cross-checked directly against `cc`.
- `test/FuncPtrTest.lean` (10 cases) for the function-pointer fixes, including two cross-checked directly against `cc`.
- `test/JsonReportTest.lean` (5 cases) for `--report=json`.
- 2 new cases in `test/HardenTest.lean` (now 7) and 6 new cases in `test/VerifierFixesTest.lean` (now 31), including direct verifier-level checks for the typedef function-pointer fix and the new `exempt` status.
- `ccc --report=json <file>`: structured, machine-readable verification output (per-function name/status/violations, program-level summary with `safe: bool`) for programmatic consumers, replacing prose-scraping in `scripts/corpus.sh`.
- `scripts/mutation_fuzz.py`: a mutation-fuzzing harness over the CVE corpus (comparison-operator-flip class), wired into CI, that auto-files any newly discovered soundness bug into a corpus entry's `must-reject/` directory.

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
