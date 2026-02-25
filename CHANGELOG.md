# Changelog

All notable changes to CCC are documented in this file.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
