# Changelog

All notable changes to CCC are documented in this file.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
