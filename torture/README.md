# GCC Torture Test Classification

## Source

GCC torture tests: `gcc/testsuite/gcc.c-torture/execute/`
Typically ~1800 test programs.

## Classification

Each test is classified as:

- **APPLICABLE**: Standard C99, within CCC's supported feature set
- **EXCLUDED_EXT**: Uses GCC extensions CCC will never support
  (nested functions, __builtin_*, __attribute__((cleanup)), statement expressions, etc.)
- **EXCLUDED_FEATURE**: Uses C features CCC explicitly doesn't support
  (_Complex, _Atomic, VLAs, alloca, __int128, etc.)
- **EXCLUDED_RUNTIME**: Requires specific runtime behavior CCC can't provide
  (signal handling, setjmp in unsupported contexts, etc.)

## Estimated breakdown (based on GCC torture suite analysis)

| Category | Estimated count | % |
|----------|----------------|---|
| APPLICABLE | ~900-1100 | 50-60% |
| EXCLUDED_EXT | ~400-500 | 25-30% |
| EXCLUDED_FEATURE | ~200-300 | 10-15% |
| EXCLUDED_RUNTIME | ~50-100 | 3-5% |

## Target

90%+ pass rate on APPLICABLE tests for x86-64.

## Test harness

```bash
# torture/run_torture.sh
# For each applicable test:
# 1. ccc -c test.c -o test.s
# 2. as test.s -o test.o
# 3. gcc test.o -o test
# 4. ./test; check exit code
```

## Classification script

```bash
# torture/classify.sh
# Scans each .c file for markers:
# - __builtin_ → EXCLUDED_EXT
# - __attribute__((cleanup)) → EXCLUDED_EXT
# - _Complex → EXCLUDED_FEATURE
# - alloca → EXCLUDED_FEATURE
# - nested function def → EXCLUDED_EXT
# Everything else → APPLICABLE
```

## Baseline

After EPIC-CCC08: baseline pass rate on APPLICABLE tests = ~5-10%
(only basic integer programs with no unsupported features).
After EPIC-CCC20: target ~60-70%.
After EPIC-CCC40: target 90%+.
