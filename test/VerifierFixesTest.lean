/-
  test/VerifierFixesTest.lean — Regression tests for the 2026-09-19 review
  fixes (Linear FEL-40..49) and the libheif-class-detection epic groundwork
  (FEL-54..62).

  Each case is either:
    - a MISS regression guard: a program that used to be silently ACCEPTED
      despite a real bug, which must now produce at least one violation, or
    - a FALSE-POSITIVE regression guard: a program that used to be
      (wrongly) REJECTED, which must now produce zero violations.

  Mirrors the style of test/VerifierAccuracyTest.lean (parse + verify,
  assert an exact/threshold violation count) rather than compiling and
  running a binary — these are about verifier judgment, not codegen.
-/
import CCC

open CCC CCC.Syntax CCC.Parse CCC.Preprocess

/-- Preprocess + parse + verify, return violation count. -/
def vfViolationCount (src : String) : IO Nat := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"  parse error: {e.take 200}"
      pure 999  -- sentinel for parse failure
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      pure report.allViolations.length

/-- A case that USED TO BE MISSED (0 violations) and must now be caught
    (at least 1 violation). -/
def expectCaught (name : String) (src : String) : IO Bool := do
  let n ← vfViolationCount src
  if n ≥ 1 then
    IO.println s!"✓ {name}: caught ({n} violation(s), expected ≥1)"
    pure true
  else
    IO.eprintln s!"✗ {name}: NOT caught (0 violations, expected ≥1) — regression!"
    pure false

/-- A case that USED TO BE A FALSE POSITIVE and must now be accepted
    cleanly (0 violations). -/
def expectClean (name : String) (src : String) : IO Bool := do
  let n ← vfViolationCount src
  if n == 0 then
    IO.println s!"✓ {name}: clean (0 violations, as expected)"
    pure true
  else
    IO.eprintln s!"✗ {name}: {n} violation(s) found, expected 0 — false positive regression!"
    pure false

def main : IO UInt32 := do
  IO.println "═══ Verifier fixes regression suite (FEL-40..49) ═══"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- FEL-41: violation inside a then-branch that ends in `return` must not
  -- be dropped just because the else-branch is what continues.
  total := total + 1
  if ← expectCaught "FEL41_if_return_drops_violation"
    "int main(int argc) {\n  char buf[4];\n  if (argc > 1) { buf[10] = 1; return 1; }\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-42: a bound learned from an early-return guard must not survive a
  -- later reassignment of the same variable.
  total := total + 1
  if ← expectCaught "FEL42_bound_not_invalidated_on_write"
    "int main(int argc) {\n  char buf[8];\n  int i = argc;\n  if (i >= 8) { return 1; }\n  i = i + 100;\n  buf[i] = 1;\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-42: same, through a struct field (the Heartbleed shape).
  total := total + 1
  if ← expectCaught "FEL42_field_bound_not_invalidated"
    ("struct R { int len; char data[64]; };\n" ++
     "int main() {\n" ++
     "  struct R *r = malloc(sizeof(struct R));\n" ++
     "  if (r == 0) { return 1; }\n" ++
     "  char out[64];\n" ++
     "  r->len = 10;\n" ++
     "  if (r->len > 64) { free(r); return 1; }\n" ++
     "  r->len = 9999;\n" ++
     "  memcpy(out, r->data, r->len);\n" ++
     "  free(r);\n" ++
     "  return out[0];\n}")
  then pass := pass + 1

  -- FEL-43: use-after-free / double-free that only manifests on the
  -- second trip around a `while` loop.
  total := total + 1
  if ← expectCaught "FEL43_loop_uaf_second_iteration"
    ("int main() {\n" ++
     "  int *p = malloc(8);\n" ++
     "  if (p == 0) { return 1; }\n" ++
     "  int i = 0;\n" ++
     "  while (i < 2) {\n" ++
     "    *p = i;\n" ++
     "    free(p);\n" ++
     "    i = i + 1;\n" ++
     "  }\n  return 0;\n}")
  then pass := pass + 1

  -- FEL-44: a pointer stored in a struct field is now tracked like a
  -- local variable — UAF/double-free through `s.p` must be caught.
  total := total + 1
  if ← expectCaught "FEL44_struct_field_pointer_uaf"
    ("struct S { int *p; };\n" ++
     "int main() {\n" ++
     "  struct S s;\n" ++
     "  s.p = malloc(8);\n" ++
     "  if (s.p == 0) { return 1; }\n" ++
     "  free(s.p);\n" ++
     "  *s.p = 1;\n" ++
     "  free(s.p);\n  return 0;\n}")
  then pass := pass + 1

  -- FEL-44: a dereference through pointer arithmetic (unresolvable root)
  -- must now be a "cannot verify" violation, not a silent pass.
  total := total + 1
  if ← expectCaught "FEL44_pointer_arithmetic_unresolved_deref"
    "int main() {\n  char buf[8];\n  char *q = buf + 100;\n  *q = 2;\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-44: dereferencing a pointer that was declared but never assigned.
  total := total + 1
  if ← expectCaught "FEL44_uninitialized_pointer_deref"
    "int main() {\n  int *p;\n  *p = 1;\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-45: strcpy from a non-literal / too-long source must be flagged.
  total := total + 1
  if ← expectCaught "FEL45_strcpy_literal_overflow"
    "int main() {\n  char buf[4];\n  strcpy(buf, \"hello world\");\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-45 (precision, not just a violation-count check): strcpy from a
  -- literal that DOES fit must not be flagged.
  total := total + 1
  if ← expectClean "FEL45_strcpy_literal_fits"
    "int main() {\n  char buf[20];\n  strcpy(buf, \"hello\");\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-46: a provably-negative index into a stack array.
  total := total + 1
  if ← expectCaught "FEL46_negative_index"
    "int main() {\n  char buf[8];\n  int i = -5;\n  if (i < 8) { buf[i] = 1; }\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-46 regression guard: a normal unsigned loop counter from 0 must
  -- NOT become a false positive now that negative indices are checked.
  total := total + 1
  if ← expectClean "FEL46_unsigned_loop_counter_no_false_positive"
    ("int main() {\n" ++
     "  char buf[8];\n" ++
     "  unsigned int i;\n" ++
     "  for (i = 0; i < 8; i = i + 1) {\n" ++
     "    buf[i] = 1;\n" ++
     "  }\n  return 0;\n}")
  then pass := pass + 1

  -- FEL-47: malloc with a non-constant size must still be tracked as a
  -- nullable heap pointer — `free()` on it must not be a false positive.
  total := total + 1
  if ← expectClean "FEL47_malloc_nonconst_size_no_false_positive"
    "int main(int n) {\n  char *buf = malloc(n);\n  if (buf == 0) { return 1; }\n  free(buf);\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-47: calloc is now tracked with a known size, so an out-of-bounds
  -- index into it is caught (previously calloc was unrecognized).
  total := total + 1
  if ← expectCaught "FEL47_calloc_bounds"
    "int main() {\n  int *p = calloc(2, sizeof(int));\n  if (p == 0) { return 1; }\n  p[5] = 1;\n  free(p);\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-48 (partial): a callee that frees a parameter is now visible at
  -- the call site — use-after-free/double-free through `release(p)`.
  total := total + 1
  if ← expectCaught "FEL48_callee_frees_param"
    ("void release(int *p) { free(p); }\n" ++
     "int main() {\n" ++
     "  int *p = malloc(8);\n" ++
     "  if (p == 0) { return 1; }\n" ++
     "  release(p);\n" ++
     "  *p = 1;\n" ++
     "  release(p);\n  return 0;\n}")
  then pass := pass + 1

  -- FEL-49: `if (!p) return;` must be recognized as a null-check.
  total := total + 1
  if ← expectClean "FEL49_bang_null_idiom"
    "int main() {\n  int *p = malloc(8);\n  if (!p) { return 1; }\n  *p = 5;\n  free(p);\n  return 0;\n}"
  then pass := pass + 1

  -- FEL-49: `p == NULL` / `p != NULL` (the NULL macro, not just `== 0`)
  -- must be recognized as a null-check.
  total := total + 1
  if ← expectClean "FEL49_NULL_macro_idiom"
    ("#include <stdlib.h>\n" ++
     "int main() {\n" ++
     "  int *p = malloc(8);\n" ++
     "  if (p == NULL) { return 1; }\n" ++
     "  *p = 5;\n" ++
     "  if (p != NULL) { *p = 6; }\n" ++
     "  free(p);\n  return 0;\n}")
  then pass := pass + 1

  -- FEL-49: a `switch` where every case ends in `break` must not report a
  -- spurious use-after-free/double-free from threading state across cases.
  total := total + 1
  if ← expectClean "FEL49_switch_break_no_false_positive"
    ("int main(int argc) {\n" ++
     "  int *p = malloc(8);\n" ++
     "  if (p == 0) { return 1; }\n" ++
     "  switch (argc) {\n" ++
     "    case 1: free(p); break;\n" ++
     "    case 2: *p = 1; free(p); break;\n" ++
     "    default: free(p); break;\n" ++
     "  }\n  return 0;\n}")
  then pass := pass + 1

  IO.println s!"\n═══ Results: {pass}/{total} passed ═══"
  if pass == total then
    IO.println "All verifier-fixes regression tests passed!"
    pure 0
  else
    IO.eprintln s!"{total - pass} test(s) FAILED"
    pure 1
