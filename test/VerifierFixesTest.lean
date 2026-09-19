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

/-- FEL-67: every non-synthetic function must be reported `.degraded`
    (goto/labels, or a fall-through switch case) — status, independent of
    violation count. -/
def expectDegraded (name : String) (src : String) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"✗ {name}: parse error: {e.take 200}"
      pure false
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      let fns := report.results.filter (·.funName != "program")
      if fns.any (·.status == .degraded) then
        IO.println s!"✓ {name}: degraded, as expected"
        pure true
      else
        IO.eprintln s!"✗ {name}: no function reported degraded — regression!"
        pure false

/-- The mirror check: every non-synthetic function must be `.verified`,
    NOT `.degraded` — guards against over-eagerly flagging ordinary,
    fully-analysable control flow (e.g. a break-terminated switch). -/
def expectNotDegraded (name : String) (src : String) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"✗ {name}: parse error: {e.take 200}"
      pure false
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      let fns := report.results.filter (·.funName != "program")
      if fns.any (·.status == .degraded) then
        IO.eprintln s!"✗ {name}: a function was (wrongly) reported degraded — false-positive regression!"
        pure false
      else
        IO.println s!"✓ {name}: not degraded, as expected"
        pure true

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

  -- FEL-56 (div-by-zero, a tractable slice of the integer-overflow domain):
  -- an unguarded division by a computed value that could be zero.
  total := total + 1
  if ← expectCaught "FEL56_div_by_unguarded_value"
    ("int main(int w, int c) {\n" ++
     "  int row_factor = w * c + 1;\n" ++
     "  int x = 100 / row_factor;\n" ++
     "  return x;\n}")
  then pass := pass + 1

  -- Regression guard: an explicit `!= 0` guard (the classic Euclidean-GCD
  -- shape) must not be flagged.
  total := total + 1
  if ← expectClean "FEL56_div_guarded_by_nonzero_check_no_false_positive"
    ("int gcd(int a, int b) {\n" ++
     "  while (b != 0) {\n" ++
     "    int t = b;\n" ++
     "    b = a % b;\n" ++
     "    a = t;\n" ++
     "  }\n  return a;\n}\n" ++
     "int main() { return gcd(252, 105); }")
  then pass := pass + 1

  -- Regression guard: `x % (1 << k)` (compute a power-of-two bucket
  -- count/mask — extremely common, e.g. libwebp's Huffman table code)
  -- must not be flagged just because `k` itself is unconstrained.
  total := total + 1
  if ← expectClean "FEL56_mod_by_shift_of_nonzero_no_false_positive"
    "int main(int sym, int root_bits) {\n  int slot = sym % (1 << root_bits);\n  return slot;\n}"
  then pass := pass + 1

  -- Regression guard: a literal nonzero divisor (the overwhelming common
  -- case in real code) must never be flagged.
  total := total + 1
  if ← expectClean "FEL56_div_by_literal_no_false_positive"
    "int main() { int x = 10; return x / 3; }"
  then pass := pass + 1

  -- Parser: `typedef struct NAME { ... } NAME;` (a struct typedef'd under
  -- its own tag name -- extremely common in real C, e.g. libwebp's
  -- HuffmanCode) previously had its field list silently discarded, so any
  -- value of the type failed emission with "unknown field" the moment a
  -- field was accessed. Compiles and RUNS this (not just checking the
  -- verifier's violation count) since the original bug was an emission
  -- failure, not a verification one.
  total := total + 1
  do
    let src :=
      "typedef struct Pair { int a; int b; } Pair;\n" ++
      "int main() {\n" ++
      "  Pair p;\n" ++
      "  p.a = 17;\n" ++
      "  p.b = 25;\n" ++
      "  return p.a + p.b;\n}\n"
    let pp ← preprocess src "."
    let result := CCC.compile pp "typedef_struct_test.c"
    match result.assembly with
    | none => IO.eprintln s!"✗ FEL55_typedef_struct_own_name_fields: no assembly: {result.report}"
    | some asm =>
        let asmPath := "/tmp/ccc_vf_typedef_struct.s"
        let objPath := "/tmp/ccc_vf_typedef_struct.o"
        let binPath := "/tmp/ccc_vf_typedef_struct"
        IO.FS.writeFile asmPath asm
        let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
        if asOut.exitCode != 0 then
          IO.eprintln s!"✗ FEL55_typedef_struct_own_name_fields: assembler error:\n{asOut.stderr}"
        else
          let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath] }
          if ccOut.exitCode != 0 then
            IO.eprintln s!"✗ FEL55_typedef_struct_own_name_fields: linker error:\n{ccOut.stderr}"
          else
            let runOut ← IO.Process.output { cmd := binPath, args := #[] }
            if runOut.exitCode == 42 then
              IO.println s!"✓ FEL55_typedef_struct_own_name_fields: exit {runOut.exitCode} (expected 42)"
              pass := pass + 1
            else
              IO.eprintln s!"✗ FEL55_typedef_struct_own_name_fields: exit {runOut.exitCode}, expected 42"

  -- FEL-68: sizeof(expr)'s operand is never evaluated in C (well-defined,
  -- no dereference actually happens), so `sizeof(*null_ptr)` must NOT be
  -- flagged as a null-pointer dereference.
  total := total + 1
  if ← expectClean "FEL68_sizeof_expr_operand_not_evaluated"
    "int main() { int *p = 0; return sizeof(*p); }\n"
  then pass := pass + 1

  -- FEL-67: degraded status (goto, or a fall-through switch case) must be
  -- computed AND reported — a function analysed with reduced precision is
  -- not "verified" just because zero violations were found in the parts
  -- CCC could analyse.
  total := total + 1
  if ← expectDegraded "FEL67_goto_marks_function_degraded"
    ("int *p;\n" ++
     "int main() {\n" ++
     "  p = malloc(8);\n" ++
     "  if (p == 0) return 1;\n" ++
     "  int n = 0;\n" ++
     "again:\n" ++
     "  *p = n;\n" ++
     "  free(p);\n" ++
     "  n = n + 1;\n" ++
     "  if (n < 2) { goto again; }\n" ++
     "  return 0;\n" ++
     "}\n")
  then pass := pass + 1

  total := total + 1
  if ← expectDegraded "FEL67_switch_fallthrough_marks_function_degraded"
    ("int main(int argc) {\n" ++
     "  int r = 0;\n" ++
     "  switch (argc) {\n" ++
     "    case 1: r = 1;\n" ++       -- no break: falls through to case 2
     "    case 2: r = 2; break;\n" ++
     "    default: r = 3; break;\n" ++
     "  }\n" ++
     "  return r;\n" ++
     "}\n")
  then pass := pass + 1

  total := total + 1
  if ← expectNotDegraded "FEL67_break_terminated_switch_not_degraded"
    ("int main(int argc) {\n" ++
     "  int r = 0;\n" ++
     "  switch (argc) {\n" ++
     "    case 1: r = 1; break;\n" ++
     "    case 2: r = 2; break;\n" ++
     "    default: r = 3; break;\n" ++
     "  }\n" ++
     "  return r;\n" ++
     "}\n")
  then pass := pass + 1

  total := total + 1
  if ← expectNotDegraded "FEL67_ordinary_loop_not_degraded"
    ("int main() {\n" ++
     "  int i = 0;\n" ++
     "  int sum = 0;\n" ++
     "  while (i < 10) { sum = sum + i; i = i + 1; }\n" ++
     "  return sum;\n" ++
     "}\n")
  then pass := pass + 1

  IO.println s!"\n═══ Results: {pass}/{total} passed ═══"
  if pass == total then
    IO.println "All verifier-fixes regression tests passed!"
    pure 0
  else
    IO.eprintln s!"{total - pass} test(s) FAILED"
    pure 1
