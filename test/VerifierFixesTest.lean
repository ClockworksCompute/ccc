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

/-- FEL-65 epic DoD bullet 7 ("never call a skipped function verified"):
    a function calling `setjmp` must be reported `.exempt` — verification
    SKIPPED, not merely degraded, since the analysis's single-return
    assumption is fundamentally wrong for it. -/
def expectExempt (name : String) (src : String) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"✗ {name}: parse error: {e.take 200}"
      pure false
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      let fns := report.results.filter (·.funName != "program")
      if fns.any (·.status == .exempt) then
        IO.println s!"✓ {name}: exempt, as expected"
        pure true
      else
        IO.eprintln s!"✗ {name}: no function reported exempt — regression!"
        pure false

/-- The mirror check: an ordinary function with no `setjmp` call must NOT
    be reported `.exempt`. -/
def expectNotExempt (name : String) (src : String) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"✗ {name}: parse error: {e.take 200}"
      pure false
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      let fns := report.results.filter (·.funName != "program")
      if fns.any (·.status == .exempt) then
        IO.eprintln s!"✗ {name}: a function was (wrongly) reported exempt — false-positive regression!"
        pure false
      else
        IO.println s!"✓ {name}: not exempt, as expected"
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

  -- FEL-68 follow-up: `state.getType` stores a variable's declared type
  -- EXACTLY as written, never resolved through typedefs, so a TYPEDEF'D
  -- function-pointer type (`typedef int (*op_t)(int,int); op_t p;`)
  -- made `(*p)(...)` look like a dereference of a non-pointer, plain
  -- `op_t` value -- rejected outright as a memory-safety violation, for
  -- perfectly ordinary, valid code (the callback-parameter/dispatch
  -- pattern real C libraries use constantly).
  total := total + 1
  if ← expectClean "FEL68_funcptr_deref_of_typedef_not_flagged"
    ("int add(int a, int b) { return a + b; }\n" ++
     "typedef int (*op_t)(int, int);\n" ++
     "int main() {\n  op_t p = add;\n  return (*p)(3, 4);\n}\n")
  then pass := pass + 1

  -- FEL-65 epic DoD bullet 7: `.exempt` was designed (VerifyStatus's own
  -- doc comment says "uses EXEMPT features (varargs, setjmp);
  -- verification skipped") but NOTHING in the verifier ever actually
  -- produced it, for any reason -- a function calling `setjmp` was
  -- silently analysed as ordinary control flow and reported fully
  -- `verified`, directly contradicting the epic's own bullet 7.
  total := total + 1
  if ← expectExempt "FEL65_setjmp_call_marks_function_exempt"
    ("typedef struct { int x[8]; } jmp_buf;\n" ++
     "int setjmp(jmp_buf env);\n" ++
     "int risky(jmp_buf env, int x) {\n" ++
     "  if (setjmp(env)) { return -1; }\n" ++
     "  return x + 1;\n" ++
     "}\n" ++
     "int main() { jmp_buf jb; return risky(jb, 5); }\n")
  then pass := pass + 1

  -- setjmp nested inside an arbitrary expression (not just a bare `if`
  -- condition) must also be found -- exercises the recursive expression
  -- walk, not just the statement-level one.
  total := total + 1
  if ← expectExempt "FEL65_setjmp_nested_in_expression_marks_exempt"
    ("typedef struct { int x[8]; } jmp_buf;\n" ++
     "int setjmp(jmp_buf env);\n" ++
     "int risky(jmp_buf env) {\n" ++
     "  int r = 1 + setjmp(env);\n" ++
     "  return r;\n" ++
     "}\n" ++
     "int main() { jmp_buf jb; return risky(jb); }\n")
  then pass := pass + 1

  -- An ordinary function with no setjmp call must NOT be marked exempt.
  total := total + 1
  if ← expectNotExempt "FEL65_ordinary_function_not_exempt"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int main() { return add(2, 3); }\n")
  then pass := pass + 1

  -- FEL-76: a fixed-capacity array parameter indexed inside a loop
  -- bounded by an ORDINARY, unbounded parameter used to be silently
  -- ACCEPTED with a `runtime-bounded` verdict -- confirmed with `cc
  -- -fsanitize=address` to genuinely heap/stack-overflow. Root cause: the
  -- bounded-fuel loop fixpoint (CCC/Verify/Verify.lean's `fixpointBody`)
  -- had no WIDENING step, so a loop counter's carried-forward range just
  -- grew by the step's fixed increment each round and FROZE at whatever
  -- value it reached when fuel ran out, instead of correctly recognizing
  -- non-convergence and treating the bound as unknown. Fixed by
  -- `widenUnstableRanges`, applied every fixpoint round.
  total := total + 1
  if ← expectCaught "FEL76_array_param_indexed_by_unbounded_param_loop"
    ("void fill(int arr[10], int n) {\n" ++
     "  int i;\n" ++
     "  for (i = 0; i < n; i = i + 1) { arr[i] = i; }\n" ++
     "}\n" ++
     "int main() {\n  int arr[10];\n  fill(arr, 20);\n  return arr[0];\n}\n")
  then pass := pass + 1

  -- Same shape through a struct-field array via a pointer parameter
  -- (`s->arr[i]`), not just a plain array parameter -- confirms the fix
  -- isn't specific to one syntactic form of "known in-function capacity".
  total := total + 1
  if ← expectCaught "FEL76_struct_field_array_indexed_by_unbounded_param_loop"
    ("struct S { int arr[10]; };\n" ++
     "void fill(struct S *s, int n) {\n" ++
     "  int i;\n" ++
     "  for (i = 0; i < n; i = i + 1) { s->arr[i] = i; }\n" ++
     "}\n" ++
     "int main() {\n  struct S s;\n  fill(&s, 20);\n  return s.arr[0];\n}\n")
  then pass := pass + 1

  -- The exact false-positive/regression risk this fix must NOT introduce:
  -- an ordinary loop bounded by a LITERAL matching the array's own real
  -- capacity must still verify clean -- this is re-derived fresh from the
  -- condition every iteration (`inferExprBoundFromCond`/
  -- `inferTransitiveBounds`, applied at loop-body entry), not from the
  -- cross-iteration carried-forward range the widening fix touches, so it
  -- must be completely unaffected.
  total := total + 1
  if ← expectClean "FEL76_literal_bounded_loop_still_verifies"
    ("void fill(int arr[10]) {\n" ++
     "  int i;\n" ++
     "  for (i = 0; i < 10; i = i + 1) { arr[i] = i; }\n" ++
     "}\n" ++
     "int main() {\n  int arr[10];\n  fill(arr);\n  return arr[0];\n}\n")
  then pass := pass + 1

  -- FEL-77: a division whose divisor is a variable initialized to a sum
  -- that unconditionally includes `+ 1`, with every other term explicitly
  -- widened to size_t before multiplying (matching real libpng's own
  -- CVE-2018-13785 fix), is provably nonzero regardless of what those
  -- other (runtime, attacker-influenced) terms are -- `resolveExprInt`
  -- alone can never fold this (the terms aren't compile-time constants),
  -- so this used to be an unconditional "cannot verify divisor is
  -- nonzero" false positive.
  total := total + 1
  if ← expectClean "FEL77_widened_sum_plus_one_provably_nonzero"
    ("typedef unsigned int uint32_t;\n" ++
     "typedef unsigned long size_t;\n" ++
     "int check(uint32_t width, uint32_t channels, uint32_t bit_depth, uint32_t interlaced, uint32_t height) {\n" ++
     "  size_t row_factor = (size_t)width * (size_t)channels * (bit_depth > 8 ? 2 : 1) + 1 + (interlaced ? 6 : 0);\n" ++
     "  if ((size_t)height > 0xFFFFFFFFUL / row_factor) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n" ++
     "int main() { return check(1431655765u, 3, 8, 0, 100); }\n")
  then pass := pass + 1

  -- THE critical adversarial case a first (since-replaced) version of the
  -- FEL-77 fix got wrong: the SAME "sum with a +1" shape, but computed
  -- ENTIRELY in native 32-bit arithmetic with NO widening cast anywhere
  -- (matching CVE-2018-13785's actual VULNERABLE shape) -- `width *
  -- channels` alone can wrap past 0xFFFFFFFF, and the following `+ 1` can
  -- then wrap the WHOLE expression back around to exactly 0. A naive
  -- "unsigned type means every term is non-negative, so the sum is >= 1"
  -- inference is UNSOUND here: it mistakes "no term is individually
  -- negative" for "the arithmetic can't wrap", which are not the same
  -- claim, and would silently re-introduce exactly the FEL-64 class of
  -- mistake this project already had to revert once. This MUST still be
  -- rejected.
  total := total + 1
  if ← expectCaught "FEL77_narrow_sum_plus_one_NOT_trusted_wraparound_risk"
    ("typedef unsigned int uint32_t;\n" ++
     "int check(uint32_t width, uint32_t channels, uint32_t bit_depth, uint32_t interlaced, uint32_t height) {\n" ++
     "  uint32_t row_factor = width * channels * (bit_depth > 8 ? 2 : 1) + 1 + (interlaced ? 6 : 0);\n" ++
     "  if (height > 0xFFFFFFFFU / row_factor) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n" ++
     "int main() { return check(1431655765u, 3, 8, 0, 100); }\n")
  then pass := pass + 1

  -- An explicit cast that is STILL only 32 bits wide (`(uint32_t)`, not
  -- `(size_t)`) must not be mistaken for a real widening cast either --
  -- the presence of *a* cast is not the signal; the cast's TARGET width
  -- is.
  total := total + 1
  if ← expectCaught "FEL77_explicit_but_still_narrow_cast_NOT_trusted"
    ("typedef unsigned int uint32_t;\n" ++
     "int check(uint32_t width, uint32_t channels) {\n" ++
     "  uint32_t row_factor = (uint32_t)width * (uint32_t)channels + 1;\n" ++
     "  if (100 > 0xFFFFFFFFU / row_factor) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n" ++
     "int main() { return check(1431655765u, 3); }\n")
  then pass := pass + 1

  -- Without the `+ 1` safety margin at all, even a fully-widened product
  -- genuinely CAN be zero (e.g. width=0) -- must still be rejected. Guards
  -- against the inference being loosened to "any widened product is
  -- automatically nonzero" rather than requiring an actual proven bound
  -- strictly greater than zero.
  total := total + 1
  if ← expectCaught "FEL77_widened_product_without_plus_one_still_rejected"
    ("typedef unsigned int uint32_t;\n" ++
     "typedef unsigned long size_t;\n" ++
     "int check(uint32_t width, uint32_t channels) {\n" ++
     "  size_t row_factor = (size_t)width * (size_t)channels;\n" ++
     "  if (100 > 0xFFFFFFFFUL / row_factor) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n" ++
     "int main() { return check(0, 3); }\n")
  then pass := pass + 1

  -- FEL-45 reopen (2026-09-19 review): a memcpy-shaped sink whose
  -- DESTINATION size cannot be determined statically (a bare pointer
  -- parameter, not an array or a known allocation) used to silently pass
  -- with 0 violations -- exactly the shape that masked the ticket's
  -- original example, `void copy(char *dst, char *src, int n)`.
  total := total + 1
  if ← expectCaught "FEL45_memcpy_unknown_dest_size_now_caught"
    ("void copy(char *dst, char *src, int n) {\n" ++
     "  memcpy(dst, src, n);\n" ++
     "}\n" ++
     "int main() { char a[8]; char b[8]; copy(a, b, 4); return 0; }\n")
  then pass := pass + 1

  -- Regression guard: memcpy between two arrays of statically-known size,
  -- with a length that provably fits both, must remain clean.
  total := total + 1
  if ← expectClean "FEL45_memcpy_known_sizes_still_clean"
    "int main() {\n  char dst[16];\n  char src[8];\n  memcpy(dst, src, 8);\n  return 0;\n}"
  then pass := pass + 1

  -- Same unknown-destination gap for the single-buffer sinks (memset was
  -- already in the table, but only checked when the destination size WAS
  -- known -- an unknown one fell through unchanged).
  total := total + 1
  if ← expectCaught "FEL45_memset_unknown_dest_size_now_caught"
    "void clear(char *p, int n) {\n  memset(p, 0, n);\n  return;\n}\n"
  then pass := pass + 1

  -- FEL-45 reopen: fread/read/fgets/vsnprintf newly added to the sink
  -- table (same (dst, len) shape as memset/strncpy/snprintf); each must
  -- now be checked rather than passed through unmodelled.
  total := total + 1
  if ← expectCaught "FEL45_fread_unknown_dest_size_caught"
    ("typedef unsigned long size_t;\n" ++
     "extern size_t fread(void *ptr, size_t size, size_t nmemb, void *stream);\n" ++
     "void load(char *buf, void *f) {\n  fread(buf, 1, 1000, f);\n}\n" ++
     "int main() { char b[8]; load(b, 0); return 0; }\n")
  then pass := pass + 1

  total := total + 1
  if ← expectCaught "FEL45_read_unknown_dest_size_caught"
    ("extern long read(int fd, void *buf, unsigned long count);\n" ++
     "void recvAll(int fd, char *buf, int n) {\n  read(fd, buf, n);\n}\n" ++
     "int main() { char b[8]; recvAll(0, b, 4); return 0; }\n")
  then pass := pass + 1

  total := total + 1
  if ← expectCaught "FEL45_fgets_unknown_dest_size_caught"
    ("extern char *fgets(char *s, int size, void *stream);\n" ++
     "void readLine(char *buf, int n, void *f) {\n  fgets(buf, n, f);\n}\n" ++
     "int main() { char b[8]; readLine(b, 8, 0); return 0; }\n")
  then pass := pass + 1

  total := total + 1
  if ← expectCaught "FEL45_vsnprintf_unknown_dest_size_caught"
    ("typedef unsigned long size_t;\n" ++
     "typedef struct __va_list_tag *va_list;\n" ++
     "extern int vsnprintf(char *s, size_t n, const char *fmt, va_list ap);\n" ++
     "void fmtInto(char *buf, int n, const char *fmt, va_list ap) {\n" ++
     "  vsnprintf(buf, n, fmt, ap);\n" ++
     "}\n" ++
     "int main() { return 0; }\n")
  then pass := pass + 1

  -- strncat's destination needs room for its EXISTING content plus n+1
  -- bytes, which this verifier does not track at all -- must always be
  -- flagged, even with a statically-sized, plausibly-large-enough buffer,
  -- since "large enough for what's already in it" is exactly what cannot
  -- be verified.
  total := total + 1
  if ← expectCaught "FEL45_strncat_always_flagged"
    "int main() {\n  char buf[64] = \"hello\";\n  strncat(buf, \" world\", 6);\n  return 0;\n}"
  then pass := pass + 1

  IO.println s!"\n═══ Results: {pass}/{total} passed ═══"
  if pass == total then
    IO.println "All verifier-fixes regression tests passed!"
    pure 0
  else
    IO.eprintln s!"{total - pass} test(s) FAILED"
    pure 1
