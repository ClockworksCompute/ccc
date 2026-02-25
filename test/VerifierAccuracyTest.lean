/-
  test/VerifierAccuracyTest.lean — Verifier false-positive elimination

  Tests that function prototypes (from #include or forward declarations) flow
  through the parser into prog.externs, and the verifier no longer produces
  false "undefined function" violations for standard library calls.
-/
import CCC

open CCC CCC.Syntax CCC.Parse CCC.Preprocess

/-- Preprocess + parse + verify, return violation count. -/
def verifySource (src : String) : IO Nat := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e =>
      IO.eprintln s!"  parse error: {e.take 120}"
      pure 999  -- sentinel for parse failure
  | .ok prog =>
      let report := Verify.verifyProgramReport prog
      let violations := report.allViolations
      pure violations.length

/-- Run a single test case. -/
def runTest (name : String) (src : String) (expectViolations : Nat) : IO Bool := do
  let actual ← verifySource src
  if actual == expectViolations then
    IO.println s!"✓ {name}: {actual} violations (expected {expectViolations})"
    pure true
  else
    IO.eprintln s!"✗ {name}: got {actual} violations, expected {expectViolations}"
    pure false

def main : IO UInt32 := do
  IO.println "═══ CCC44: Verifier Accuracy Tests ═══"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- ─── Test 1: printf with stdio.h → 0 violations ───
  total := total + 1
  if ← runTest "printf_with_stdio"
    "#include <stdio.h>\nint main() { printf(\"hello\\n\"); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 2: strlen with string.h → 0 violations ───
  total := total + 1
  if ← runTest "strlen_with_string"
    "#include <string.h>\nint main() { int n = strlen(\"hello\"); return n; }" 0
  then pass := pass + 1

  -- ─── Test 3: malloc/free with stdlib.h → 0 violations ───
  total := total + 1
  if ← runTest "malloc_free_with_stdlib"
    "#include <stdlib.h>\nint main() { void *p = malloc(10); free(p); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 4: variadic printf with multiple args → 0 violations ───
  total := total + 1
  if ← runTest "printf_variadic_multi_args"
    "#include <stdio.h>\nint main() { printf(\"x=%d y=%d\\n\", 1, 2); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 5: forward declaration works ───
  total := total + 1
  if ← runTest "forward_declaration"
    "int foo(int x);\nint main() { return foo(42); }\nint foo(int x) { return x; }" 0
  then pass := pass + 1

  -- ─── Test 6: truly undefined function → 0 violations (linker catches it) ───
  total := total + 1
  if ← runTest "undefined_function_no_crash"
    "int main() { undefined_func(); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 7: memcpy with string.h → 0 violations ───
  total := total + 1
  if ← runTest "memcpy_with_string"
    "#include <string.h>\nint main() { char a[10]; char b[10]; memcpy(a, b, 5); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 8: fprintf with stdio.h (variadic, 2+ args) → 0 violations ───
  total := total + 1
  if ← runTest "fprintf_variadic"
    "#include <stdio.h>\nint main() { fprintf(stdout, \"val=%d\\n\", 42); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 9: snprintf with stdio.h → 0 violations ───
  total := total + 1
  if ← runTest "snprintf_with_stdio"
    "#include <stdio.h>\nint main() { char buf[64]; snprintf(buf, 64, \"x=%d\", 1); return 0; }" 0
  then pass := pass + 1

  -- ─── Test 10: memset with string.h → 0 violations ───
  total := total + 1
  if ← runTest "memset_with_string"
    "#include <string.h>\nint main() { char buf[32]; memset(buf, 0, 32); return 0; }" 0
  then pass := pass + 1

  -- ─── Summary ───
  IO.println s!"\n═══ Results: {pass}/{total} passed ═══"
  if pass == total then
    IO.println "All verifier accuracy tests passed!"
    pure 0
  else
    IO.eprintln s!"{total - pass} test(s) FAILED"
    pure 1
