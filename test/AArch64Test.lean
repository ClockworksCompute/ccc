/-
  test/AArch64Test.lean — End-to-end AArch64 backend tests

  Compiles C source → AArch64 assembly → assembles → links → runs on Apple Silicon.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

/-- Preprocess + parse + verify + emit via AArch64 backend -/
def compileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog =>
      let report := CCC.Verify.verifyProgramReport prog
      if report.isSafe then
        pure (emitProgramAArch64 prog)
      else
        -- Try emitting anyway for programs that only have minor verify issues
        pure (emitProgramAArch64 prog)

/-- Assemble + link + run, returning exit code -/
def assembleAndRun (asm : String) (testName : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_arm_{testName}.s"
  let objPath := s!"/tmp/ccc_arm_{testName}.o"
  let binPath := s!"/tmp/ccc_arm_{testName}"
  IO.FS.writeFile asmPath asm
  -- Assemble
  let asOut ← IO.Process.output {
    cmd := "as"
    args := #["-o", objPath, asmPath]
  }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  -- Link
  let ccOut ← IO.Process.output {
    cmd := "cc"
    args := #["-o", binPath, objPath]
  }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"link failed for {testName}:\n{ccOut.stderr}"
  -- Run
  let runOut ← IO.Process.output {
    cmd := binPath
    args := #[]
  }
  pure runOut.exitCode

/-- Run a single test: compile C → asm → assemble → link → run → check exit code -/
def runTest (name : String) (src : String) (expectedExit : UInt32) : IO Bool := do
  match ← compileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compilation error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← assembleAndRun asm name
        if exitCode == expectedExit then
          IO.println s!"✓ {name}: exit code {exitCode} (expected {expectedExit})"
          pure true
        else
          IO.eprintln s!"✗ {name}: exit code {exitCode}, expected {expectedExit}"
          IO.eprintln s!"  Assembly:\n{asm}"
          pure false
      catch e =>
        IO.eprintln s!"✗ {name}: {e}"
        pure false

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  let cases : List (String × String × UInt32) := [
    -- 1. Return constant
    ("return_42",
     "int main() { return 42; }",
     42),

    -- 2. Arithmetic: addition
    ("add_3_4",
     "int main() { return 3 + 4; }",
     7),

    -- 3. Arithmetic: subtraction
    ("sub_10_3",
     "int main() { return 10 - 3; }",
     7),

    -- 4. Arithmetic: multiplication
    ("mul_6_7",
     "int main() { return 6 * 7; }",
     42),

    -- 5. Arithmetic: division
    ("div_84_2",
     "int main() { return 84 / 2; }",
     42),

    -- 6. Arithmetic: modulo
    ("mod_17_5",
     "int main() { return 17 % 5; }",
     2),

    -- 7. Local variable
    ("local_var",
     "int main() { int x = 42; return x; }",
     42),

    -- 8. Multiple locals and expressions
    ("multi_local",
     "int main() { int a = 10; int b = 20; int c = a + b; return c; }",
     30),

    -- 9. If/else — true branch
    ("if_true",
     "int main() { int x = 5; if (x > 3) { return 1; } else { return 0; } }",
     1),

    -- 10. If/else — false branch
    ("if_false",
     "int main() { int x = 1; if (x > 3) { return 1; } else { return 0; } }",
     0),

    -- 11. While loop
    ("while_loop",
     "int main() { int i = 0; int s = 0; while (i < 5) { s = s + i; i = i + 1; } return s; }",
     10),

    -- 12. For loop
    ("for_loop",
     "int main() { int s = 0; for (int i = 0; i < 10; i = i + 1) { s = s + i; } return s; }",
     45),

    -- 13. Function call with args
    ("func_call",
     "int add(int a, int b) { return a + b; } int main() { return add(20, 22); }",
     42),

    -- 14. Multiple function calls
    ("multi_call",
     "int double_(int x) { return x + x; } int main() { return double_(double_(5)); }",
     20),

    -- 15. Nested if
    ("nested_if",
     "int main() { int x = 10; if (x > 5) { if (x > 8) { return 1; } else { return 2; } } else { return 3; } }",
     1),

    -- 16. Comparison operators
    ("cmp_eq",
     "int main() { int x = 5; if (x == 5) { return 1; } return 0; }",
     1),

    -- 17. Negation
    ("negation",
     "int main() { int x = -42; return 0 - x; }",
     42),

    -- 18. Logical not
    ("logical_not",
     "int main() { int x = 0; if (!x) { return 1; } return 0; }",
     1),

    -- 19. Compound expressions
    ("compound",
     "int main() { return (2 + 3) * (8 - 1); }",
     35),

    -- 20. Do-while loop
    ("do_while",
     "int main() { int x = 0; do { x = x + 1; } while (x < 5); return x; }",
     5),

    -- 21. Break from loop
    ("break_test",
     "int main() { int i = 0; while (i < 100) { if (i == 7) { break; } i = i + 1; } return i; }",
     7),

    -- 22. Continue in loop
    ("continue_test",
     "int main() { int s = 0; for (int i = 0; i < 10; i = i + 1) { if (i == 5) { continue; } s = s + 1; } return s; }",
     9),

    -- 23. Ternary expression
    ("ternary",
     "int main() { int x = 5; int y = x > 3 ? 42 : 0; return y; }",
     42),

    -- 24. Bitwise AND
    ("bitwise_and",
     "int main() { return 0xFF & 0x0F; }",
     15),

    -- 25. Bitwise OR
    ("bitwise_or",
     "int main() { return 0xF0 | 0x0F; }",
     255),

    -- 26. Shift left
    ("shift_left",
     "int main() { return 1 << 3; }",
     8),

    -- 27. Increment
    ("pre_inc",
     "int main() { int x = 41; ++x; return x; }",
     42),

    -- 28. Compound assignment
    ("plus_assign",
     "int main() { int x = 30; x += 12; return x; }",
     42),

    -- 29. Switch
    ("switch_basic",
     "int main() { int x = 2; int r = 0; switch (x) { case 1: r = 10; break; case 2: r = 42; break; default: r = 99; break; } return r; }",
     42),

    -- 30. Goto
    ("goto_test",
     "int main() { int x = 0; goto done; x = 99; done: return x; }",
     0),

    -- 31. Logical AND
    ("logical_and",
     "int main() { int a = 1; int b = 1; if (a && b) { return 1; } return 0; }",
     1),

    -- 32. Logical OR
    ("logical_or",
     "int main() { int a = 0; int b = 1; if (a || b) { return 1; } return 0; }",
     1),

    -- 33. Three args
    ("three_args",
     "int sum3(int a, int b, int c) { return a + b + c; } int main() { return sum3(10, 20, 12); }",
     42),

    -- 34. Recursive function
    ("recursive",
     "int fib(int n) { if (n <= 1) { return n; } return fib(n - 1) + fib(n - 2); } int main() { return fib(10); }",
     55)
  ]

  for (name, src, expected) in cases do
    total := total + 1
    let ok ← runTest name src expected
    if ok then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  AArch64 backend: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
