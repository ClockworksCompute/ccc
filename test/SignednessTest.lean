/-
  test/SignednessTest.lean — Signed-integer codegen regression tests (FEL-50)

  Covers the AArch64 emitter bug where signed sub-word loads (`int`/`short`/`char`) were
  always zero-extended instead of sign-extended, and where division/modulo/shift/comparison
  always used the signed instruction form regardless of operand type. Together these made
  negative values, signed division/modulo, and 32-bit `int` overflow compute wrong results.

  Compile C → AArch64 assembly (via `emitProgramAArch64`, bypassing the verifier) → assemble
  → link → run → check exit code.

  Note: two of the probes from the bug report use comma-separated multi-declaration with
  initializers (`int a=-8,b=2;`), which hits an unrelated, pre-existing parser/emitter
  limitation (`unknown variable 'b'`) independent of signedness. Those two are written here
  with separate declarations instead, which is sufficient to exercise the signed division/
  modulo codegen this file is testing.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

/-- Preprocess + parse + emit via AArch64 backend (bypasses verifier). -/
def signSuiteCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

/-- Assemble + link + run, returning exit code. -/
def signSuiteAssembleAndRun (asm : String) (testName : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_sign_{testName}.s"
  let objPath := s!"/tmp/ccc_sign_{testName}.o"
  let binPath := s!"/tmp/ccc_sign_{testName}"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output {
    cmd := "as"
    args := #["-o", objPath, asmPath]
  }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  let ccOut ← IO.Process.output {
    cmd := "cc"
    args := #["-o", binPath, objPath]
  }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"link failed for {testName}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output {
    cmd := binPath
    args := #[]
  }
  pure runOut.exitCode

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  IO.println "═══════════════════════════════════════════"
  IO.println "  Signedness Tests (FEL-50)"
  IO.println "═══════════════════════════════════════════"

  let cases : List (String × String) := [
    ("negative_int_lt_zero",
      "int main() { int x = -1; if (x < 0) return 1; return 0; }"),
    ("signed_div_negative",
      "int main() { int a = -8; int b = 2; if (a/b == -4) return 1; return 0; }"),
    ("signed_mod_negative",
      "int main() { int a = -7; int b = 3; if (a%b == -1) return 1; return 0; }"),
    ("negative_char_lt_zero",
      "int main() { char c = -1; if (c < 0) return 1; return 0; }"),
    ("negative_char_array_elem",
      "int main() { char buf[2]; buf[0] = -1; if (buf[0] < 0) return 1; return 0; }"),
    ("int_overflow_wraps_negative",
      "int main() { int x = 2147483647; x = x + 1; if (x < 0) return 1; return 0; }"),
    ("negative_return_value",
      "int f() { return -1; } int main() { int r = f(); if (r < 0) return 1; return 0; }"),
    ("short_mul_negative",
      "int main() { short s = -3; int t = s * 2; if (t == -6) return 1; return 0; }")
  ]

  for (name, src) in cases do
    total := total + 1
    match ← signSuiteCompileToArm src with
    | .error e =>
        IO.eprintln s!"✗ {name}: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← signSuiteAssembleAndRun asm name
          if exitCode == 1 then
            IO.println s!"✓ {name}: exit code {exitCode} (expected 1)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ {name}: exit code {exitCode}, expected 1"
        catch e => IO.eprintln s!"✗ {name}: {e}"

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Signedness tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
