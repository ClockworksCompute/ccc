/-
  test/EnumResolveTest.lean — Enum constant resolution regression tests
  (FEL-68).

  `enum Color { RED, GREEN, BLUE };` was parsed and its member values
  correctly computed into `Program.enums`, but nothing ever consulted
  that table when a member NAME was used as an expression: `RED` parses
  as a plain `Expr.var "RED"`, the same node an ordinary (nonexistent)
  variable reference produces, so any use of an enum constant by name
  failed emission outright with "unknown variable 'RED'". This is a
  HARD, immediate compile failure for essentially any real C header that
  declares an enum and uses a member anywhere — enums are everywhere in
  real code (error codes, flags, state machines) — unlike several of the
  other FEL-68 gaps, which produced silently wrong values rather than an
  outright failure to compile.

  Fixed by `CCC.Syntax.EnumResolve`, a post-parse AST rewrite run
  automatically at the end of `Parse.parseProgram`. Compile C → AArch64
  assembly (via `emitProgramAArch64`, bypassing the verifier — matches
  the pattern of the other FEL-68 test files) → assemble → link → run →
  check exit code. The explicit-value/auto-increment-resume case is also
  cross-checked directly against `cc` compiling the identical source.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

def enumCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

def enumAssembleAndRun (asm : String) (testName : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_enum_{testName}.s"
  let objPath := s!"/tmp/ccc_enum_{testName}.o"
  let binPath := s!"/tmp/ccc_enum_{testName}"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath] }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"linker error for {testName}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  pure runOut.exitCode

def expectExit (name : String) (src : String) (expected : UInt32) : IO Bool := do
  match ← enumCompileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compile error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← enumAssembleAndRun asm name
        if exitCode == expected then
          IO.println s!"✓ {name}: exit code {exitCode} (expected {expected})"
          pure true
        else
          IO.eprintln s!"✗ {name}: exit code {exitCode}, expected {expected}"
          pure false
      catch e =>
        IO.eprintln s!"✗ {name}: {e}"
        pure false

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════"
  IO.println "  Enum constant resolution tests (FEL-68)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The core severity check: using a bare enum constant as an expression
  -- used to be a hard "unknown variable" compile failure.
  total := total + 1
  if ← expectExit "enum_bare_constant"
    "enum Color { RED, GREEN, BLUE };\nint main() { return RED; }\n"
    0
  then pass := pass + 1

  -- Default auto-increment: members with no explicit value count up from 0.
  total := total + 1
  if ← expectExit "enum_default_autoincrement"
    "enum Color { RED, GREEN, BLUE };\nint main() { return BLUE; }\n"
    2
  then pass := pass + 1

  -- Assigned to a variable and compared -- the general "used as an
  -- ordinary int expression" pattern.
  total := total + 1
  if ← expectExit "enum_var_and_compare"
    ("enum Color { RED, GREEN, BLUE };\n" ++
     "int main() {\n  enum Color c = GREEN;\n  if (c == BLUE) { return 99; }\n  return c;\n}\n")
    1
  then pass := pass + 1

  -- Explicit values AND the "auto-increment resumes from the explicit
  -- value" rule in the same enum -- the case most likely to be gotten
  -- subtly wrong.
  total := total + 1
  if ← expectExit "enum_explicit_and_resume"
    "enum E { A, B = 10, C, D = 20, F };\nint main() { return A + B + C + D + F; }\n"
    62
  then pass := pass + 1

  -- Cross-check directly against `cc` compiling the identical source.
  total := total + 1
  do
    let src := "enum E { A, B = 10, C, D = 20, F };\nint main() { return A + B + C + D + F; }\n"
    match ← enumCompileToArm src with
    | .error e => IO.eprintln s!"✗ enum_matches_cc: compile error: {e}"
    | .ok asm =>
        try
          let cccExit ← enumAssembleAndRun asm "enum_matches_cc"
          let srcPath := "/tmp/ccc_enum_cc_ref.c"
          let ccBin := "/tmp/ccc_enum_cc_ref_bin"
          IO.FS.writeFile srcPath src
          let ccCompile ← IO.Process.output { cmd := "cc", args := #["-o", ccBin, srcPath] }
          if ccCompile.exitCode != 0 then
            IO.eprintln s!"✗ enum_matches_cc: cc failed to compile the reference:\n{ccCompile.stderr}"
          else
            let ccRun ← IO.Process.output { cmd := ccBin, args := #[] }
            if cccExit == ccRun.exitCode then
              IO.println s!"✓ enum_matches_cc: CCC={cccExit}, cc={ccRun.exitCode} (agree)"
              pass := pass + 1
            else
              IO.eprintln s!"✗ enum_matches_cc: CCC={cccExit}, cc={ccRun.exitCode} (disagree!)"
        catch e => IO.eprintln s!"✗ enum_matches_cc: {e}"

  -- An enum constant used as a global initializer, and as a function
  -- argument -- the rewrite must reach global declarations too, not
  -- just function bodies.
  total := total + 1
  if ← expectExit "enum_in_global_init_and_call_arg"
    ("enum Level { LOW, MEDIUM, HIGH };\n" ++
     "int level = HIGH;\n" ++
     "int identity(int x) { return x; }\n" ++
     "int main() { return level + identity(MEDIUM); }\n")
    3
  then pass := pass + 1

  -- A plain, no-enum program must be completely unaffected (the
  -- `table.isEmpty` fast path).
  total := total + 1
  if ← expectExit "no_enum_unaffected" "int main() { return 5; }\n" 5
  then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Enum resolution tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
