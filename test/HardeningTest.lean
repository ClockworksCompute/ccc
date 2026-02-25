/-
  test/HardeningTest.lean — Emitter hardening tests

  Tests: global variables, force-emit through violations, extern function calls.
  Compile C → AArch64 assembly → assemble → link → run → check exit code.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

/-- Preprocess + parse + emit via AArch64 backend (bypasses verifier for globals) -/
def compileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

/-- Compile via full pipeline (parse → verify → force-emit) -/
def compileViaPipeline (src : String) : IO (Option String × Nat) := do
  let pp ← preprocess src "."
  let result := CCC.compile pp "test.c"
  pure (result.assembly, result.violations.length)

/-- Assemble + link + run, returning exit code -/
def assembleAndRun (asm : String) (testName : String) (withRuntime : Bool := false)
    : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_hard_{testName}.s"
  let objPath := s!"/tmp/ccc_hard_{testName}.o"
  let binPath := s!"/tmp/ccc_hard_{testName}"
  IO.FS.writeFile asmPath asm
  -- Assemble
  let asOut ← IO.Process.output {
    cmd := "as"
    args := #["-o", objPath, asmPath]
  }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  -- Link (optionally with runtime for malloc/free)
  if withRuntime then
    let rtOut ← IO.Process.output {
      cmd := "cc"
      args := #["-c", "-o", "/tmp/ccc_hard_runtime.o", "runtime/ccc_runtime.c"]
    }
    if rtOut.exitCode != 0 then
      throw <| IO.userError s!"runtime compile failed:\n{rtOut.stderr}"
    let ccOut ← IO.Process.output {
      cmd := "cc"
      args := #["-o", binPath, objPath, "/tmp/ccc_hard_runtime.o"]
    }
    if ccOut.exitCode != 0 then
      throw <| IO.userError s!"link failed for {testName}:\n{ccOut.stderr}"
  else
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

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  IO.println "═══════════════════════════════════════════"
  IO.println "  Emitter Hardening Tests"
  IO.println "═══════════════════════════════════════════"

  -- ═══════════════════════════════════════════
  -- T1: Global variable (initialized)
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int g = 42;\nint main() { return g; }"
    match ← compileToArm src with
    | .error e =>
        IO.eprintln s!"✗ T1_global_var: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← assembleAndRun asm "T1_global_var"
          if exitCode == 42 then
            IO.println s!"✓ T1_global_var: exit code {exitCode} (expected 42)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T1_global_var: exit code {exitCode}, expected 42"
        catch e => IO.eprintln s!"✗ T1_global_var: {e}"

  -- ═══════════════════════════════════════════
  -- T2: Global + function
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int counter = 0;\nvoid inc() { counter = counter + 1; }\nint main() { inc(); inc(); inc(); return counter; }"
    match ← compileToArm src with
    | .error e =>
        IO.eprintln s!"✗ T2_global_func: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← assembleAndRun asm "T2_global_func"
          if exitCode == 3 then
            IO.println s!"✓ T2_global_func: exit code {exitCode} (expected 3)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T2_global_func: exit code {exitCode}, expected 3"
        catch e => IO.eprintln s!"✗ T2_global_func: {e}"

  -- ═══════════════════════════════════════════
  -- T3: printf via force-emit (verifier reports violations, still emits)
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int printf(const char *fmt);\nint main() { printf(\"hello\\n\"); return 0; }"
    let (asmOpt, nViolations) ← compileViaPipeline src
    match asmOpt with
    | some asm =>
        try
          let exitCode ← assembleAndRun asm "T3_printf_force"
          if exitCode == 0 then
            IO.println s!"✓ T3_printf_force: exit code {exitCode} (expected 0), violations={nViolations} (force-emit OK)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T3_printf_force: exit code {exitCode}, expected 0"
        catch e => IO.eprintln s!"✗ T3_printf_force: {e}"
    | none =>
        IO.eprintln s!"✗ T3_printf_force: no assembly produced (force-emit failed)"

  -- ═══════════════════════════════════════════
  -- T4: malloc + struct arrow via force-emit
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "struct Node { int val; int pad; };\nint main() {\n    struct Node *n = malloc(16);\n    n->val = 42;\n    int r = n->val;\n    free(n);\n    return r;\n}"
    let (asmOpt, nViolations) ← compileViaPipeline src
    match asmOpt with
    | some asm =>
        try
          let exitCode ← assembleAndRun asm "T4_malloc_force" (withRuntime := true)
          if exitCode == 42 then
            IO.println s!"✓ T4_malloc_force: exit code {exitCode} (expected 42), violations={nViolations} (force-emit OK)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T4_malloc_force: exit code {exitCode}, expected 42"
        catch e => IO.eprintln s!"✗ T4_malloc_force: {e}"
    | none =>
        IO.eprintln s!"✗ T4_malloc_force: no assembly produced (force-emit failed)"

  -- ═══════════════════════════════════════════
  -- T5: String literal + puts
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int puts(const char *s);\nint main() { puts(\"world\"); return 0; }"
    match ← compileToArm src with
    | .error e =>
        IO.eprintln s!"✗ T5_puts: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← assembleAndRun asm "T5_puts"
          if exitCode == 0 then
            IO.println s!"✓ T5_puts: exit code {exitCode} (expected 0)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T5_puts: exit code {exitCode}, expected 0"
        catch e => IO.eprintln s!"✗ T5_puts: {e}"

  -- ═══════════════════════════════════════════
  -- T6: Uninitialized global (BSS)
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int x;\nint main() { x = 99; return x; }"
    match ← compileToArm src with
    | .error e =>
        IO.eprintln s!"✗ T6_bss_global: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← assembleAndRun asm "T6_bss_global"
          if exitCode == 99 then
            IO.println s!"✓ T6_bss_global: exit code {exitCode} (expected 99)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T6_bss_global: exit code {exitCode}, expected 99"
        catch e => IO.eprintln s!"✗ T6_bss_global: {e}"

  -- ═══════════════════════════════════════════
  -- T7: Force-emit produces assembly despite violations
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    -- This program triggers null-deref warnings from the verifier
    let src := "int main() { int *p = malloc(8); *p = 7; int r = *p; free(p); return r; }"
    let (asmOpt, nViolations) ← compileViaPipeline src
    match asmOpt with
    | some _ =>
        IO.println s!"✓ T7_force_emit_check: assembly produced with {nViolations} violation(s) (force-emit OK)"
        pass := pass + 1
    | none =>
        IO.eprintln s!"✗ T7_force_emit_check: no assembly produced (force-emit failed)"

  -- ═══════════════════════════════════════════
  -- T8: Multiple globals
  -- ═══════════════════════════════════════════
  total := total + 1
  do
    let src := "int a = 10;\nint b = 20;\nint c = 12;\nint main() { return a + b + c; }"
    match ← compileToArm src with
    | .error e =>
        IO.eprintln s!"✗ T8_multi_globals: compile error: {e}"
    | .ok asm =>
        try
          let exitCode ← assembleAndRun asm "T8_multi_globals"
          if exitCode == 42 then
            IO.println s!"✓ T8_multi_globals: exit code {exitCode} (expected 42)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ T8_multi_globals: exit code {exitCode}, expected 42"
        catch e => IO.eprintln s!"✗ T8_multi_globals: {e}"

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Hardening tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
