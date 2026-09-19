/-
  test/StructLayoutTest.lean — Struct alignment and sizeof(expr) regression
  tests (FEL-68).

  Covers two emitter-completeness gaps:

  1. Struct layout previously summed field sizes with NO alignment
     padding (`struct P { char c; int x; long y; }` came out to 13 bytes
     at offsets 0/1/5), instead of the real System V AMD64 / AAPCS64
     layout: 16 bytes at offsets 0/4/8. Internally consistent for a
     CCC-to-CCC-compiled program, but wrong the moment the struct's
     memory is shared with real C code — exactly what compiling a real
     library (FEL-65's whole aim) requires. Fixed via the shared
     `CCC.Syntax.Layout` module.

  2. `sizeof(expr)` (as opposed to `sizeof(type)`) used to discard the
     parsed operand entirely and approximate the result as `sizeof(int)`
     regardless of what the operand actually was. Fixed via the new
     `Expr.sizeOfExpr` AST node, whose real size is resolved from the
     operand's inferred type.

  Compile C → AArch64 assembly (via `emitProgramAArch64`, bypassing the
  verifier — matches `SignednessTest.lean`'s pattern) → assemble → link →
  run → check exit code.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

/-- Preprocess + parse + emit via AArch64 backend (bypasses verifier). -/
def layoutCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

/-- Assemble + link + run, returning exit code. `withRuntime` links
    `runtime/ccc_runtime.c` (needed for any test using malloc/free, which
    the emitter maps to `ccc_malloc`/`ccc_free`). -/
def layoutAssembleAndRun (asm : String) (testName : String) (withRuntime : Bool := false)
    : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_layout_{testName}.s"
  let objPath := s!"/tmp/ccc_layout_{testName}.o"
  let binPath := s!"/tmp/ccc_layout_{testName}"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  if withRuntime then
    let runtimeObj := "/tmp/ccc_layout_runtime.o"
    let rtOut ← IO.Process.output
      { cmd := "cc", args := #["-c", "-o", runtimeObj, "runtime/ccc_runtime.c"] }
    if rtOut.exitCode != 0 then
      throw <| IO.userError s!"runtime compile failed:\n{rtOut.stderr}"
    let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath, runtimeObj] }
    if ccOut.exitCode != 0 then
      throw <| IO.userError s!"linker error for {testName}:\n{ccOut.stderr}"
  else
    let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath] }
    if ccOut.exitCode != 0 then
      throw <| IO.userError s!"linker error for {testName}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  pure runOut.exitCode

def expectExit (name : String) (src : String) (expected : UInt32) (withRuntime : Bool := false)
    : IO Bool := do
  match ← layoutCompileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compile error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← layoutAssembleAndRun asm name withRuntime
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
  IO.println "  Struct layout + sizeof(expr) tests (FEL-68)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The exact repro from the review: char + int + long with no explicit
  -- padding must size as 16 (aligned), not 13 (packed).
  total := total + 1
  if ← expectExit "struct_char_int_long_padded_size"
    "struct P { char c; int x; long y; };\nint main() { return sizeof(struct P); }\n"
    16
  then pass := pass + 1

  -- Cross-check: matching cc's own idea of the same struct's size (also
  -- confirms the C-interop motivation directly, not just an assertion
  -- about CCC's internal number).
  total := total + 1
  do
    let src := "struct P { char c; int x; long y; };\nint main() { return sizeof(struct P); }\n"
    match ← layoutCompileToArm src with
    | .error e => IO.eprintln s!"✗ struct_size_matches_cc: compile error: {e}"
    | .ok asm =>
        try
          let ccExitCode ← IO.Process.output
            { cmd := "sh", args := #["-c",
                "echo 'struct P { char c; int x; long y; }; int main(){return sizeof(struct P);}' | cc -x c - -o /tmp/ccc_layout_cc_ref && /tmp/ccc_layout_cc_ref; echo $?"] }
          let ccVal := (ccExitCode.stdout.trim.splitOn "\n").getLast!.trim
          let cccExit ← layoutAssembleAndRun asm "struct_size_matches_cc"
          if toString cccExit == ccVal then
            IO.println s!"✓ struct_size_matches_cc: CCC={cccExit}, cc={ccVal} (agree)"
            pass := pass + 1
          else
            IO.eprintln s!"✗ struct_size_matches_cc: CCC={cccExit}, cc={ccVal} (disagree!)"
        catch e => IO.eprintln s!"✗ struct_size_matches_cc: {e}"

  -- Field offsets must actually be correct, not just the total size:
  -- write every field, read every field back.
  total := total + 1
  if ← expectExit "struct_field_offsets_roundtrip"
    ("struct P { char c; int x; long y; };\n" ++
     "int main() {\n" ++
     "  struct P p;\n" ++
     "  p.c = 1; p.x = 2; p.y = 3;\n" ++
     "  int r = 0;\n" ++
     "  if (p.c == 1) { r = r + 1; }\n" ++
     "  if (p.x == 2) { r = r + 10; }\n" ++
     "  if (p.y == 3) { r = r + 100; }\n" ++
     "  return r;\n" ++
     "}\n")
    111
  then pass := pass + 1

  -- A struct with no padding needed at all (all 4-byte fields) must stay
  -- exactly as small as before — this change should never ADD padding
  -- that isn't required.
  total := total + 1
  if ← expectExit "struct_no_padding_needed_stays_packed"
    "struct Q { int a; int b; int c; };\nint main() { return sizeof(struct Q); }\n"
    12
  then pass := pass + 1

  -- Malloc'd-by-sizeof struct, accessed through a pointer, freed: the
  -- realistic interop pattern (allocate exactly enough, per the real
  -- ABI, for every field) that motivates this fix.
  total := total + 1
  if ← expectExit "struct_malloc_sizeof_roundtrip"
    ("struct P { char c; int x; long y; };\n" ++
     "int main() {\n" ++
     "  struct P *p = malloc(sizeof(struct P));\n" ++
     "  if (p == 0) { return 1; }\n" ++
     "  p->c = 1; p->x = 2; p->y = 3;\n" ++
     "  int r = p->c + p->x + p->y;\n" ++
     "  free(p);\n" ++
     "  return r;\n" ++
     "}\n")
    6 (withRuntime := true)
  then pass := pass + 1

  -- sizeof(expr): previously discarded and approximated as sizeof(int).
  total := total + 1
  if ← expectExit "sizeof_expr_long_variable"
    "int main() { long x = 5; return sizeof(x); }\n"
    8
  then pass := pass + 1

  total := total + 1
  if ← expectExit "sizeof_expr_char_variable"
    "int main() { char c = 5; return sizeof(c); }\n"
    1
  then pass := pass + 1

  total := total + 1
  if ← expectExit "sizeof_expr_pointer_deref"
    "int main() { int y = 1; int *p = &y; return sizeof(*p); }\n"
    4
  then pass := pass + 1

  total := total + 1
  if ← expectExit "sizeof_expr_struct_field"
    ("struct P { char c; int x; long y; };\n" ++
     "int main() { struct P p; return sizeof(p.y); }\n")
    8
  then pass := pass + 1

  -- sizeof(type) — the OTHER branch of the parser's sizeof handling —
  -- must be completely unaffected by adding the sizeof(expr) case.
  total := total + 1
  if ← expectExit "sizeof_type_unaffected"
    "int main() { return sizeof(long); }\n"
    8
  then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Struct layout tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
