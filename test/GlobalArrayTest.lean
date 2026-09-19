/-
  test/GlobalArrayTest.lean — Global array declaration and initializer
  regression tests (FEL-68).

  A top-level `int table[8];` (with or without a brace initializer) used
  to vanish from the program entirely: the parser branch for global
  arrays never once touched `pendingGlobals`, so the symbol itself was
  dropped, not merely its initial values. When such a declaration WAS
  present in a way that got registered (it wasn't, but the initializer
  parsing was independently broken too), the brace initializer was parsed
  and discarded, so the array would have come out all-zero regardless.

  Real C libraries lean heavily on this exact pattern — static lookup
  tables, CRC tables, coefficient tables — so this is a correctness gap
  of the same severity as the struct-layout and stack-argument fixes
  earlier in FEL-68, not a cosmetic one.

  Compile C → AArch64 assembly (via `emitProgramAArch64`, bypassing the
  verifier — matches `SignednessTest.lean`'s / `StructLayoutTest.lean`'s
  pattern) → assemble → link → run → check exit code. One case is also
  cross-checked directly against `cc`'s own output for the identical
  source, the strongest available confirmation this matches real ABI/
  layout behaviour, not just internal self-consistency.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

def globalArrCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

def globalArrAssembleAndRun (asm : String) (testName : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_globalarr_{testName}.s"
  let objPath := s!"/tmp/ccc_globalarr_{testName}.o"
  let binPath := s!"/tmp/ccc_globalarr_{testName}"
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
  match ← globalArrCompileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compile error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← globalArrAssembleAndRun asm name
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
  IO.println "  Global array tests (FEL-68)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The core severity check: a fully-initialized global array must
  -- exist AND carry its real values -- previously it didn't even exist.
  total := total + 1
  if ← expectExit "global_array_basic_init"
    "int table[5] = {10, 20, 30, 40, 50};\nint main() { return table[2]; }\n"
    30
  then pass := pass + 1

  -- C zero-pads any element the initializer list doesn't provide.
  total := total + 1
  if ← expectExit "global_array_zero_padded"
    "int table[5] = {1, 2};\nint main() { return table[0]+table[1]+table[2]+table[3]+table[4]; }\n"
    3
  then pass := pass + 1

  -- Byte-width elements: each must occupy exactly 1 byte in the .data
  -- section, not the uniform word/quad width an earlier, wrong version
  -- of this fix would have used.
  total := total + 1
  if ← expectExit "global_array_char_width"
    "char bytes[4] = {5, 10, 15, 20};\nint main() { return bytes[0]+bytes[1]+bytes[2]+bytes[3]; }\n"
    50
  then pass := pass + 1

  -- A bare (uninitialized) global array declaration must still register
  -- a real symbol with the right size (BSS), not vanish.
  total := total + 1
  if ← expectExit "global_array_uninitialized_declares_symbol"
    "int table[3];\nint main() { table[0]=7; table[1]=8; table[2]=9; return table[0]+table[1]+table[2]; }\n"
    24
  then pass := pass + 1

  -- Accessed through a separate function taking a runtime index (not
  -- just a compile-time-constant subscript in main), and using `short`
  -- (2-byte) elements -- exercises the general load path, not just
  -- literal-index codegen.
  total := total + 1
  if ← expectExit "global_array_short_width_runtime_index"
    ("short vals[6] = {100, 200, 300, 400, 500, 600};\n" ++
     "int lookup(int i) { return vals[i]; }\n" ++
     "int main() { return lookup(0) + lookup(3) - lookup(5); }\n")
    156
  then pass := pass + 1

  -- Cross-check directly against `cc` compiling the IDENTICAL source:
  -- the strongest available confirmation this isn't merely
  -- self-consistent but actually matches real layout/initializer
  -- behaviour.
  total := total + 1
  do
    let src := "short vals[6] = {100, 200, 300, 400, 500, 600};\n" ++
               "int lookup(int i) { return vals[i]; }\n" ++
               "int main() { return lookup(0) + lookup(3) - lookup(5); }\n"
    match ← globalArrCompileToArm src with
    | .error e => IO.eprintln s!"✗ global_array_matches_cc: compile error: {e}"
    | .ok asm =>
        try
          let cccExit ← globalArrAssembleAndRun asm "global_array_matches_cc"
          let srcPath := "/tmp/ccc_globalarr_cc_ref.c"
          let ccBin := "/tmp/ccc_globalarr_cc_ref_bin"
          IO.FS.writeFile srcPath src
          let ccCompile ← IO.Process.output { cmd := "cc", args := #["-o", ccBin, srcPath] }
          if ccCompile.exitCode != 0 then
            IO.eprintln s!"✗ global_array_matches_cc: cc failed to compile the reference:\n{ccCompile.stderr}"
          else
            let ccRun ← IO.Process.output { cmd := ccBin, args := #[] }
            if cccExit == ccRun.exitCode then
              IO.println s!"✓ global_array_matches_cc: CCC={cccExit}, cc={ccRun.exitCode} (agree)"
              pass := pass + 1
            else
              IO.eprintln s!"✗ global_array_matches_cc: CCC={cccExit}, cc={ccRun.exitCode} (disagree!)"
        catch e => IO.eprintln s!"✗ global_array_matches_cc: {e}"

  -- Existing scalar global initializer path (int x = 5;) must be
  -- completely unaffected.
  total := total + 1
  if ← expectExit "global_scalar_unaffected"
    "int counter = 42;\nint main() { return counter; }\n"
    42
  then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Global array tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
