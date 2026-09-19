/-
  test/HardenTest.lean — FEL-59 (--harden runtime bounds checks) regression
  suite, and the const-qualified-typedef resolveType fix found while
  building it.

  Compiles via `CCC.compileIgnoringViolations _ _ (harden := true)`,
  assembles/links (pulling in `runtime/ccc_runtime.c`'s allocation
  registry + ccc_check_index), runs, and checks the real exit code:
  a runtime bounds violation must abort (SIGABRT, exit 134 on macOS/Linux
  via `sh`'s wait-status encoding), and a safe access must exit cleanly.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

def compileHardened (src : String) : IO (Option String) := do
  let pp ← preprocess src "."
  let result := CCC.compileIgnoringViolations pp "harden_test.c" (harden := true)
  pure result.assembly

def assembleLinkRunHardened (asm : String) (tag : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_harden_{tag}.s"
  let objPath := s!"/tmp/ccc_harden_{tag}.o"
  let binPath := s!"/tmp/ccc_harden_{tag}"
  let runtimeObj := "/tmp/ccc_harden_runtime.o"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembler error for {tag}:\n{asOut.stderr}"
  let rtOut ← IO.Process.output {
    cmd := "cc", args := #["-c", "-o", runtimeObj, "runtime/ccc_runtime.c"] }
  if rtOut.exitCode != 0 then
    throw <| IO.userError s!"runtime compile error:\n{rtOut.stderr}"
  let ccOut ← IO.Process.output {
    cmd := "cc", args := #["-o", binPath, objPath, runtimeObj, "-no-pie"] }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"linker error for {tag}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  pure runOut.exitCode

/-- SIGABRT via a plain process wait shows up as exit code 134 (128+6) on
    both macOS and Linux. -/
def expectAbort (name : String) (src : String) : IO Bool := do
  match ← compileHardened src with
  | none =>
      IO.eprintln s!"✗ {name}: --harden produced no assembly at all"
      pure false
  | some asm =>
      let code ← assembleLinkRunHardened asm name
      if code == 134 then
        IO.println s!"✓ {name}: aborted as expected (exit {code})"
        pure true
      else
        IO.eprintln s!"✗ {name}: expected abort (134), got exit {code}"
        pure false

def expectExit (name : String) (src : String) (expected : UInt32) : IO Bool := do
  match ← compileHardened src with
  | none =>
      IO.eprintln s!"✗ {name}: --harden produced no assembly at all"
      pure false
  | some asm =>
      let code ← assembleLinkRunHardened asm name
      if code == expected then
        IO.println s!"✓ {name}: exit {code} (expected {expected})"
        pure true
      else
        IO.eprintln s!"✗ {name}: exit {code}, expected {expected}"
        pure false

def main : IO UInt32 := do
  IO.println "═══ --harden runtime bounds check suite (FEL-59) ═══"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The actual DoD acceptance test: a faithful port of the libheif overlay
  -- bug, --harden'd, must abort instead of corrupting memory; a safe
  -- access through the same kind of buffer must not.
  total := total + 1
  if ← expectAbort "libheif_overlay_vulnerable_aborts"
    (← IO.FS.readFile "test/corpus/libheif-overlay-85e21ad/vulnerable.c")
  then pass := pass + 1

  total := total + 1
  if ← expectExit "libheif_overlay_fixed_runs_clean"
    (← IO.FS.readFile "test/corpus/libheif-overlay-85e21ad/fixed.c") 0
  then pass := pass + 1

  -- Direct, minimal reproductions of the two bugs found while building
  -- this: (1) the runtime check itself catching a heap overrun through a
  -- non-constant-sized malloc, and (2) the const-qualified-typedef
  -- resolveType bug (`const uint8_t *` silently used elem_size=8 instead
  -- of 1, corrupting every indexed access's address — found because it
  -- made the FIRST version of this very test fail confusingly).
  total := total + 1
  if ← expectAbort "harden_catches_heap_overrun"
    ("int main(int n) {\n" ++
     "  char *buf = malloc(n);\n" ++
     "  buf[n] = 1;\n" ++          -- one past the end: n is a valid size, index n is OOB
     "  return 0;\n}") -- n is 0 at runtime (argc-less main), so buf has size 0 and buf[0] is already OOB
  then pass := pass + 1

  total := total + 1
  if ← expectExit "harden_allows_in_bounds_access"
    ("int main() {\n" ++
     "  char *buf = malloc(4);\n" ++
     "  buf[3] = 42;\n" ++
     "  return buf[3];\n}") 42
  then pass := pass + 1

  total := total + 1
  if ← expectAbort "const_typedef_pointer_index_bug_regression"
    ("typedef unsigned char uint8_t;\n" ++
     "typedef unsigned long size_t;\n" ++
     "void *malloc(size_t size);\n" ++
     "int use(const uint8_t *p) {\n" ++
     "  return p[8];\n" ++          -- index 8 into an 8-byte buffer: OOB by exactly
     "}\n" ++                       -- one element; only detectable at elem_size=1
     "int main() {\n" ++
     "  uint8_t *buf = malloc(8);\n" ++
     "  return use(buf);\n}")
  then pass := pass + 1

  -- FEL-59 follow-up: an INTERIOR pointer (`row = p + offset; row[i];`)
  -- used to go completely unchecked -- the registry only matched an
  -- allocation's OWN starting address exactly, and `row`'s address is
  -- never itself registered. Confirmed to genuinely heap-overflow under
  -- `cc -fsanitize=address` (a real bug, not just a theoretical gap).
  -- Fixed by making the registry lookup range-based (does `row`'s
  -- address fall WITHIN some tracked allocation's byte range) instead
  -- of an exact match.
  total := total + 1
  if ← expectAbort "harden_catches_interior_pointer_overrun"
    ("int main() {\n" ++
     "  unsigned char *p = malloc(16);\n" ++
     "  unsigned char *row = p + 10;\n" ++
     "  row[10] = 1;\n" ++  -- p[20]: 4 bytes past the 16-byte allocation
     "  return 0;\n}")
  then pass := pass + 1

  -- The same interior-pointer shape, but genuinely in bounds -- must NOT
  -- be falsely flagged.
  total := total + 1
  if ← expectExit "harden_allows_interior_pointer_in_bounds"
    ("int main() {\n" ++
     "  unsigned char *p = malloc(16);\n" ++
     "  unsigned char *row = p + 10;\n" ++
     "  row[5] = 7;\n" ++  -- p[15]: last valid byte of the 16-byte allocation
     "  return row[5];\n}") 7
  then pass := pass + 1

  IO.println s!"\n═══ Results: {pass}/{total} passed ═══"
  if pass == total then
    IO.println "All --harden regression tests passed!"
    pure 0
  else
    IO.eprintln s!"{total - pass} test(s) FAILED"
    pure 1
