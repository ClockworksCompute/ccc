/-
  test/regression/DegradedGateRepro.lean
  FEL-67: a function marked `degraded` (goto back-edge, or a switch case
  that can fall through) must block `ccc` from exiting 0 unless
  `--allow-degraded` is passed, and `--verify-report` must never call
  such a function "verified".

  This exercises the actual `.lake/build/bin/ccc` CLI binary (not just the
  library-level `Verify.verifyProgramReport`), because the gate this
  regression protects lives in `Main.lean`'s argument handling, not in the
  verifier itself. Must FAIL before the FEL-67 fix, PASS after.
-/
import CCC

/-- The exact repro from FEL-43/FEL-67: a use-after-free that only
    manifests on the second trip around a hand-rolled `goto` loop. Before
    FEL-67, `ccc` exited 0 for this file (0 violations were *found* by the
    verifier — it cannot analyse goto control flow at all — and the
    `degraded` status that fact was recorded under was never checked by
    the CLI). -/
def gotoSrc : String :=
"int *p;\n" ++
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
"}\n"

def runCcc (args : List String) : IO (UInt32 × String) := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/ccc", args := args.toArray }
  pure (result.exitCode, result.stdout ++ result.stderr)

def main : IO Unit := do
  let path := "/tmp/ccc_degraded_gate_repro.c"
  IO.FS.writeFile path gotoSrc

  let mut ok := true

  -- 1. Plain `ccc <file>` (verify-only, no -o) must exit non-zero.
  let (code1, out1) ← runCcc [path]
  if code1 == 0 then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — `ccc {path}` exited 0 for a degraded (goto) function"
    ok := false
  else if !((out1.splitOn "degraded").length > 1) then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — exit was non-zero ({code1}) but output doesn't mention 'degraded':\n{out1}"
    ok := false
  else
    IO.println s!"✓ PASS  DegradedGateRepro — verify-only mode correctly exits {code1} and names 'degraded'"

  -- 2. `ccc <file> -o <out>` (the actual "would silently link an
  --    unanalysed program" case FEL-67 exists for) must also exit non-zero
  --    and must NOT produce a binary.
  let outBin := "/tmp/ccc_degraded_gate_repro_bin"
  let (code2, _out2) ← runCcc [path, "-o", outBin]
  let binExists ← System.FilePath.pathExists outBin
  if code2 == 0 || binExists then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — `ccc {path} -o {outBin}` exited {code2}, binary exists={binExists} (expected: exit≠0, no binary)"
    ok := false
  else
    IO.println s!"✓ PASS  DegradedGateRepro — `-o` mode correctly exits {code2} and produces no binary"

  -- 3. `--allow-degraded` must opt back in: exit 0 and a binary appears.
  if binExists then IO.FS.removeFile outBin
  let (code3, out3) ← runCcc ["--allow-degraded", path, "-o", outBin]
  let binExists3 ← System.FilePath.pathExists outBin
  if code3 != 0 || !binExists3 then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — `--allow-degraded` did not opt back in: exit={code3}, binary exists={binExists3}\n{out3}"
    ok := false
  else
    IO.println s!"✓ PASS  DegradedGateRepro — `--allow-degraded` opts back in (exit 0, binary produced)"
    IO.FS.removeFile outBin

  -- 4. `--verify-report` must call the function "degraded", never "verified".
  let (_code4, out4) ← runCcc ["--verify-report", path]
  if (out4.splitOn "verified").length > 1 && (out4.splitOn "degraded").length ≤ 1 then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — --verify-report still calls the goto function 'verified':\n{out4}"
    ok := false
  else if (out4.splitOn "degraded").length ≤ 1 then
    IO.eprintln s!"✗ FAIL  DegradedGateRepro — --verify-report doesn't mention 'degraded' at all:\n{out4}"
    ok := false
  else
    IO.println s!"✓ PASS  DegradedGateRepro — --verify-report correctly labels the function 'degraded'"

  IO.FS.removeFile path
  if ok then
    IO.println "✓ PASS  DegradedGateRepro — all checks passed"
  else
    IO.eprintln "✗ FAIL  DegradedGateRepro — see failures above"
    IO.Process.exit 1
