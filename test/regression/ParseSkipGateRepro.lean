/-
  test/regression/ParseSkipGateRepro.lean
  FEL-55/FEL-65 epic DoD bullet 7 follow-up: a top-level construct the
  parser could not parse (and silently skipped via `skipToTopLevel`)
  must block `ccc` from exiting 0 unless `--allow-degraded` is passed,
  and every report mode must say so explicitly rather than only ever
  reporting on the functions that DID parse.

  This exercises the actual `.lake/build/bin/ccc` CLI binary, since the
  gate lives in `Main.lean`'s argument handling, not the verifier or
  parser themselves. Must FAIL before this fix, PASS after.
-/
import CCC

/-- Three ordinary functions, one of which uses `_Atomic` — a keyword
    this parser's expression/declaration grammar doesn't recognize,
    so `parseFunDefOrProtoSafe` fails on it and the recovery path
    (`skipToTopLevel`) silently drops it entirely. Before this fix,
    `ccc` reported "3 functions analyzed... Verified" for this file —
    correct about the 3 it saw, but with no indication a 4th function
    existed at all. -/
def skipSrc : String :=
"int good_fn(int x) { return x + 1; }\n" ++
"_Atomic int bad_fn(int y) { return y; }\n" ++
"int also_good(int z) { return z * 2; }\n" ++
"int main() { return good_fn(1) + also_good(2); }\n"

def runCcc (args : List String) : IO (UInt32 × String) := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/ccc", args := args.toArray }
  pure (result.exitCode, result.stdout ++ result.stderr)

def containsStr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def main : IO Unit := do
  let path := "/tmp/ccc_parse_skip_gate_repro.c"
  IO.FS.writeFile path skipSrc

  let mut ok := true

  -- 1. Plain `ccc <file>` (verify-only, no -o) must exit non-zero and
  --    name what was SKIPPED.
  let (code1, out1) ← runCcc [path]
  if code1 == 0 then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — `ccc {path}` exited 0 despite a skipped top-level construct"
    ok := false
  else if !((out1.splitOn "SKIPPED").length > 1) then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — exit was non-zero ({code1}) but output doesn't mention 'SKIPPED':\n{out1}"
    ok := false
  else
    IO.println s!"✓ PASS  ParseSkipGateRepro — verify-only mode correctly exits {code1} and names what was SKIPPED"

  -- 2. `ccc <file> -o <out>` must also exit non-zero and NOT produce a
  --    binary — the exact "would silently link an unanalysed function"
  --    case this gate exists for.
  let outBin := "/tmp/ccc_parse_skip_gate_repro_bin"
  let (code2, _out2) ← runCcc [path, "-o", outBin]
  let binExists ← System.FilePath.pathExists outBin
  if code2 == 0 || binExists then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — `ccc {path} -o {outBin}` exited {code2}, binary exists={binExists} (expected: exit≠0, no binary)"
    ok := false
  else
    IO.println s!"✓ PASS  ParseSkipGateRepro — `-o` mode correctly exits {code2} and produces no binary"

  -- 3. `--allow-degraded` must opt back in: exit 0, binary appears.
  if binExists then IO.FS.removeFile outBin
  let (code3, out3) ← runCcc ["--allow-degraded", path, "-o", outBin]
  let binExists3 ← System.FilePath.pathExists outBin
  if code3 != 0 || !binExists3 then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — `--allow-degraded` did not opt back in: exit={code3}, binary exists={binExists3}\n{out3}"
    ok := false
  else
    IO.println s!"✓ PASS  ParseSkipGateRepro — `--allow-degraded` opts back in (exit 0, binary produced)"
    IO.FS.removeFile outBin

  -- 4. `--verify-report` must mention the skip explicitly, not just
  --    silently list the 3 functions that DID parse.
  let (_code4, out4) ← runCcc ["--verify-report", path]
  if !((out4.splitOn "could not be parsed").length > 1) then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — --verify-report doesn't mention the skipped construct:\n{out4}"
    ok := false
  else
    IO.println s!"✓ PASS  ParseSkipGateRepro — --verify-report mentions the skipped construct"

  -- 5. `--report=json` must include a non-empty `parseWarnings` array
  --    and `summary.safe: false`, even though every function that DID
  --    parse is individually "verified" with 0 violations.
  let (code5, out5) ← runCcc ["--report=json", path]
  let hasWarnings : Bool := !containsStr out5 "\"parseWarnings\":[]"
  let safeFalse : Bool := containsStr out5 "\"safe\":false"
  if code5 == 0 || !hasWarnings || !safeFalse then
    IO.eprintln s!"✗ FAIL  ParseSkipGateRepro — --report=json: exit={code5}\n{out5}"
    ok := false
  else
    IO.println s!"✓ PASS  ParseSkipGateRepro — --report=json: exit 1, non-empty parseWarnings, safe:false"

  IO.FS.removeFile path
  if ok then
    IO.println "✓ PASS  ParseSkipGateRepro — all checks passed"
  else
    IO.eprintln "✗ FAIL  ParseSkipGateRepro — see failures above"
    IO.Process.exit 1
