/-
  test/JsonReportTest.lean — Machine-readable report regression tests
  (FEL-70).

  `ccc --report=json <file>` emits the same verification result as
  `--verify-report`'s prose, but as real structured JSON, so consumers
  (`scripts/corpus.sh`, the mutation fuzzer, an eventual patch-synthesis
  loop) stop scraping text meant for a terminal. Exercises the CLI
  end-to-end (shells out to the built `ccc` binary directly, matching
  `test/regression/DegradedGateRepro.lean`'s pattern) rather than calling
  `CCC.Error.programReportToJson` in-process, since the whole point is to
  test what the CLI actually prints and exits with.
-/
import CCC

def ccJson (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd := ".lake/build/bin/ccc", args := args }
  pure (out.exitCode, out.stdout)

def writeTmp (name src : String) : IO String := do
  let path := s!"/tmp/ccc_jsonreport_{name}.c"
  IO.FS.writeFile path src
  pure path

def containsStr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════"
  IO.println "  JSON report tests (FEL-70)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- A safe program: exit 0, valid JSON, summary.safe true, 0 violations.
  total := total + 1
  do
    let path ← writeTmp "safe" "int main() { return 5; }\n"
    let (code, out) ← ccJson #["--report=json", path]
    let ok := code == 0 && containsStr out "\"safe\":true" && containsStr out "\"totalViolations\":0"
    if ok then
      IO.println "✓ json_safe_program: exit 0, safe:true, 0 violations"
      pass := pass + 1
    else
      IO.eprintln s!"✗ json_safe_program: exit {code}, output: {out}"

  -- An unsafe program: exit 1, summary.safe false, violation present with
  -- a recognizable property tag and location.
  total := total + 1
  do
    let path ← writeTmp "unsafe"
      ("int main() {\n  int arr[4];\n  int i = 10;\n  arr[i] = 1;\n  return arr[i];\n}\n")
    let (code, out) ← ccJson #["--report=json", path]
    let ok := code == 1 && containsStr out "\"safe\":false" && containsStr out "\"property\":\"buffer-bounds\""
    if ok then
      IO.println "✓ json_unsafe_program: exit 1, safe:false, buffer-bounds violation present"
      pass := pass + 1
    else
      IO.eprintln s!"✗ json_unsafe_program: exit {code}, output: {out}"

  -- Output must be valid JSON parseable by an independent parser, not
  -- just string-matched — cross-checked via `python3 -m json.tool`.
  total := total + 1
  do
    let path ← writeTmp "validjson"
      ("int add(int a, int b) { return a + b; }\n" ++
       "int main() { return add(2, 3); }\n")
    let (_, out) ← ccJson #["--report=json", path]
    IO.FS.writeFile "/tmp/ccc_jsonreport_out.json" out
    let pyOut ← IO.Process.output {
      cmd := "python3", args := #["-m", "json.tool", "/tmp/ccc_jsonreport_out.json"]
    }
    if pyOut.exitCode == 0 then
      IO.println "✓ json_output_is_valid_json: python3 -m json.tool accepted it"
      pass := pass + 1
    else
      IO.eprintln s!"✗ json_output_is_valid_json: {pyOut.stderr}"

  -- A degraded function (goto) must show up with status "degraded" and
  -- a non-empty degradedReasons array, not silently look "verified".
  total := total + 1
  do
    let path ← writeTmp "degraded"
      ("int main() {\n  goto end;\n  end:\n  return 0;\n}\n")
    let (_, out) ← ccJson #["--report=json", path]
    let ok := containsStr out "\"status\":\"degraded\"" && !containsStr out "\"degradedReasons\":[]"
    if ok then
      IO.println "✓ json_degraded_function: status degraded, degradedReasons non-empty"
      pass := pass + 1
    else
      IO.eprintln s!"✗ json_degraded_function: output: {out}"

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  JSON report tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
