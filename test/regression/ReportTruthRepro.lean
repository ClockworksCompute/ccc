/-
  test/regression/ReportTruthRepro.lean
  CCC-BUG-002: Verify-only mode must NOT claim "Assembled" with a size.
  Must FAIL before fix, PASS after fix.
-/
import CCC

def main : IO Unit := do
  let src := "int main() { return 0; }"
  let result := CCC.compile src "truth_test.c"
  -- In verify-only mode: assembly is generated but no binary is linked
  -- The report should NOT contain a binary size claim
  let report := result.report
  -- Check for the misleading pattern: "Assembled: ... (NKB)" without actual linking
  let hasSizeClaim := (report.splitOn "KB)").length > 1 || (report.splitOn "B)").length > 1
  let hasAssembledWord := (report.splitOn "Assembled").length > 1
  if hasAssembledWord && hasSizeClaim then
    IO.eprintln "✗ FAIL  ReportTruthRepro — verify-only report claims binary size"
    IO.eprintln s!"  report: {report}"
    IO.Process.exit 1
  else
    IO.println "✓ PASS  ReportTruthRepro — report does not overstate evidence"
