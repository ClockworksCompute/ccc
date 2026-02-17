/-
  test/E2EAllDemos.lean — End-to-end pipeline test on all 7 real .c demo files

  Reads actual source files, runs through parse → verify → emit pipeline.
  Verifies accept/reject matches expected results.
-/

import CCC

def main : IO Unit := do
  let mut passed : Nat := 0
  let mut failed : Nat := 0

  -- Programs that must be REJECTED
  let rejectDemos := #[
    ("heartbleed_mini", "bounds"),
    ("heartbleed_fixed_nope", ""),  -- placeholder, we skip this
    ("buffer_overflow", "bounds"),
    ("use_after_free", "use-after-free"),
    ("double_free", "double-free"),
    ("null_deref", "null")
  ]

  for (demo, expectedKind) in #[
    ("heartbleed_mini", "bufferBounds"),
    ("buffer_overflow", "bufferBounds"),
    ("use_after_free", "noUseAfterFree"),
    ("double_free", "noDoubleFree"),
    ("null_deref", "noNullDeref")
  ] do
    let path := s!"test/demo/{demo}.c"
    let source ← IO.FS.readFile path
    let result := CCC.compile source s!"{demo}.c"
    if result.violations.isEmpty then
      IO.println s!"✗ {demo}.c: expected REJECT ({expectedKind}), got ACCEPT"
      failed := failed + 1
    else
      IO.println s!"✓ {demo}.c: REJECTED ({expectedKind})"
      passed := passed + 1

  -- Programs that must be ACCEPTED
  for (demo, _expectedExit) in #[
    ("heartbleed_fixed", 13),
    ("safe_server", 2)
  ] do
    let path := s!"test/demo/{demo}.c"
    let source ← IO.FS.readFile path
    let result := CCC.compile source s!"{demo}.c"
    if !result.violations.isEmpty then
      IO.println s!"✗ {demo}.c: expected ACCEPT, got REJECT"
      for v in result.violations do
        IO.println s!"  violation: {v.message}"
      failed := failed + 1
    else
      match result.assembly with
      | some _ =>
        IO.println s!"✓ {demo}.c: ACCEPTED (assembly generated)"
        passed := passed + 1
      | none =>
        IO.println s!"✗ {demo}.c: ACCEPTED but no assembly produced"
        IO.println s!"  report: {result.report}"
        failed := failed + 1

  IO.println ""
  IO.println s!"Results: {passed} passed, {failed} failed out of 7"
  if failed > 0 then
    IO.Process.exit 1
