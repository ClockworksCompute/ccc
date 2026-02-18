/-
  test/HoldoutTest.lean — Run all holdout test cases through CCC pipeline
-/
import CCC

def main : IO Unit := do
  let holdoutDir := "../factory/holdout/ccc"

  -- All holdout programs and their expected results
  -- REJECT means the compiler should reject (parse error, verify error, etc.)
  -- A number means ACCEPT and expected exit code (cannot verify exit code on macOS, just check accept)
  let cases : List (String × String) := [
    -- Safe programs (should ACCEPT)
    ("fibonacci", "55"),
    ("swap_pointers", "7"),
    ("string_count", "3"),
    ("multi_alloc", "0"),
    ("nested_branches", "31"),
    ("struct_with_array", "15"),
    -- Unsafe — memory safety violations (should REJECT)
    ("alias_uaf", "REJECT"),
    ("conditional_free_uaf", "REJECT"),
    ("loop_off_by_one", "REJECT"),
    ("null_else_deref", "REJECT"),
    ("memcpy_computed_len", "REJECT"),
    ("free_stack_var", "REJECT"),
    -- Unsupported syntax (should REJECT)
    ("unsupported_float", "ACCEPT"),       -- Now supported (Phase 2: parse+verify, emit panics)
    ("unsupported_preprocessor", "REJECT"),
    ("unsupported_union_goto", "REJECT"),  -- Parses but emitter panics on goto/label
    ("unsupported_function_pointer", "ACCEPT"),  -- Now supported: parser handles function pointers
    ("unsupported_variadic", "REJECT"),
    -- Type/semantic errors (should REJECT)
    ("typerr_undeclared_var", "REJECT"),
    ("typerr_wrong_arg_count", "REJECT"),
    ("typerr_undefined_function", "ACCEPT"),  -- CCC44: not a memory safety violation; linker catches it
    ("typerr_deref_non_pointer", "REJECT"),
    ("typerr_undefined_struct", "REJECT"),
    ("typerr_bad_member_access", "REJECT"),
    ("typerr_assign_to_literal", "REJECT")
  ]

  let mut pass : Nat := 0
  let mut fail : Nat := 0
  let mut total : Nat := 0

  for (name, expected) in cases do
    total := total + 1
    let path := s!"{holdoutDir}/{name}.c"
    let fileExists ← System.FilePath.pathExists path
    if !fileExists then
      IO.println s!"✗ SKIP  {name}.c  (file not found at {path})"
      fail := fail + 1
      continue

    let source ← IO.FS.readFile path
    let result := CCC.compile source s!"{name}.c"

    if expected == "REJECT" then
      -- Should be rejected: non-empty violations OR parse/emit error with no assembly
      let rejected := !result.violations.isEmpty || result.assembly.isNone
      if rejected then
        -- Classify rejection reason
        let reason := if !result.violations.isEmpty then
          let props := result.violations.map (·.property)
          let propStrs := props.map fun p => match p with
            | .bufferBounds => "bounds"
            | .noUseAfterFree => "uaf"
            | .noDoubleFree => "double-free"
            | .noNullDeref => "null"
            | .noStackOverflow => "stack"
          s!"safety({String.intercalate "," propStrs})"
        else if (result.report.splitOn "Parse error").length > 1 then "parse-error"
        else if (result.report.splitOn "Emission error").length > 1 then "emit-error"
        else "unknown-reject"
        IO.println s!"✓ PASS  {name}.c  REJECTED  [{reason}]"
        pass := pass + 1
      else
        IO.println s!"✗ FAIL  {name}.c  should be REJECTED but was ACCEPTED"
        IO.println s!"        report: {result.report.take 200}"
        fail := fail + 1
    else
      -- Should be accepted
      if result.violations.isEmpty && result.assembly.isSome then
        IO.println s!"✓ PASS  {name}.c  ACCEPTED  (assembly generated, expected exit={expected})"
        pass := pass + 1
      else if !result.violations.isEmpty then
        IO.println s!"✗ FAIL  {name}.c  should be ACCEPTED but was REJECTED"
        for v in result.violations.take 3 do
          IO.println s!"        violation: {v.message}"
        fail := fail + 1
      else
        IO.println s!"✗ FAIL  {name}.c  should be ACCEPTED but pipeline failed"
        IO.println s!"        report: {result.report.take 200}"
        fail := fail + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Holdout results: {pass}/{total} passed, {fail} failed"
  IO.println "═══════════════════════════════════════════"
  if fail > 0 then IO.Process.exit 1
