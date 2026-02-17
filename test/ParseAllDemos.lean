import CCC

def main : IO Unit := do
  let demos : Array String := #[
    "heartbleed_mini", "heartbleed_fixed", "buffer_overflow",
    "use_after_free", "double_free", "null_deref", "safe_server"
  ]
  for demo in demos do
    let path : String := s!"test/demo/{demo}.c"
    let source ← IO.FS.readFile path
    match CCC.parseSource source with
    | .ok prog =>
        IO.println s!"✓ {demo}.c: {prog.functions.length} functions, {prog.structs.length} structs"
    | .error e =>
        IO.println s!"✗ {demo}.c: {e}"
        IO.Process.exit 1
  IO.println "All 7 demos parsed successfully."
