/-
  ccc.lean — CLI entry point for the Clockworks C Compiler

  Usage: ccc input.c -o output
  - If safe: emits assembly, assembles, links, prints success report
  - If unsafe: prints error report with violations, exits 1
-/

import CCC

def usage : String :=
  "Usage: ccc <input.c> [-o <output>]\n" ++
  "  Compile a C source file with memory safety verification.\n" ++
  "  If no -o specified, only verify (no assembly/linking)."

/-- Find the runtime source file relative to the executable. -/
def findRuntimeSource : IO String := do
  -- Try several locations
  let candidates := #[
    "runtime/ccc_runtime.c",
    "ccc/runtime/ccc_runtime.c",
    "../runtime/ccc_runtime.c"
  ]
  for path in candidates do
    if ← System.FilePath.pathExists path then
      return path
  throw <| IO.Error.userError "Cannot find ccc_runtime.c"

/-- Check if a command is available. -/
def commandExists (cmd : String) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "which"
    args := #[cmd]
  }
  return result.exitCode == 0

def main (args : List String) : IO UInt32 := do
  -- Parse arguments
  let (inputFile, outputFile) ← do
    match args with
    | [input] => pure (input, none)
    | [input, "-o", output] => pure (input, some output)
    | _ =>
      IO.eprintln usage
      return 1

  -- Read source
  let source ← IO.FS.readFile inputFile

  -- Extract filename for reporting
  let filename := (inputFile.splitOn "/").getLast!

  -- Compile
  let result := CCC.compile source filename

  -- Print report
  IO.println result.report

  -- If violations found, exit 1
  if !result.violations.isEmpty then
    return 1

  -- If no assembly produced (parse error, emit error), exit 1
  let some asm := result.assembly | return 1

  -- If output requested, assemble and link
  match outputFile with
  | none =>
    IO.println "\n(Verify-only mode: no output binary. Use -o to produce binary.)"
    return 0
  | some output => do
    -- Check for assembler/linker
    let hasAs ← commandExists "as"
    let hasGcc ← commandExists "gcc"
    if !hasAs || !hasGcc then
      IO.eprintln "Warning: 'as' or 'gcc' not found. Writing assembly to stdout."
      IO.println asm
      return 0

    -- Write assembly to temp file
    let tmpAsm := s!"/tmp/ccc_{filename}.s"
    let tmpObj := s!"/tmp/ccc_{filename}.o"
    IO.FS.writeFile tmpAsm asm

    -- Assemble
    let asResult ← IO.Process.output {
      cmd := "as"
      args := #["-o", tmpObj, tmpAsm]
    }
    if asResult.exitCode != 0 then
      IO.eprintln s!"Assembler error:\n{asResult.stderr}"
      return 1

    -- Compile runtime
    let runtimeSrc ← findRuntimeSource
    let runtimeObj := "/tmp/ccc_runtime.o"
    let gccRt ← IO.Process.output {
      cmd := "gcc"
      args := #["-c", "-o", runtimeObj, runtimeSrc]
    }
    if gccRt.exitCode != 0 then
      IO.eprintln s!"Runtime compilation error:\n{gccRt.stderr}"
      return 1

    -- Link
    let linkResult ← IO.Process.output {
      cmd := "gcc"
      args := #["-o", output, tmpObj, runtimeObj, "-no-pie"]
    }
    if linkResult.exitCode != 0 then
      IO.eprintln s!"Linker error:\n{linkResult.stderr}"
      return 1

    return 0
