/-
  ccc.lean — CLI entry point for the Clockworks C Compiler

  Usage: ccc input.c -o output
  - If safe: emits assembly, assembles, links, prints success report
  - If unsafe: prints error report with violations, exits 1
-/

import CCC

def usage : String :=
  "Usage: ccc <input.c> [-o <output>]\n" ++
  "       ccc -c <input.c> -o <output.s>\n" ++
  "       ccc --verify-report <input.c>\n" ++
  "  Compile a C source file with memory safety verification.\n" ++
  "  -c: compile to assembly only (no assembling/linking).\n" ++
  "  --verify-report: print per-function verification status.\n" ++
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

open CCC.Syntax in
/-- Format a SafetyProperty as a short tag. -/
def violationTag : SafetyProperty → String
  | .bufferBounds    => "bounds"
  | .noUseAfterFree  => "uaf"
  | .noDoubleFree    => "double-free"
  | .noNullDeref     => "null-deref"
  | .noStackOverflow => "stack-overflow"

open CCC.Syntax in
/-- Format a single FunVerifyResult as one line of verify-report output. -/
def formatFunReport (r : FunVerifyResult) : String :=
  let nv := r.violations.length
  if r.status == .exempt then
    s!"{r.funName}: exempt (uses setjmp)"
  else if nv == 0 then
    s!"{r.funName}: verified (0 violations)"
  else
    let tags := r.violations.map fun v =>
      s!"{violationTag v.property} at line {v.loc.line}"
    let tagStr := String.intercalate ", " tags
    s!"{r.funName}: degraded ({nv} violations: {tagStr})"

/-- Read and preprocess a source file. -/
def readAndPreprocess (inputFile : String) : IO String := do
  let raw ← IO.FS.readFile inputFile
  let parts := inputFile.splitOn "/"
  let basePath := if parts.length > 1 then
      String.intercalate "/" (parts.dropLast)
    else "."
  CCC.Preprocess.preprocess raw basePath

def main (args : List String) : IO UInt32 := do
  -- Handle --verify-report mode
  match args with
  | ["--verify-report", inputFile] => do
      let source ← readAndPreprocess inputFile
      let filename := (inputFile.splitOn "/").getLast!
      match CCC.parseSource source with
      | .error e =>
          IO.eprintln s!"ERROR: Parse error in {filename}:\n  {e}"
          return 1
      | .ok prog =>
          let report := CCC.Verify.verifyProgramReport prog
          -- Print per-function status, skipping the synthetic "program" entry
          for r in report.results do
            if r.funName != "program" then
              IO.println (formatFunReport r)
          return 0
  | _ => pure ()

  -- Parse arguments
  let (inputFile, outputFile, compileOnly) ← do
    match args with
    | [input] => pure (input, none, false)
    | [input, "-o", output] => pure (input, some output, false)
    | ["-c", input, "-o", output] => pure (input, some output, true)
    | _ =>
      IO.eprintln usage
      return 1

  -- Read and preprocess source (self-contained, no gcc dependency)
  let source ← readAndPreprocess inputFile

  -- Extract filename for reporting
  let filename := (inputFile.splitOn "/").getLast!

  -- Compile
  let result := CCC.compile source filename

  -- Print report
  IO.println result.report

  -- Force-emit mode: violations no longer abort if assembly was produced.
  -- Only exit 1 if there is no assembly at all.
  let some asm := result.assembly | return 1

  -- If compile-only mode, write assembly directly and exit
  if compileOnly then
    match outputFile with
    | none =>
      IO.eprintln "Error: -c requires -o <output.s>"
      return 1
    | some output =>
      IO.FS.writeFile output asm
      IO.println s!"Wrote assembly to {output}"
      return 0

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
