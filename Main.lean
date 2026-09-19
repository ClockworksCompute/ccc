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
  "       ccc --harden <input.c> -o <output>\n" ++
  "  Compile a C source file with memory safety verification.\n" ++
  "  -c: compile to assembly only (no assembling/linking).\n" ++
  "  --verify-report: print per-function verification status.\n" ++
  "  --harden: EXPERIMENTAL (FEL-59, in progress). Emit a binary even when\n" ++
  "    the verifier finds violations it cannot clear, with a loud warning\n" ++
  "    naming exactly what was not proven. Exit code stays 0. As of this\n" ++
  "    build, every `base[index]` subscript through a pointer-typed base\n" ++
  "    (a heap allocation or a parameter) gets a runtime bounds check,\n" ++
  "    against a size registry populated by ccc_malloc/ccc_calloc, and\n" ++
  "    aborts instead of corrupting memory when it fires. That check only\n" ++
  "    protects an access whose base is exactly a tracked allocation's own\n" ++
  "    pointer VALUE — the registry does an exact-address match, so ANY\n" ++
  "    pointer arithmetic in between (`row = p + y*stride; row[x]`) yields\n" ++
  "    an untracked address and the check silently no-ops for it. Also NOT\n" ++
  "    covered at all: struct field arrow/dot access, and bare pointer\n" ++
  "    dereference (`*p`). All of those stay exactly as unprotected as\n" ++
  "    without --harden. Do not treat this as a complete hardening mode.\n" ++
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
  | .noDivByZero     => "div-by-zero"

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

  -- Strip an optional leading `--harden` flag before the usual argument
  -- shapes (FEL-59, experimental — see the `usage` docstring above for
  -- exactly what this does and does not do today).
  let (harden, args) := match args with
    | "--harden" :: rest => (true, rest)
    | _ => (false, args)

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

  -- Compile. `--harden` uses the explicit force-emit escape hatch instead
  -- of the safe default (see FEL-40/FEL-59) and prints a loud disclaimer
  -- whenever it actually needed to.
  let result := if harden then CCC.compileIgnoringViolations source filename harden
                else CCC.compile source filename

  -- Print report
  IO.println result.report
  if harden && !result.violations.isEmpty then
    IO.println ""
    IO.println "⚠️  --harden: emitting despite unproven access(es) above."
    IO.println "⚠️  Index subscripts through a base that is exactly a tracked"
    IO.println "⚠️  malloc/calloc pointer VALUE get a real runtime bounds"
    IO.println "⚠️  check and will abort rather than corrupt memory. Everything"
    IO.println "⚠️  else — pointer arithmetic before the subscript, struct"
    IO.println "⚠️  field access, bare `*p` dereference, or a base the"
    IO.println "⚠️  registry never saw — is NOT checked (FEL-59 is not"
    IO.println "⚠️  finished) and can still misbehave exactly like an"
    IO.println "⚠️  unverified C program. Do not treat this as a safe binary."

  -- FEL-40: `CCC.compile` never produces assembly for a program with
  -- violations (parse error, verification failure, or emission error all
  -- leave `assembly := none`), so this is now a plain, correct gate: no
  -- assembly means nothing further should happen and `ccc` must exit
  -- non-zero. (Earlier versions force-emitted despite violations and only
  -- checked for assembly's mere presence, so a rejected program could still
  -- exit 0 — see FEL-40.)
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
