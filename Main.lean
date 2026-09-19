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
  "       ccc --report=json <input.c>\n" ++
  "       ccc [--harden] [--allow-degraded] <input.c> -o <output>\n" ++
  "  Compile a C source file with memory safety verification.\n" ++
  "  -c: compile to assembly only (no assembling/linking).\n" ++
  "  --verify-report: print per-function verification status.\n" ++
  "  --report=json: print the same verification result as one line of\n" ++
  "    JSON ({file, functions: [{name, status, violations, degradedReasons}],\n" ++
  "    parseWarnings: [{message, loc}], summary: {totalFunctions, verified,\n" ++
  "    degraded, exempt, totalViolations, safe}}) for programmatic consumers\n" ++
  "    instead of the prose report. Exits 0 iff `summary.safe` is true.\n" ++
  "  --allow-degraded: by default, ccc refuses to emit (exits 1) when any\n" ++
  "    function was analysed with reduced precision (`degraded`: it uses\n" ++
  "    goto/labels, or has a switch case that can fall through), had\n" ++
  "    verification SKIPPED ENTIRELY (`exempt`: it calls setjmp), OR when\n" ++
  "    a top-level construct could not be parsed at all and was silently\n" ++
  "    dropped — even if zero violations were found in what could be\n" ++
  "    analysed. None of these were proven memory-safe, and treating any\n" ++
  "    of them the same as a fully verified program would be dishonest.\n" ++
  "    Pass this flag to emit anyway; exactly what was degraded, exempt,\n" ++
  "    or skipped (and why) is still printed.\n" ++
  "  --harden: EXPERIMENTAL (FEL-59, in progress). Emit a binary even when\n" ++
  "    the verifier finds violations it cannot clear, with a loud warning\n" ++
  "    naming exactly what was not proven. Exit code stays 0. As of this\n" ++
  "    build, every `base[index]` subscript through a pointer-typed base\n" ++
  "    (a heap allocation or a parameter) gets a runtime bounds check,\n" ++
  "    against a size registry populated by ccc_malloc/ccc_calloc, and\n" ++
  "    aborts instead of corrupting memory when it fires. The registry\n" ++
  "    lookup is RANGE-based, so an interior pointer produced by pointer\n" ++
  "    arithmetic (`row = p + y*stride; row[x]`) is checked too, not just\n" ++
  "    an exact match on a tracked allocation's own starting address. NOT\n" ++
  "    covered at all: struct field arrow/dot access, bare pointer\n" ++
  "    dereference (`*p`), and a negative index through an interior\n" ++
  "    pointer that would still land inside the same allocation. All of\n" ++
  "    those stay exactly as unprotected as without --harden. Do not\n" ++
  "    treat this as a complete hardening mode.\n" ++
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
/-- The reason(s) a function is `degraded`, from its `degradedBy`
    evidence (see `Verify.verifyFunction`). -/
def degradeReasons (r : FunVerifyResult) : List String :=
  r.evidence.filterMap fun e =>
    match e with
    | .degradedBy _feature reason loc => some s!"{reason} (line {loc.line})"
    | _ => none

open CCC.Syntax in
/-- Format a single FunVerifyResult as one line of verify-report output.
    FEL-67: status (verified/degraded/exempt) and violation count are two
    separate axes — a function can be `degraded` (goto, or a
    fall-through switch case) with zero violations, and that must not be
    reported as plain "verified (0 violations)", which is what this used
    to do (it only ever checked `.exempt`, and otherwise treated "zero
    violations" as synonymous with "fully verified"). -/
def formatFunReport (r : FunVerifyResult) : String :=
  let nv := r.violations.length
  let violationStr :=
    if nv == 0 then "0 violations"
    else
      let tags := r.violations.map fun v => s!"{violationTag v.property} at line {v.loc.line}"
      s!"{nv} violations: {String.intercalate ", " tags}"
  if r.status == .exempt then
    s!"{r.funName}: exempt (uses setjmp) [{violationStr}]"
  else if r.status == .degraded then
    let reasons := degradeReasons r
    let reasonStr := if reasons.isEmpty then "reduced analysis precision"
      else String.intercalate "; " reasons
    s!"{r.funName}: degraded ({reasonStr}) — not fully proven memory-safe [{violationStr}]"
  else if nv == 0 then
    s!"{r.funName}: verified (0 violations)"
  else
    s!"{r.funName}: unsafe ({violationStr})"

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
          -- FEL-55/FEL-65 epic DoD bullet 7 follow-up: this report is
          -- only ever about what parsed — say so explicitly when
          -- something didn't.
          if !prog.parseWarnings.isEmpty then
            IO.println ""
            IO.println s!"⚠ {prog.parseWarnings.length} top-level construct(s) could not be parsed and are NOT included above:"
            for (msg, loc) in prog.parseWarnings do
              IO.println s!"  at {loc.line}:{loc.col}: {msg}"
          return 0
  | ["--report=json", inputFile] => do
      -- FEL-70: structured output for programmatic consumers (corpus.sh,
      -- the mutation fuzzer, an eventual patch-synthesis loop) instead of
      -- scraping the prose report meant for a terminal.
      let filename := (inputFile.splitOn "/").getLast!
      let source ← readAndPreprocess inputFile
      match CCC.parseSource source with
      | .error e =>
          let errJson := Lean.Json.mkObj [
            ("file", Lean.Json.str filename),
            ("parseError", Lean.Json.str e)
          ]
          IO.println errJson.compress
          return 1
      | .ok prog =>
          let report := CCC.Verify.verifyProgramReport prog
          let reportJson := CCC.Error.programReportToJson filename report prog.parseWarnings
          IO.println reportJson.compress
          return (if CCC.Error.isFullyVerified report prog.parseWarnings then 0 else 1)
  | _ => pure ()

  -- Strip any leading `--harden` / `--allow-degraded` flags, in either
  -- order, before the usual positional argument shapes are parsed. See
  -- the `usage` docstring above for exactly what each one does.
  let rec stripFlags (harden allowDegraded : Bool) (a : List String)
      : Bool × Bool × List String :=
    match a with
    | "--harden" :: rest => stripFlags true allowDegraded rest
    | "--allow-degraded" :: rest => stripFlags harden true rest
    | _ => (harden, allowDegraded, a)
  let (harden, allowDegraded, args) := stripFlags false false args

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

  -- FEL-67 (extended, FEL-65 epic DoD bullet 7: "never call a skipped
  -- function verified"): a `degraded` function (goto/labels, or a switch
  -- case that can fall through) was analysed with reduced precision and
  -- was NOT proven memory-safe; an `exempt` function (setjmp, varargs) had
  -- verification SKIPPED ENTIRELY -- strictly worse than degraded, not
  -- milder. Both used to be invisible here: `--verify-report` printed
  -- "verified (0 violations)" for either, the FEL-67 gate below originally
  -- only checked `.degraded` (added FEL-67; `.exempt` was left out, an
  -- oversight this closes), and the top-level success banner
  -- (`Report.formatSuccess`) says "Verified: <name> (assembly generated)"
  -- unconditionally whenever there happen to be zero violations, with no
  -- awareness of status at all -- so an exempt function's caller still saw
  -- the whole program pronounced "Verified". Block both by default, the
  -- same way an actual violation blocks; `--allow-degraded` opts into
  -- BOTH (there is no finer-grained flag yet -- a real distinction
  -- between "reduced precision but attempted" and "skipped outright"
  -- would need a second flag, left for whenever that granularity is
  -- actually requested rather than added speculatively here).
  -- FEL-67/FEL-55 (FEL-65 epic DoD bullet 7, "never call a skipped
  -- function verified"): three ways a report can be less complete than
  -- it looks, all gated under the same `--allow-degraded` lever (there
  -- is no finer-grained flag yet) and all reported TOGETHER when more
  -- than one applies, rather than only whichever is checked first --
  -- a caller fixing one must not be surprised by a second still-hidden
  -- issue on the next run.
  --   - `degraded`: analysed, but with reduced precision (goto, a
  --     switch case that can fall through) -- NOT proven memory-safe.
  --   - `exempt`: verification SKIPPED ENTIRELY (setjmp, varargs) --
  --     worse than degraded, not milder.
  --   - a top-level construct the parser could not parse at all: worse
  --     still -- silently DROPPED with no trace anywhere unless this is
  --     checked, so the report (which only ever sees what DID parse)
  --     could look completely clean while an entire additional
  --     function, of unknown content, was never considered at all.
  let unverifiedFns : List CCC.Syntax.FunVerifyResult :=
    match result.verifyResult with
    | some vr => vr.results.filter (fun r =>
        r.funName != "program" && (r.status == .degraded || r.status == .exempt))
    | none => []
  if (!unverifiedFns.isEmpty || !result.parseWarnings.isEmpty) && !allowDegraded then
    IO.eprintln ""
    if !unverifiedFns.isEmpty then
      IO.eprintln s!"ERROR: {unverifiedFns.length} function(s) were NOT fully verified (degraded or exempt):"
      for r in unverifiedFns do
        IO.eprintln s!"  {formatFunReport r}"
    if !result.parseWarnings.isEmpty then
      IO.eprintln s!"ERROR: {result.parseWarnings.length} top-level construct(s) could not be parsed and were SKIPPED:"
      for (msg, loc) in result.parseWarnings do
        IO.eprintln s!"  at {loc.line}:{loc.col}: {msg}"
      IO.eprintln "The report above is only about what DID parse -- an unknown amount of additional source was never analysed at all."
    IO.eprintln "Pass --allow-degraded to compile anyway (these were not fully checked)."
    return 1

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
