/-
  CCC/Pipeline.lean — End-to-end compilation pipeline

  Wires parseSource → verifyProgram → emitProgram with error reporting.
-/

import CCC.Contracts
import CCC.Error.Report

namespace CCC

/-- Result of attempting to compile a C source file. -/
structure CompileResult where
  assembly       : Option String
  verifyResult   : Option Syntax.ProgramVerifyResult
  violations     : List Syntax.SafetyViolation
  report         : String
  deriving Repr

/-- Build a ProgramVerifyResult from a flat list of violations (for error reporting). -/
private def violationsToResult (violations : List Syntax.SafetyViolation)
    : Syntax.ProgramVerifyResult :=
  { results := [{ funName := "program", status := .verified, violations := violations, evidence := [] }] }

/-- Full compilation pipeline: parse → verify → emit, with formatted reporting.

    FEL-40: this is the ONLY public entry point, and it never emits assembly
    for a program the verifier rejected. Earlier versions "force-emitted"
    anyway (`Emit.emitProgramAArch64 prog` on the raw, unverified program),
    which meant `ccc program.c -o out` would happily assemble, link, and
    exit 0 for a program it had just printed "Compilation aborted" for —
    the exact opposite of the guarantee the README describes. See
    `compileIgnoringViolations` below for the (explicitly-named, not
    CLI-wired) escape hatch this replaces. -/
def compile (source : String) (filename : String) : CompileResult :=
  match parseSource source with
  | .error parseErr =>
    { assembly := none
      verifyResult := none
      violations := []
      report := s!"ERROR: Parse error in {filename}:\n  {parseErr}" }
  | .ok prog =>
    match verifyProgram prog with
    | .ok vprog =>
      match emitProgram vprog with
      | .ok asm =>
        { assembly := some asm
          verifyResult := some vprog.evidence
          violations := []
          report := Error.formatSuccess vprog.evidence filename .verified }
      | .error emitErr =>
        { assembly := none
          verifyResult := some vprog.evidence
          violations := []
          report := s!"ERROR: Emission error in {filename}:\n  {emitErr}" }
    | .error violations =>
      { assembly := none
        verifyResult := some (violationsToResult violations)
        violations := violations
        report := Error.formatResult (violationsToResult violations) source filename }

/-- Explicit, deliberately-not-CLI-wired escape hatch: emit assembly for a
    program even though the verifier rejected it. This exists for the
    `--harden` runtime-check work (FEL-59), where the point is precisely to
    still produce a binary but with checks inserted at every access the
    verifier could not prove — NOT to silently hand back the unverified
    assembly as if nothing were wrong. Nothing calls this today; `Main.lean`
    only ever calls `compile`. -/
def compileIgnoringViolations (source : String) (filename : String) : CompileResult :=
  match parseSource source with
  | .error parseErr =>
    { assembly := none, verifyResult := none, violations := []
      report := s!"ERROR: Parse error in {filename}:\n  {parseErr}" }
  | .ok prog =>
    match verifyProgram prog with
    | .ok vprog =>
      match emitProgram vprog with
      | .ok asm =>
        { assembly := some asm, verifyResult := some vprog.evidence, violations := []
          report := Error.formatSuccess vprog.evidence filename .verified }
      | .error emitErr =>
        { assembly := none, verifyResult := some vprog.evidence, violations := []
          report := s!"ERROR: Emission error in {filename}:\n  {emitErr}" }
    | .error violations =>
      let verifyResult := violationsToResult violations
      match Emit.emitProgramAArch64 prog with
      | .ok asm =>
        { assembly := some asm, verifyResult := some verifyResult, violations := violations
          report := Error.formatResult verifyResult source filename }
      | .error _ =>
        { assembly := none, verifyResult := some verifyResult, violations := violations
          report := Error.formatResult verifyResult source filename }

end CCC
