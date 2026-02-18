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

/-- Full compilation pipeline: parse → verify → emit, with formatted reporting. -/
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
      let verifyResult := violationsToResult violations
      -- Force-emit: attempt emission despite verification failures
      let emitResult := Emit.emitProgramAArch64 prog
      match emitResult with
      | .ok asm =>
        { assembly := some asm
          verifyResult := some verifyResult
          violations := violations
          report := Error.formatResult verifyResult source filename }
      | .error _ =>
        { assembly := none
          verifyResult := some verifyResult
          violations := violations
          report := Error.formatResult verifyResult source filename }

end CCC
