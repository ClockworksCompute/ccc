/-
  CCC/Contracts.lean — Module API contracts (canonical)

  Source of truth: factory/docs/design/CCC_CANONICAL_CONTRACT.md

  VerifiedProgram has private constructor — emitter cannot accept unverified Program.
  Construction flows through CCC.VerifierOnly.mkVerified with proof evidence.isSafe = true.
-/

import CCC.Syntax.AST
import CCC.Syntax.PtrState
import CCC.Parse.Parse
import CCC.Verify.Verify
import CCC.Emit.EmitX86

namespace CCC

/-- Opaque wrapper: callers cannot construct this directly.
    Prevents calling the emitter on an unverified program. -/
structure VerifiedProgram where
  private mk ::
  program : Syntax.Program
  evidence : Syntax.ProgramVerifyResult
  deriving Repr

namespace VerifierOnly

/-- Trusted constructor used by verifier implementation and emitter unit tests.
    Requires proof that the report is safe. -/
def mkVerified (prog : Syntax.Program) (evidence : Syntax.ProgramVerifyResult)
    (_h : evidence.isSafe = true) : VerifiedProgram :=
  { program := prog, evidence := evidence }

end VerifierOnly

/-- Parser contract. Implemented by CCC01. -/
def parseSource (source : String) : Except String Syntax.Program :=
  Parse.parseProgram source

/-- Verifier contract. Implemented by CCC02.
    Returns VerifiedProgram on success, or violations on failure. -/
def verifyProgram (prog : Syntax.Program)
    : Except (List Syntax.SafetyViolation) VerifiedProgram := do
  let report := Verify.verifyProgramReport prog
  if h : report.isSafe then
    return VerifierOnly.mkVerified prog report h
  else
    throw report.allViolations

/-- Emitter contract. Implemented by CCC03.
    Only accepts VerifiedProgram — verifier bypass is a type error. -/
def emitProgram (vprog : VerifiedProgram) : Except String String :=
  Emit.emitProgramImpl vprog.program

end CCC
