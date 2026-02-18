/-
  CCC/Syntax/PtrState.lean — Safety types for the verifier

  Pointer state machine, safety properties, violations, evidence,
  and verify result types. These are the contract between verifier and reporter.
-/

import CCC.Syntax.AST

namespace CCC.Syntax

/-- Pointer state machine.
    uninitialized → stackLocal(size)    on local array/var
    uninitialized → nullable(size?)     on malloc return
    nullable      → checkedLive(size?)  after null check
    heapLive      → freed               after free
    checkedLive   → freed               after free
    freed         → ✗                   terminal — no recovery
-/
inductive PtrState where
  | uninitialized
  | stackLocal  (size : Option Nat)
  | heapLive    (size : Option Nat)
  | nullable    (size : Option Nat)
  | checkedLive (size : Option Nat)
  | freed
  deriving Repr, Inhabited, BEq, DecidableEq

namespace PtrState

/-- Can this pointer state be safely dereferenced? -/
def isDereferenceable : PtrState → Bool
  | .stackLocal _  => true
  | .heapLive _    => true
  | .checkedLive _ => true
  | _              => false

/-- Can this pointer state be safely freed? -/
def isFreeable : PtrState → Bool
  | .heapLive _    => true
  | .checkedLive _ => true
  | _              => false

/-- Get known allocation size, if any. -/
def knownSize : PtrState → Option Nat
  | .stackLocal s  => s
  | .heapLive s    => s
  | .nullable s    => s
  | .checkedLive s => s
  | _              => none

end PtrState

/-- Verification status for a function or translation unit.
    SAFE features → verified. DEGRADE features → degraded.
    EXEMPT features → exempt. -/
inductive VerifyStatus where
  | verified    -- all SAFE/EXTEND features only; full P1-P5 guarantees
  | degraded    -- uses DEGRADE features (goto, cast, union, funcptr); reduced precision
  | exempt      -- uses EXEMPT features (varargs, setjmp); verification skipped
  | parseError  -- source didn't parse
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Which memory safety property was violated. -/
inductive SafetyProperty where
  | bufferBounds     -- CWE-120, CWE-787: out-of-bounds access
  | noUseAfterFree   -- CWE-416: dereference of freed pointer
  | noDoubleFree     -- CWE-415: free of already-freed pointer
  | noNullDeref      -- CWE-476: dereference of potentially-null pointer
  | noStackOverflow  -- CWE-121: stack buffer overflow
  deriving Repr, Inhabited, BEq, DecidableEq

/-- A single safety violation found by the verifier. -/
structure SafetyViolation where
  property   : SafetyProperty
  loc        : Loc
  expr       : String          -- the offending expression as text
  message    : String          -- human-readable description
  context    : List String     -- additional context lines
  suggestion : Option String   -- suggested fix, if applicable
  deriving Repr, Inhabited

/-- Evidence that a specific safety property holds. -/
inductive SafetyEvidence where
  | staticBounds         (arrName : String) (size : Nat) (idx : Nat)
  | dynamicBoundsChecked (arrName : String) (checkLoc : Loc)
  | ptrLive              (ptrName : String) (state : PtrState)
  | nullChecked          (ptrName : String) (checkLoc : Loc)
  | neverFreed           (ptrName : String)
  | stackBounded         (arrName : String) (size : Nat)
  | degradedBy           (feature : String) (reason : String) (loc : Loc)
  | exemptedBy           (feature : String) (reason : String) (loc : Loc)
  deriving Repr, Inhabited

/-- Verification result for a single function. -/
structure FunVerifyResult where
  funName    : String
  status     : VerifyStatus
  violations : List SafetyViolation
  evidence   : List SafetyEvidence
  deriving Repr, Inhabited

namespace FunVerifyResult

def isSafe (r : FunVerifyResult) : Bool := r.violations.isEmpty

def isVerified (r : FunVerifyResult) : Bool :=
  r.violations.isEmpty && r.status == .verified

def isDegraded (r : FunVerifyResult) : Bool :=
  r.status == .degraded

def isExempt (r : FunVerifyResult) : Bool :=
  r.status == .exempt

end FunVerifyResult

/-- Verification result for an entire program. -/
structure ProgramVerifyResult where
  results : List FunVerifyResult
  deriving Repr, Inhabited

namespace ProgramVerifyResult

def isSafe (r : ProgramVerifyResult) : Bool :=
  r.results.all (·.isSafe)

def allViolations (r : ProgramVerifyResult) : List SafetyViolation :=
  (r.results.map (·.violations)).flatten

def allEvidence (r : ProgramVerifyResult) : List SafetyEvidence :=
  (r.results.map (·.evidence)).flatten

def totalFunctions (r : ProgramVerifyResult) : Nat :=
  r.results.length

/-- Compute the worst-case status across all functions. -/
def worstStatus (r : ProgramVerifyResult) : VerifyStatus :=
  r.results.foldl (fun acc fr =>
    match acc, fr.status with
    | .exempt, _ | _, .exempt => .exempt
    | .degraded, _ | _, .degraded => .degraded
    | .parseError, _ | _, .parseError => .parseError
    | .verified, .verified => .verified
  ) .verified

/-- List functions that are degraded. -/
def degradedFunctions (r : ProgramVerifyResult) : List String :=
  (r.results.filter (·.isDegraded)).map (·.funName)

/-- List functions that are exempt. -/
def exemptFunctions (r : ProgramVerifyResult) : List String :=
  (r.results.filter (·.isExempt)).map (·.funName)

end ProgramVerifyResult

end CCC.Syntax
