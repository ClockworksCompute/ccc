import CCC.Verify.FlowState

namespace CCC.Verify

/-- Facts learned from a branch condition. Bounds are exclusive upper bounds. -/
inductive BranchFact where
  | ptrNonNull (name : String)
  | ptrIsNull (name : String)
  | varBounded (name : String) (bound : Nat)
  | varBoundedField (obj : String) (field : String) (bound : Nat)
  deriving Repr, Inhabited, BEq, DecidableEq

private def fieldBoundKey (obj : String) (field : String) : String :=
  obj ++ "->" ++ field

private def intLitToNat? (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .intLit v _ =>
      if v < 0 then none else some v.toNat
  | _ => none

private def ptrNameFromExpr? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | _ => none

private def boundExprFromExpr? (expr : Syntax.Expr) : Option (String × Option String) :=
  match expr with
  | .var name _ => some (name, none)
  | .arrow (.var obj _) field _ => some (obj, some field)
  | _ => none

private def makeBoundFact (obj : String) (fieldOpt : Option String) (bound : Nat) : BranchFact :=
  match fieldOpt with
  | some field => .varBoundedField obj field bound
  | none => .varBounded obj bound

private def extractCmpFacts (op : Syntax.BinOp) (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  match boundExprFromExpr? lhs, intLitToNat? rhs with
  | some (obj, fieldOpt), some n =>
      match op with
      | .lt => ([makeBoundFact obj fieldOpt n], [])
      | .gt => ([], [makeBoundFact obj fieldOpt (n + 1)])
      | .le => ([makeBoundFact obj fieldOpt (n + 1)], [])
      | .ge => ([], [makeBoundFact obj fieldOpt n])
      | _ => ([], [])
  | _, _ => ([], [])

private def extractNullEqFacts (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  let lhsPtr : Option String := ptrNameFromExpr? lhs
  let rhsPtr : Option String := ptrNameFromExpr? rhs
  let lhsZero : Bool := match rhs with | .intLit v _ => v == 0 | _ => false
  let rhsZero : Bool := match lhs with | .intLit v _ => v == 0 | _ => false
  match lhsPtr, rhsPtr, lhsZero, rhsZero with
  | some p, _, true, _ => ([.ptrIsNull p], [.ptrNonNull p])
  | _, some p, _, true => ([.ptrIsNull p], [.ptrNonNull p])
  | _, _, _, _ => ([], [])

private def extractNullNeFacts (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  let lhsPtr : Option String := ptrNameFromExpr? lhs
  let rhsPtr : Option String := ptrNameFromExpr? rhs
  let lhsZero : Bool := match rhs with | .intLit v _ => v == 0 | _ => false
  let rhsZero : Bool := match lhs with | .intLit v _ => v == 0 | _ => false
  match lhsPtr, rhsPtr, lhsZero, rhsZero with
  | some p, _, true, _ => ([.ptrNonNull p], [.ptrIsNull p])
  | _, some p, _, true => ([.ptrNonNull p], [.ptrIsNull p])
  | _, _, _, _ => ([], [])

/-- Extract facts for then/else branches from a boolean expression. -/
partial def extractFacts (cond : Syntax.Expr) : (List BranchFact) × (List BranchFact) :=
  match cond with
  | .unOp .not_ inner _ =>
      let (thenFacts, elseFacts) := extractFacts inner
      (elseFacts, thenFacts)
  | .binOp .eq lhs rhs _ => extractNullEqFacts lhs rhs
  | .binOp .ne lhs rhs _ => extractNullNeFacts lhs rhs
  | .binOp .lt lhs rhs _ => extractCmpFacts .lt lhs rhs
  | .binOp .gt lhs rhs _ => extractCmpFacts .gt lhs rhs
  | .binOp .le lhs rhs _ => extractCmpFacts .le lhs rhs
  | .binOp .ge lhs rhs _ => extractCmpFacts .ge lhs rhs
  | .binOp .or_ lhs rhs _ =>
      let (_thenL, elseL) := extractFacts lhs
      let (_thenR, elseR) := extractFacts rhs
      ([], elseL ++ elseR)
  | .binOp .and_ lhs rhs _ =>
      let (thenL, _elseL) := extractFacts lhs
      let (thenR, _elseR) := extractFacts rhs
      (thenL ++ thenR, [])
  | _ => ([], [])

/-- Apply branch facts to flow state. -/
def applyFacts (facts : List BranchFact) (state : FlowState) : FlowState :=
  facts.foldl
    (fun st fact =>
      match fact with
      | .ptrNonNull name =>
          match st.getPtr name with
          | some (.nullable sz) => st.setPtr name (.checkedLive sz)
          | some (.heapLive sz) => st.setPtr name (.checkedLive sz)
          | _ => st
      | .ptrIsNull name =>
          match st.getPtr name with
          | some ps => st.setPtr name (.nullable (Syntax.PtrState.knownSize ps))
          | none => st
      | .varBounded name bound => st.setBound name bound
      | .varBoundedField obj field bound => st.setBound (fieldBoundKey obj field) bound)
    state

/-- Utility for callers that key bounds by `obj->field`. -/
def boundKeyForField (obj : String) (field : String) : String :=
  fieldBoundKey obj field

end CCC.Verify
