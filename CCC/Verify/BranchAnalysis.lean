import CCC.Verify.FlowState

namespace CCC.Verify

/-- Facts learned from a branch condition, keyed by an access-path string
    ("name", "obj->field", "obj.field") — see `rangeKeyOfExpr?`. -/
inductive BranchFact where
  | ptrNonNull (name : String)
  | ptrIsNull (name : String)
  | rangeLo (key : String) (v : Int)           -- key ≥ v
  | rangeHiExclusive (key : String) (v : Int)  -- key < v
  deriving Repr, Inhabited, BEq, DecidableEq

private def fieldBoundKey (obj : String) (field : String) : String :=
  obj ++ "->" ++ field

/-- Signed integer literal value, if the expression is exactly a literal
    (including a negated literal, so `-5` produced by the unary-minus parse
    is also recognised). -/
private partial def intLitToInt? (expr : Syntax.Expr) : Option Int :=
  match expr with
  | .intLit v _ => some v
  | .unOp .neg inner _ =>
      match intLitToInt? inner with
      | some v => some (-v)
      | none => none
  | _ => none

private def ptrNameFromExpr? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | _ => none

/-- Is this expression a spelling of the null pointer constant?
    Covers `0`, the `NULL` macro after preprocessing (`(void*)0`, parsed as a
    cast of an int literal), and the dedicated `.nullLit` token. -/
private def isNullLikeExpr (expr : Syntax.Expr) : Bool :=
  match expr with
  | .nullLit _ => true
  | .intLit v _ => v == 0
  | .cast _ (.intLit v _) _ => v == 0
  | .cast _ (.nullLit _) _ => true
  | _ => false

/-- Extract a range-tracking key from a variable or field expression. -/
private def rangeKeyOfExpr? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | .arrow (.var obj _) field _ => some (fieldBoundKey obj field)
  | .member (.var obj _) field _ => some (obj ++ "." ++ field)
  | _ => none

private def makeLoFact (key : String) (v : Int) : BranchFact := .rangeLo key v
private def makeHiFact (key : String) (v : Int) : BranchFact := .rangeHiExclusive key v

/-- `cmp` is `lhs op rhs` where `lhs` is a tracked key-expression and `rhs` is
    a literal. Returns (thenFacts, elseFacts) for that orientation. Handles
    all four ordering operators, producing BOTH an upper-bound fact on the
    side where it applies and a lower-bound fact on the other side (the
    previous implementation only ever produced upper bounds). -/
private def extractOrderedCmp (op : Syntax.BinOp) (key : String) (n : Int)
    : (List BranchFact) × (List BranchFact) :=
  match op with
  | .lt => ([makeHiFact key n],       [makeLoFact key n])       -- i<n / i≥n
  | .gt => ([makeLoFact key (n + 1)], [makeHiFact key (n + 1)]) -- i>n / i≤n
  | .le => ([makeHiFact key (n + 1)], [makeLoFact key (n + 1)]) -- i≤n / i>n
  | .ge => ([makeLoFact key n],       [makeHiFact key n])       -- i≥n / i<n
  | _ => ([], [])

/-- Flip an ordering operator for swapped operands: `n < i` becomes `i > n`. -/
private def flipOrder (op : Syntax.BinOp) : Syntax.BinOp :=
  match op with
  | .lt => .gt
  | .gt => .lt
  | .le => .ge
  | .ge => .le
  | other => other

private def extractCmpFacts (op : Syntax.BinOp) (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  match rangeKeyOfExpr? lhs, intLitToInt? rhs with
  | some key, some n => extractOrderedCmp op key n
  | _, _ =>
      match intLitToInt? lhs, rangeKeyOfExpr? rhs with
      | some n, some key => extractOrderedCmp (flipOrder op) key n
      | _, _ => ([], [])

private def extractNullEqFacts (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  let lhsPtr : Option String := ptrNameFromExpr? lhs
  let rhsPtr : Option String := ptrNameFromExpr? rhs
  match lhsPtr, rhsPtr, isNullLikeExpr rhs, isNullLikeExpr lhs with
  | some p, _, true, _ => ([.ptrIsNull p], [.ptrNonNull p])
  | _, some p, _, true => ([.ptrIsNull p], [.ptrNonNull p])
  | _, _, _, _ => ([], [])

private def extractNullNeFacts (lhs rhs : Syntax.Expr)
    : (List BranchFact) × (List BranchFact) :=
  let lhsPtr : Option String := ptrNameFromExpr? lhs
  let rhsPtr : Option String := ptrNameFromExpr? rhs
  match lhsPtr, rhsPtr, isNullLikeExpr rhs, isNullLikeExpr lhs with
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
  -- A bare pointer used as a condition: `if (p)` / `if (!p)` (via the .not_
  -- case above). Harmless no-op for non-pointer variables (applyFacts only
  -- acts on tracked pointer state).
  | .var name _ => ([.ptrNonNull name], [.ptrIsNull name])
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
      | .rangeLo key v => st.tightenLo key v
      | .rangeHiExclusive key v => st.tightenHiExclusive key v)
    state

/-- Utility for callers that key bounds by `obj->field`. -/
def boundKeyForField (obj : String) (field : String) : String :=
  fieldBoundKey obj field

end CCC.Verify
