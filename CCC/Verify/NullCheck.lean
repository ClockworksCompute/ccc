import CCC.Verify.FlowState

namespace CCC.Verify.NullCheck

private def ptrRootName? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | _ => none

private def mkNullViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    : Syntax.SafetyViolation :=
  { property := .noNullDeref
    loc := loc
    expr := reprStr expr
    message := "Possible null-pointer dereference"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Add a null-check guard before dereferencing this pointer" }

private def checkNullableDeref (ctx : VerifyCtx) (state : FlowState)
    (ptrExpr : Syntax.Expr) (fullExpr : Syntax.Expr) (loc : Syntax.Loc) : FlowState :=
  match ptrRootName? ptrExpr with
  | some name =>
      match state.getPtr name with
      | some (.nullable _) =>
          state.addViolation (mkNullViolation ctx loc fullExpr)
      | some (.checkedLive _) =>
          state.addEvidence (.nullChecked name loc)
      | _ => state
  | none => state

/-- Null-dereference checks over expressions. -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .unOp .deref operand loc =>
      let s1 := checkExpr ctx operand state
      checkNullableDeref ctx s1 operand expr loc
  | .arrow ptr _field loc =>
      let s1 := checkExpr ctx ptr state
      checkNullableDeref ctx s1 ptr expr loc
  | .index arr idx loc =>
      let s1 := checkExpr ctx arr state
      let s2 := checkExpr ctx idx s1
      checkNullableDeref ctx s2 arr expr loc
  | .binOp _ lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      checkExpr ctx rhs s1
  | .unOp _ operand _ => checkExpr ctx operand state
  | .member obj _ _ => checkExpr ctx obj state
  | .call _ args _ => args.foldl (fun st arg => checkExpr ctx arg st) state
  | .assign lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      checkExpr ctx rhs s1
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  -- FEL-68: sizeof(expr)'s operand is never evaluated in C, so there's
  -- nothing to null-check inside it — same leaf treatment as `.sizeOf`.
  | .sizeOfExpr _ _ => state
  -- Phase 2 Expr
  | .strLit _ _ | .nullLit _ | .floatLit _ _ => state
  | .ternary c t e _ =>
      let s1 := checkExpr ctx c state
      let s2 := checkExpr ctx t s1
      checkExpr ctx e s2
  | .cast _ operand _ => checkExpr ctx operand state
  | .comma l r _ =>
      let s1 := checkExpr ctx l state
      checkExpr ctx r s1
  | .initList elems _ => elems.foldl (fun st e => checkExpr ctx e st) state
  | .callFnPtr fn args _ =>
      let s1 := checkExpr ctx fn state
      args.foldl (fun st arg => checkExpr ctx arg st) s1

end CCC.Verify.NullCheck
