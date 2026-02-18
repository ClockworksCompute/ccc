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

/-- Null-dereference check entrypoint for statements. -/
partial def check (ctx : VerifyCtx) (stmt : Syntax.Stmt) (state : FlowState) : FlowState :=
  match stmt with
  | .varDecl _ _ init _ =>
      match init with
      | some expr => checkExpr ctx expr state
      | none => state
  | .exprStmt expr _ => checkExpr ctx expr state
  | .ret val _ =>
      match val with
      | some expr => checkExpr ctx expr state
      | none => state
  | .ifElse cond thenBody elseBody _ =>
      let s0 := checkExpr ctx cond state
      let sThen := thenBody.foldl (fun st stx => check ctx stx st) s0
      let sElse := elseBody.foldl (fun st stx => check ctx stx st) s0
      FlowState.merge sThen sElse
  | .while_ cond body _ =>
      let s0 := checkExpr ctx cond state
      body.foldl (fun st stx => check ctx stx st) s0
  | .for_ init cond step body _ =>
      let s1 := match init with
        | some initStmt => check ctx initStmt state
        | none => state
      let s2 := match cond with
        | some condExpr => checkExpr ctx condExpr s1
        | none => s1
      let s3 := match step with
        | some stepExpr => checkExpr ctx stepExpr s2
        | none => s2
      body.foldl (fun st stx => check ctx stx st) s3
  | .block stmts _ => stmts.foldl (fun st stx => check ctx stx st) state
  -- Phase 2 Stmt
  | .switch_ scrut cases _ =>
      let s0 := checkExpr ctx scrut state
      cases.foldl (fun st (_, body, _) => body.foldl (fun s stx => check ctx stx s) st) s0
  | .doWhile body cond _ =>
      let s1 := body.foldl (fun st stx => check ctx stx st) state
      checkExpr ctx cond s1
  | .break_ _ | .continue_ _ | .emptyStmt _ => state
  | .goto_ _ _ => state
  | .label_ _ body _ => check ctx body state

end CCC.Verify.NullCheck
