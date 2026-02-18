import CCC.Verify.TypeSize

namespace CCC.Verify.PointerSafety

private def ptrRootName? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | _ => none

private def isPointerTy (ty : Syntax.CType) : Bool :=
  match ty with
  | .pointer _ => true
  | _ => false

private def mallocCallSize? (ctx : VerifyCtx) (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .call "malloc" args _ =>
      match args with
      | [sizeExpr] => resolveExprNat ctx sizeExpr
      | _ => none
  | _ => none

private def isZeroLiteral (expr : Syntax.Expr) : Bool :=
  match expr with
  | .intLit v _ => v == 0
  | _ => false

private def mkUseAfterFreeViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    : Syntax.SafetyViolation :=
  { property := .noUseAfterFree
    loc := loc
    expr := reprStr expr
    message := "Dereference of pointer after it was freed"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Do not use the pointer after free; set it to null and avoid dereference" }

private def mkDoubleFreeViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    : Syntax.SafetyViolation :=
  { property := .noDoubleFree
    loc := loc
    expr := reprStr expr
    message := "Double free detected"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Ensure each allocation is freed at most once" }

private def mkInvalidFreeViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    : Syntax.SafetyViolation :=
  { property := .noDoubleFree
    loc := loc
    expr := reprStr expr
    message := "Attempt to free a pointer that is not known to be heap-live"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Only call free on heap pointers returned from malloc" }

private partial def tyName : Syntax.CType → String
  | .void => "void"
  | .int => "int"
  | .char => "char"
  | .long => "long"
  | .bool => "bool"
  | .sizeT => "size_t"
  | .pointer inner => s!"{tyName inner} *"
  | .unsigned inner => s!"unsigned {tyName inner}"
  | .array inner n => s!"{tyName inner}[{n}]"
  | .struct_ name => s!"struct {name}"
  -- Phase 2 types
  | .float_ => "float"
  | .double_ => "double"
  | .short => "short"
  | .longLong => "long long"
  | .signed inner => s!"signed {tyName inner}"
  | .enum_ name => s!"enum {name}"
  | .union_ name => s!"union {name}"
  | .funcPtr ret params =>
      let paramStr := String.intercalate ", " (params.map tyName)
      s!"{tyName ret} (*)({paramStr})"
  | .typedef_ name => name
  | .const_ inner => s!"const {tyName inner}"
  | .volatile_ inner => s!"volatile {tyName inner}"
  | .restrict_ inner => s!"restrict {tyName inner}"

private def mkDerefNonPointerViolation (ctx : VerifyCtx) (loc : Syntax.Loc)
    (expr : Syntax.Expr) (name : String) (ty : Syntax.CType) : Syntax.SafetyViolation :=
  { property := .noNullDeref
    loc := loc
    expr := reprStr expr
    message := s!"Dereference of non-pointer variable '{name}' (type: {tyName ty})"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some s!"Variable '{name}' is not a pointer; remove the dereference operator" }

private def checkDereferenceable (ctx : VerifyCtx) (state : FlowState)
    (ptrExpr : Syntax.Expr) (fullExpr : Syntax.Expr) (loc : Syntax.Loc) : FlowState :=
  match ptrRootName? ptrExpr with
  | some name =>
      match state.getPtr name with
      | some .freed => state.addViolation (mkUseAfterFreeViolation ctx loc fullExpr)
      | some ps =>
          if Syntax.PtrState.isDereferenceable ps then
            state.addEvidence (.ptrLive name ps)
          else
            state
      | none =>
          -- No pointer state: check if the variable has a known non-pointer type
          match state.getType name with
          | some ty =>
              if isPointerTy ty then state
              else state.addViolation (mkDerefNonPointerViolation ctx loc fullExpr name ty)
          | none => state
  | none => state

private def applyFreeTransition (ctx : VerifyCtx) (state : FlowState)
    (arg : Syntax.Expr) (fullExpr : Syntax.Expr) (loc : Syntax.Loc) : FlowState :=
  match ptrRootName? arg with
  | some name =>
      match state.getPtr name with
      | some .freed => state.addViolation (mkDoubleFreeViolation ctx loc fullExpr)
      | some (.stackLocal _) => state.addViolation (mkInvalidFreeViolation ctx loc fullExpr)
      | some (.uninitialized) => state.addViolation (mkInvalidFreeViolation ctx loc fullExpr)
      | some _ =>
          -- Mark the freed name AND all its aliases as freed
          let group := state.getAliasGroup name
          group.foldl (fun st n => st.setPtr n .freed) state
      | none => state
  | none => state

private def applyAssignTransition (ctx : VerifyCtx) (state : FlowState)
    (lhs rhs : Syntax.Expr) : FlowState :=
  match lhs with
  | .var lhsName _ =>
      match state.getType lhsName with
      | some lhsTy =>
          if isPointerTy lhsTy then
            match mallocCallSize? ctx rhs with
            | some n =>
                -- Fresh allocation: break old aliases, no new alias
                (state.removeAliasesFor lhsName).setPtr lhsName (.nullable (some n))
            | none =>
                match rhs with
                | .var rhsName _ =>
                    match state.getPtr rhsName with
                    | some rhsState =>
                        -- Pointer-to-pointer copy: break old aliases, register new
                        let s1 := state.removeAliasesFor lhsName
                        let s2 := s1.setPtr lhsName rhsState
                        s2.addAlias lhsName rhsName
                    | none => state
                | _ =>
                    if isZeroLiteral rhs then
                      (state.removeAliasesFor lhsName).setPtr lhsName (.nullable none)
                    else state
          else
            state
      | none => state
  | _ => state

/-- Pointer liveness checks over expressions (use-after-free + free transitions). -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  | .binOp _ lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      checkExpr ctx rhs s1
  | .unOp .deref operand loc =>
      let s1 := checkExpr ctx operand state
      checkDereferenceable ctx s1 operand expr loc
  | .unOp _ operand _ => checkExpr ctx operand state
  | .index arr idx loc =>
      let s1 := checkExpr ctx arr state
      let s2 := checkExpr ctx idx s1
      checkDereferenceable ctx s2 arr expr loc
  | .member obj _ _ => checkExpr ctx obj state
  | .arrow ptr _field loc =>
      let s1 := checkExpr ctx ptr state
      checkDereferenceable ctx s1 ptr expr loc
  | .call fn args loc =>
      let s1 := args.foldl (fun st arg => checkExpr ctx arg st) state
      if fn == "free" then
        match args with
        | [arg] => applyFreeTransition ctx s1 arg expr loc
        | _ => s1
      else
        s1
  | .assign lhs rhs _loc =>
      let s1 := checkExpr ctx lhs state
      let s2 := checkExpr ctx rhs s1
      applyAssignTransition ctx s2 lhs rhs
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

/-- Handle declaration-level pointer state updates. -/
def handleVarDecl (ctx : VerifyCtx) (name : String) (ty : Syntax.CType)
    (init : Option Syntax.Expr) (state : FlowState) : FlowState :=
  let baseState : FlowState := (state.setType name ty)
  let typedState : FlowState :=
    match ty with
    | .array _ n =>
        let byteSize : Option Nat := sizeOfType ctx ty
        let st1 := baseState.setPtr name (.stackLocal byteSize)
        st1.addEvidence (.stackBounded name n)
    | .pointer _ => baseState.setPtr name .uninitialized
    | _ => baseState
  match init with
  | some initExpr =>
      let s1 := checkExpr ctx initExpr typedState
      let s2 : FlowState :=
        match ty with
        | .pointer _ =>
            match mallocCallSize? ctx initExpr with
            | some n => s1.setPtr name (.nullable (some n))
            | none =>
                match initExpr with
                | .var rhsName _ =>
                    match s1.getPtr rhsName with
                    | some rhsState =>
                        -- Declaration with pointer init: register alias
                        let st := s1.setPtr name rhsState
                        st.addAlias name rhsName
                    | none => s1
                | _ => if isZeroLiteral initExpr then s1.setPtr name (.nullable none) else s1
        | _ => s1
      s2
  | none => typedState

/-- Statement-level entrypoint for pointer safety checks. -/
partial def check (ctx : VerifyCtx) (stmt : Syntax.Stmt) (state : FlowState) : FlowState :=
  match stmt with
  | .varDecl name ty init _ => handleVarDecl ctx name ty init state
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
      let bodyState := body.foldl (fun st stx => check ctx stx st) s0
      FlowState.merge s0 bodyState
  | .for_ init cond step body _ =>
      let s1 :=
        match init with
        | some initStmt => check ctx initStmt state
        | none => state
      let s2 :=
        match cond with
        | some condExpr => checkExpr ctx condExpr s1
        | none => s1
      let s3 :=
        match step with
        | some stepExpr => checkExpr ctx stepExpr s2
        | none => s2
      let bodyState := body.foldl (fun st stx => check ctx stx st) s3
      FlowState.merge s3 bodyState
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

end CCC.Verify.PointerSafety
