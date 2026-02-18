import CCC.Verify.BranchAnalysis
import CCC.Verify.TypeSize

namespace CCC.Verify.BoundsCheck

private def exprName (expr : Syntax.Expr) : String :=
  match expr with
  | .var name _ => name
  | .arrow (.var obj _) field _ => obj ++ "->" ++ field
  | .member (.var obj _) field _ => obj ++ "." ++ field
  | _ => reprStr expr

private def boundKeyFromExpr? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | .arrow (.var obj _) field _ => some (CCC.Verify.boundKeyForField obj field)
  | .member (.var obj _) field _ => some (obj ++ "." ++ field)
  | _ => none

private def intLitNat? (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .intLit v _ =>
      if v < 0 then none else some v.toNat
  | _ => none

private def mkBoundsViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (message : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds
    loc := loc
    expr := reprStr expr
    message := message
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Add or strengthen bounds checks before this access" }

private def mkMemcpyViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (message : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds
    loc := loc
    expr := reprStr expr
    message := message
    context := [s!"function: {ctx.currentFun}", "builtin: memcpy"]
    suggestion := some "Prove len is bounded by both source and destination buffer sizes" }

partial def exprType? (ctx : VerifyCtx) (state : FlowState) (expr : Syntax.Expr)
    : Option Syntax.CType :=
  match expr with
  | .intLit _ _ => some .int
  | .charLit _ _ => some .char
  | .var name _ => state.getType name
  | .sizeOf _ _ => some .sizeT
  | .unOp .deref operand _ =>
      match exprType? ctx state operand with
      | some (.pointer elem) => some elem
      | _ => none
  | .unOp .addrOf operand _ =>
      match exprType? ctx state operand with
      | some t => some (.pointer t)
      | none => none
  | .unOp _ operand _ => exprType? ctx state operand
  | .index arr _ _ =>
      match exprType? ctx state arr with
      | some (.array elem _) => some elem
      | some (.pointer elem) => some elem
      | _ => none
  | .member obj field _ =>
      match exprType? ctx state obj with
      | some (.struct_ structName) => findStructFieldType ctx structName field
      | _ => none
  | .arrow ptr field _ =>
      match exprType? ctx state ptr with
      | some (.pointer (.struct_ structName)) => findStructFieldType ctx structName field
      | _ => none
  | .call fn _ _ =>
      if fn == "malloc" then some (.pointer .void) else none
  | .binOp op _ _ _ =>
      match op with
      | .eq | .ne | .lt | .gt | .le | .ge | .and_ | .or_ => some .bool
      | _ => some .int
  | .assign lhs _ _ => exprType? ctx state lhs
  -- Phase 2 Expr
  | .strLit _ _ => some (.pointer .char)
  | .nullLit _ => some (.pointer .void)
  | .floatLit _ _ => some .double_
  | .ternary _ t _ _ => exprType? ctx state t
  | .cast ty _ _ => some ty
  | .comma _ r _ => exprType? ctx state r
  | .initList _ _ => none
  | .callFnPtr _ _ _ => none

private def arrayCapacityElems? (ctx : VerifyCtx) (state : FlowState)
    (arrExpr : Syntax.Expr) : Option Nat :=
  match arrExpr with
  | .var name _ =>
      match state.getType name with
      | some (.array _ n) => some n
      | some (.pointer elem) =>
          match state.getPtr name with
          | some ps =>
              match Syntax.PtrState.knownSize ps, sizeOfType ctx elem with
              | some bytes, some elemSize =>
                  if elemSize = 0 then none else some (bytes / elemSize)
              | _, _ => none
          | none => none
      | _ => none
  | _ =>
      match exprType? ctx state arrExpr with
      | some (.array _ n) => some n
      | _ => none

private def indexBoundExclusive? (state : FlowState) (idxExpr : Syntax.Expr) : Option Nat :=
  match intLitNat? idxExpr with
  | some n => some (n + 1)
  | none =>
      match boundKeyFromExpr? idxExpr with
      | some key => state.getBound key
      | none => none

private def lengthBoundInclusive? (ctx : VerifyCtx) (state : FlowState)
    (lenExpr : Syntax.Expr) : Option Nat :=
  match intLitNat? lenExpr with
  | some n => some n
  | none =>
      match boundKeyFromExpr? lenExpr with
      | some key =>
          match state.getBound key with
          | some b =>
              if b = 0 then some 0 else some (b - 1)
          | none => none
      | none => resolveExprNat ctx lenExpr

private def bufferSizeBytes? (ctx : VerifyCtx) (state : FlowState)
    (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .var name _ =>
      match state.getType name with
      | some (.array elem n) => sizeOfType ctx (.array elem n)
      | some (.pointer _) =>
          match state.getPtr name with
          | some ps => Syntax.PtrState.knownSize ps
          | none => none
      | some ty => sizeOfType ctx ty
      | none => none
  | _ =>
      match exprType? ctx state expr with
      | some ty => sizeOfType ctx ty
      | none => none

private def checkIndexAccess (ctx : VerifyCtx) (arr idx fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match arrayCapacityElems? ctx state arr with
  | some cap =>
      match indexBoundExclusive? state idx with
      | some idxBound =>
          if idxBound ≤ cap then
            match intLitNat? idx with
            | some staticIdx =>
                state.addEvidence (.staticBounds (exprName arr) cap staticIdx)
            | none =>
                state.addEvidence (.dynamicBoundsChecked (exprName arr) loc)
          else
            state.addViolation
              (mkBoundsViolation ctx loc fullExpr
                s!"Index may exceed array bounds (capacity={cap}, required<{idxBound})")
      | none =>
          state.addViolation
            (mkBoundsViolation ctx loc fullExpr
              "Cannot verify dynamic index is within bounds")
  | none => state

private def checkMemcpyCall (ctx : VerifyCtx) (dst src len fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match bufferSizeBytes? ctx state dst, bufferSizeBytes? ctx state src with
  | some dstSize, some srcSize =>
      match lengthBoundInclusive? ctx state len with
      | some lenInc =>
          if lenInc ≤ dstSize && lenInc ≤ srcSize then
            state.addEvidence (.dynamicBoundsChecked (exprName dst) loc)
          else
            state.addViolation
              (mkMemcpyViolation ctx loc fullExpr
                s!"memcpy length {lenInc} exceeds buffer size (dst={dstSize}, src={srcSize})")
      | none =>
          state.addViolation
            (mkMemcpyViolation ctx loc fullExpr
              s!"Cannot verify memcpy length against buffers (dst={dstSize}, src={srcSize})")
  | _, _ => state

/-- Bounds checks over expressions (array index + memcpy). -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  | .binOp _ lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      checkExpr ctx rhs s1
  | .unOp _ operand _ => checkExpr ctx operand state
  | .member obj _ _ => checkExpr ctx obj state
  | .arrow ptr _ _ => checkExpr ctx ptr state
  | .index arr idx loc =>
      let s1 := checkExpr ctx arr state
      let s2 := checkExpr ctx idx s1
      checkIndexAccess ctx arr idx expr loc s2
  | .call fn args loc =>
      let s1 := args.foldl (fun st arg => checkExpr ctx arg st) state
      if fn == "memcpy" then
        match args with
        | [dst, src, len] => checkMemcpyCall ctx dst src len expr loc s1
        | _ => s1
      else
        s1
  | .assign lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      checkExpr ctx rhs s1
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

/-- Statement-level bounds check entrypoint. -/
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

end CCC.Verify.BoundsCheck
