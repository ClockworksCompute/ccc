import CCC.Verify.BranchAnalysis
import CCC.Verify.TypeSize

namespace CCC.Verify.BoundsCheck

private def exprName (expr : Syntax.Expr) : String :=
  match expr with
  | .var name _ => name
  | .arrow (.var obj _) field _ => obj ++ "->" ++ field
  | .member (.var obj _) field _ => obj ++ "." ++ field
  | _ => reprStr expr

/-- Access-path key used to look up / update tracked range facts. -/
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

private def isUnsignedTy (ty : Syntax.CType) : Bool :=
  match ty with
  | .unsigned _ => true
  | .sizeT => true
  | _ => false

private def mkBoundsViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (message : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds
    loc := loc
    expr := reprStr expr
    message := message
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Add or strengthen bounds checks before this access" }

private def mkBufSinkViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (fnName : String) (message : String) (suggestion : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds
    loc := loc
    expr := reprStr expr
    message := message
    context := [s!"function: {ctx.currentFun}", s!"builtin: {fnName}"]
    suggestion := some suggestion }

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

-- ══════════════════════════════════════════════════════════════
-- Range resolution for indices / lengths (FEL-46: signed, with lower
-- bounds, replacing the old Nat-only "exclusive upper bound" scheme).
-- ══════════════════════════════════════════════════════════════

/-- Best-known range for an expression: a resolvable literal/arithmetic value
    collapses to a point range; otherwise fall back to whatever range is
    tracked for its access-path key. -/
private def idxKnownRange (ctx : VerifyCtx) (state : FlowState) (idx : Syntax.Expr) : IRange :=
  match resolveExprInt ctx idx with
  | some v => IRange.point v
  | none =>
      match boundKeyFromExpr? idx with
      | some key => (state.getRange key).getD IRange.unknown
      | none => IRange.unknown

/-- Is this index/length provably non-negative? Prefers a known lower bound;
    falls back to the declared type being unsigned. -/
private def idxLoOk (ctx : VerifyCtx) (state : FlowState) (idx : Syntax.Expr) (r : IRange) : Bool :=
  if r.knownNonNeg then true
  else if r.knownNeg then false
  else
    match exprType? ctx state idx with
    | some ty => isUnsignedTy ty
    | none => false

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

/-- Signed-aware length resolution used by the memcpy-shaped sinks: `none`
    means "cannot verify" (including a length we can prove may be negative,
    which is at least as dangerous as an over-long length once cast to
    `size_t`). -/
private def lengthBoundInclusive? (ctx : VerifyCtx) (state : FlowState)
    (lenExpr : Syntax.Expr) : Option Nat :=
  let r := idxKnownRange ctx state lenExpr
  if !(idxLoOk ctx state lenExpr r) then none
  else
    match r.hi with
    | some hiExcl => if hiExcl ≤ 0 then some 0 else some (hiExcl - 1).toNat
    | none => none

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
  | none => state
  | some cap =>
      let r := idxKnownRange ctx state idx
      if !(idxLoOk ctx state idx r) then
        state.addViolation
          (mkBoundsViolation ctx loc fullExpr
            "Index may be negative (cannot verify a non-negative lower bound)")
      else
        match r.hi with
        | some idxBoundExclusive =>
            if idxBoundExclusive ≤ Int.ofNat cap then
              match resolveExprInt ctx idx with
              | some v =>
                  if v ≥ 0 then
                    state.addEvidence (.staticBounds (exprName arr) cap v.toNat)
                  else
                    state.addEvidence (.dynamicBoundsChecked (exprName arr) loc)
              | none => state.addEvidence (.dynamicBoundsChecked (exprName arr) loc)
            else
              state.addViolation
                (mkBoundsViolation ctx loc fullExpr
                  s!"Index may exceed array bounds (capacity={cap}, required<{idxBoundExclusive})")
        | none =>
            state.addViolation
              (mkBoundsViolation ctx loc fullExpr
                "Cannot verify dynamic index is within bounds")

-- ══════════════════════════════════════════════════════════════
-- Known-sink table (FEL-45): memcpy/memmove/memset/strncpy/snprintf checked
-- like memcpy against the destination (and source, where relevant);
-- strcpy/strcat accepted only when the source is a literal that provably
-- fits; sprintf/gets always flagged as inherently unboundable.
-- ══════════════════════════════════════════════════════════════

private def checkCopyCall (ctx : VerifyCtx) (fnName : String) (dst src len fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match bufferSizeBytes? ctx state dst, bufferSizeBytes? ctx state src with
  | some dstSize, some srcSize =>
      match lengthBoundInclusive? ctx state len with
      | some lenInc =>
          if lenInc ≤ dstSize && lenInc ≤ srcSize then
            state.addEvidence (.dynamicBoundsChecked (exprName dst) loc)
          else
            state.addViolation
              (mkBufSinkViolation ctx loc fullExpr fnName
                s!"{fnName} length {lenInc} exceeds buffer size (dst={dstSize}, src={srcSize})"
                "Prove len is bounded by both source and destination buffer sizes")
      | none =>
          state.addViolation
            (mkBufSinkViolation ctx loc fullExpr fnName
              s!"Cannot verify {fnName} length against buffers (dst={dstSize}, src={srcSize})"
              "Prove len is bounded by both source and destination buffer sizes")
  | _, _ => state

private def checkSingleBufLenCall (ctx : VerifyCtx) (fnName : String) (dst len fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match bufferSizeBytes? ctx state dst with
  | some dstSize =>
      match lengthBoundInclusive? ctx state len with
      | some lenInc =>
          if lenInc ≤ dstSize then
            state.addEvidence (.dynamicBoundsChecked (exprName dst) loc)
          else
            state.addViolation
              (mkBufSinkViolation ctx loc fullExpr fnName
                s!"{fnName} length {lenInc} exceeds destination buffer size (dst={dstSize})"
                "Prove len is bounded by the destination buffer size")
      | none =>
          state.addViolation
            (mkBufSinkViolation ctx loc fullExpr fnName
              s!"Cannot verify {fnName} length against destination buffer (dst={dstSize})"
              "Prove len is bounded by the destination buffer size")
  | none => state

private def checkLiteralFitsCall (ctx : VerifyCtx) (fnName : String) (dst src fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match src with
  | .strLit s _ =>
      match bufferSizeBytes? ctx state dst with
      | some dstSize =>
          if s.length + 1 ≤ dstSize then
            state.addEvidence (.dynamicBoundsChecked (exprName dst) loc)
          else
            state.addViolation
              (mkBufSinkViolation ctx loc fullExpr fnName
                s!"{fnName} source literal ({s.length + 1} bytes incl. NUL) exceeds destination buffer size (dst={dstSize})"
                s!"Use a bounded copy (e.g. strncpy/snprintf) or enlarge the destination")
      | none =>
          state.addViolation
            (mkBufSinkViolation ctx loc fullExpr fnName
              s!"Cannot verify {fnName} destination buffer size"
              "Prove the destination buffer is large enough for the source")
  | _ =>
      state.addViolation
        (mkBufSinkViolation ctx loc fullExpr fnName
          s!"Cannot verify {fnName} destination is large enough for a non-literal source"
          s!"Use a bounded copy (e.g. strncpy/snprintf) or a literal source of known length")

-- ══════════════════════════════════════════════════════════════
-- Kill/shift range facts on write (FEL-42). Any write to a tracked key must
-- either recompute its range from the new value or forget it — a stale
-- upper bound surviving a reassignment is how the Heartbleed-shaped bug in
-- FEL-42 slips past a bounds check.
-- ══════════════════════════════════════════════════════════════

/-- If `rhs` is `key + literal` / `literal + key` / `key - literal` where
    `key` matches `selfKey`, return the signed delta (`i = i + 100` and its
    `i - k` counterpart; used for both plain reassignment and the desugared
    shape produced by `i += k`). -/
private def selfShiftDelta? (ctx : VerifyCtx) (selfKey : String) (rhs : Syntax.Expr) : Option Int :=
  match rhs with
  | .binOp .add a b _ =>
      match boundKeyFromExpr? a, resolveExprInt ctx b with
      | some k, some d => if k == selfKey then some d else none
      | _, _ =>
          match boundKeyFromExpr? b, resolveExprInt ctx a with
          | some k, some d => if k == selfKey then some d else none
          | _, _ => none
  | .binOp .sub a _b _ =>
      match boundKeyFromExpr? a with
      | some k =>
          if k == selfKey then
            match resolveExprInt ctx _b with
            | some d => some (-d)
            | none => none
          else none
      | none => none
  | _ => none

private def applyScalarAssign (ctx : VerifyCtx) (lhs rhs : Syntax.Expr) (state : FlowState)
    : FlowState :=
  match boundKeyFromExpr? lhs with
  | none => state
  | some key =>
      match resolveExprInt ctx rhs with
      | some v => state.setRange key (IRange.point v)
      | none =>
          match selfShiftDelta? ctx key rhs with
          | some d =>
              match state.getRange key with
              | some r => state.setRange key (r.shift d)
              | none => state.clearRange key
          | none => state.clearRange key

private def applyScalarCompound (ctx : VerifyCtx) (op : Syntax.BinOp) (lhs rhs : Syntax.Expr)
    (state : FlowState) : FlowState :=
  match boundKeyFromExpr? lhs with
  | none => state
  | some key =>
      let delta? : Option Int :=
        match op with
        | .addAssign => resolveExprInt ctx rhs
        | .subAssign => (resolveExprInt ctx rhs).map (fun v => -v)
        | _ => none
      match delta?, state.getRange key with
      | some d, some r => state.setRange key (r.shift d)
      | _, _ => state.clearRange key

private def applyScalarIncDec (op : Syntax.UnOp) (operand : Syntax.Expr) (state : FlowState)
    : FlowState :=
  match boundKeyFromExpr? operand with
  | none => state
  | some key =>
      let delta? : Option Int :=
        match op with
        | .preInc | .postInc => some 1
        | .preDec | .postDec => some (-1)
        | _ => none
      match delta?, state.getRange key with
      | some d, some r => state.setRange key (r.shift d)
      | some _, none => state.clearRange key
      | none, _ => state

/-- Called for a `varDecl` initializer: seeds a point range when the
    initializer resolves to a known integer, otherwise leaves it unknown
    (never clears — the variable has no prior tracked range to go stale). -/
def applyDeclRange (ctx : VerifyCtx) (name : String) (init : Syntax.Expr) (state : FlowState)
    : FlowState :=
  match resolveExprInt ctx init with
  | some v => state.setRange name (IRange.point v)
  | none => state

/-- Bounds checks over expressions (array index, memcpy-shaped sinks, and
    range invalidation/update on writes). -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  | .binOp op lhs rhs _ =>
      match op with
      | .addAssign | .subAssign | .mulAssign | .divAssign | .modAssign
      | .andAssign | .orAssign | .xorAssign | .shlAssign | .shrAssign =>
          let s1 := checkExpr ctx lhs state
          let s2 := checkExpr ctx rhs s1
          applyScalarCompound ctx op lhs rhs s2
      | _ =>
          let s1 := checkExpr ctx lhs state
          checkExpr ctx rhs s1
  | .unOp op operand _ =>
      match op with
      | .preInc | .preDec | .postInc | .postDec =>
          let s1 := checkExpr ctx operand state
          applyScalarIncDec op operand s1
      | _ => checkExpr ctx operand state
  | .member obj _ _ => checkExpr ctx obj state
  | .arrow ptr _ _ => checkExpr ctx ptr state
  | .index arr idx loc =>
      let s1 := checkExpr ctx arr state
      let s2 := checkExpr ctx idx s1
      checkIndexAccess ctx arr idx expr loc s2
  | .call fn args loc =>
      let s1 := args.foldl (fun st arg => checkExpr ctx arg st) state
      match fn, args with
      | "memcpy", [dst, src, len] => checkCopyCall ctx "memcpy" dst src len expr loc s1
      | "memmove", [dst, src, len] => checkCopyCall ctx "memmove" dst src len expr loc s1
      | "memset", [dst, _val, len] => checkSingleBufLenCall ctx "memset" dst len expr loc s1
      | "strncpy", [dst, _src, len] => checkSingleBufLenCall ctx "strncpy" dst len expr loc s1
      | "snprintf", (dst :: len :: _rest) => checkSingleBufLenCall ctx "snprintf" dst len expr loc s1
      | "strcpy", [dst, src] => checkLiteralFitsCall ctx "strcpy" dst src expr loc s1
      | "strcat", [dst, src] => checkLiteralFitsCall ctx "strcat" dst src expr loc s1
      | "sprintf", (_dst :: _rest) =>
          s1.addViolation
            (mkBufSinkViolation ctx loc expr "sprintf"
              "sprintf has no bound on output length"
              "Use snprintf with an explicit destination size instead")
      | "gets", [_dst] =>
          s1.addViolation
            (mkBufSinkViolation ctx loc expr "gets"
              "gets() cannot bound input length and is inherently unsafe"
              "Use fgets with an explicit buffer size instead")
      | _, _ => s1
  | .assign lhs rhs _ =>
      let s1 := checkExpr ctx lhs state
      let s2 := checkExpr ctx rhs s1
      applyScalarAssign ctx lhs rhs s2
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

end CCC.Verify.BoundsCheck
