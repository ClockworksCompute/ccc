import CCC.Verify.BranchAnalysis
import CCC.Verify.TypeSize
import CCC.Verify.Canon

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

private def mkDivByZeroViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (opName : String) : Syntax.SafetyViolation :=
  { property := .noDivByZero
    loc := loc
    expr := reprStr expr
    message := s!"Cannot verify the {opName} divisor is nonzero"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Guard with an explicit `!= 0` check, or prove it via a literal/shift-of-nonzero divisor" }

/-- Is `rhs` (a division/modulo divisor) provably nonzero? A literal
    resolves directly; `1 << x`-shaped expressions (the extremely common
    "compute a power-of-two mask/bucket-count" idiom, e.g. libwebp's
    `sym % (1 << root_bits)`) are safe whenever the shifted base is a
    nonzero literal; otherwise fall back to an explicit `!= 0` branch fact
    (`FlowState.nonZeroKeys`) or a range that excludes zero entirely
    (strictly positive or strictly negative). -/
private def isProvablyNonzero (ctx : VerifyCtx) (state : FlowState) (rhs : Syntax.Expr) : Bool :=
  match resolveExprInt ctx rhs with
  | some v => v != 0
  | none =>
      match rhs with
      | .binOp .shl base _shiftAmt _ =>
          match resolveExprInt ctx base with
          | some b => b != 0
          | none => false
      | _ =>
          match boundKeyFromExpr? rhs with
          | some key =>
              state.isNonZero key ||
              (match state.getRange key with
                | some r =>
                    (match r.lo with | some l => l > 0 | none => false) ||
                    (match r.hi with | some h => h ≤ 0 | none => false)
                | none => false)
          | none => false

partial def exprType? (ctx : VerifyCtx) (state : FlowState) (expr : Syntax.Expr)
    : Option Syntax.CType :=
  match expr with
  | .intLit _ _ => some .int
  | .charLit _ _ => some .char
  | .var name _ => state.getType name
  | .sizeOf _ _ => some .sizeT
  -- FEL-68: `sizeof(expr)`'s own type (as an expression) is always
  -- size_t, regardless of what `expr` is — matching `.sizeOf ty _` above.
  | .sizeOfExpr _ _ => some .sizeT
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

/-- Decompose `idx` as `(rowOffset+rowVar)*strideExpr + colOffset + colVar`
    — the flattened-2-D-array-write shape (e.g. libheif's
    `(out_y0+row)*out_w + out_x0 + col`). Anything else: `none`. -/
private def decompose2DIndex (idx : Syntax.Expr)
    : Option (Syntax.Expr × Syntax.Expr × Syntax.Expr × Syntax.Expr × Syntax.Expr) :=
  match idx with
  | .binOp .add (.binOp .add (.binOp .mul rowSum strideExpr _) colOffset _) colVar _ =>
      match rowSum with
      | .binOp .add rowOffset rowVar _ => some (rowOffset, rowVar, strideExpr, colOffset, colVar)
      | _ => none
  | _ => none

/-- Chain-walk proof that `aExpr + xExpr <= targetBound` (all as plain,
    unsubstituted canon keys — by the time this runs we're always past a
    branch merge, where `symbolicDefs` has been reset to `[]`, so there is
    nothing left to substitute through). Tries the direct combined key
    first, then follows `xExpr`'s own key through its exprBound chain
    (e.g. `col -> in_w -> out_w`), recombining with `aExpr` at each step.
    The two-variable combined keys this looks for are exactly the ones
    `transferExprBoundOnAssign`'s cross-term step establishes below. -/
private partial def proveSumLE (ctx : VerifyCtx) (state : FlowState)
    (aExpr xExpr : Syntax.Expr) (targetBound : String) (fuel : Nat) : Bool :=
  let aC := canon ctx.program aExpr
  let rec go (curXC : String) (fuel : Nat) : Bool :=
    let combined := joinAdd aC curXC
    if state.getExprBound combined == some targetBound then true
    else if fuel == 0 then false
    else
      match state.getExprBound curXC with
      | some nextC => go nextC (fuel - 1)
      | none => false
  go (canon ctx.program xExpr) fuel

/-- FEL-54/56/57/58 (libheif-class detection, epic DoD bullet 1) — pattern
    RECOGNITION only, never ACCEPTANCE. See FEL-64: the `proveSumLE`/`canon`
    machinery this used to accept access on reasons over unbounded integers
    (ℤ), stripping every cast and never modelling wraparound, truncation, or
    per-call-site capacity mismatches. Six one-to-three-line mutations of a
    program this mechanism accepted were confirmed with AddressSanitizer to
    still heap-overflow while it reported 0 violations (off-by-one loop
    bound, removed overflow guards, a truncating cast in a clip, a second
    call site with a smaller buffer, a capacity mutated between allocation
    and use, an unsigned-subtraction wrap) — see FEL-64's table for the
    full list. So this now ALWAYS reports "cannot verify" for the pattern
    it recognizes (a parameter whose (width, height) capacity was inferred
    interprocedurally via `VerifyCtx.capacityParamsAt`, indexed by a
    flattened 2-D expression whose stride matches the inferred width) —
    `colOk`/`rowOk` are still computed and reported in the message as a
    diagnostic hint (they tell you WHICH axis the heuristic could not close
    even provisionally), but they never flip this into an accept. Do not
    make this accept again without a sound interval/overflow domain
    (FEL-56) and a real per-call-site capacity check (FEL-58) underneath
    it — a false "equal" or a false "bounded" here is a silent, unsound
    accept, exactly the shape FEL-64 exploited. -/
private def check2DIndex (ctx : VerifyCtx) (arr idx fullExpr : Syntax.Expr) (loc : Syntax.Loc)
    (state : FlowState) : Option FlowState :=
  match arr with
  | .var arrName _ =>
      match ctx.currentParamIndex.find? (·.1 == arrName) with
      | none => none
      | some (_, arrIdx) =>
          match ctx.capacityParamsAt ctx.currentFun arrIdx with
          | none => none
          | some (widthKey, heightKey) =>
              match decompose2DIndex idx with
              | none => none
              | some (rowOffset, rowVar, strideExpr, colOffset, colVar) =>
                  if canon ctx.program strideExpr != widthKey then none
                  else
                    -- Diagnostic only (see the docstring above) — NOT used
                    -- to accept the access.
                    let colOk := proveSumLE ctx state colOffset colVar widthKey 4 ||
                                 proveSumLE ctx state colOffset colVar ("@" ++ widthKey) 4
                    let rowOk := proveSumLE ctx state rowOffset rowVar heightKey 4 ||
                                 proveSumLE ctx state rowOffset rowVar ("@" ++ heightKey) 4
                    let axisHint :=
                      if colOk && rowOk then
                        " (a heuristic pass over unbounded-integer arithmetic could not rule out overflow/wraparound in this idiom — FEL-64)"
                      else if colOk then " (row offset unproven even heuristically)"
                      else if rowOk then " (column offset unproven even heuristically)"
                      else " (neither axis proven, even heuristically)"
                    some (state.addViolation
                      (mkBoundsViolation ctx loc fullExpr
                        s!"Cannot verify flattened 2-D index stays within the inferred capacity ({widthKey}×{heightKey}) of parameter '{arrName}'{axisHint}"))
  | _ => none

private def checkIndexAccess (ctx : VerifyCtx) (arr idx fullExpr : Syntax.Expr)
    (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  match arrayCapacityElems? ctx state arr with
  | none =>
      match check2DIndex ctx arr idx fullExpr loc state with
      | some state' => state'
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

/-- Does `e` mention `key` as a `.var` anywhere in its structure? Used to
    avoid recording a self-referential symbolic definition (`in_w = in_w -
    in_x0`): substituting such a definition back into itself during a
    later `canon` walk doesn't eliminate the variable, it just unrolls it
    once per unit of `fuel` — actively counterproductive noise, not a
    useful fact, so these are simply never recorded as a symbolicDef. -/
private partial def exprMentions (key : String) (e : Syntax.Expr) : Bool :=
  match e with
  | .var name _ => name == key
  | .unOp _ o _ => exprMentions key o
  | .binOp _ l r _ => exprMentions key l || exprMentions key r
  | .cast _ o _ => exprMentions key o
  | .call _ args _ => args.any (exprMentions key)
  | .callFnPtr f args _ => exprMentions key f || args.any (exprMentions key)
  | .member o _ _ => exprMentions key o
  | .arrow p _ _ => exprMentions key p
  | .index a i _ => exprMentions key a || exprMentions key i
  | .assign l r _ => exprMentions key l || exprMentions key r
  | .ternary c t e2 _ => exprMentions key c || exprMentions key t || exprMentions key e2
  | .comma l r _ => exprMentions key l || exprMentions key r
  | .initList es _ => es.any (exprMentions key)
  | _ => false

/-- Every currently-known scalar name worth trying as a cross-term partner
    for the just-assigned variable, in the derivation below: the current
    function's own parameters, plus every key with an existing symbolic
    definition (covers the common case where the "other" side of the sum
    is a same-block local — like libheif's `out_x0` — that has no
    parameter status of its own but DOES have a just-recorded
    definition). -/
private def crossTermCandidates (ctx : VerifyCtx) (state : FlowState) : List String :=
  ctx.currentParamIndex.map (·.1) ++ state.symbolicDefs.map (·.1)

/-- FEL-56/57/58 (scoped symbolic bounds): if the RHS's canonical form
    (substituted through `symbolicDefs`) matches an EXISTING exprBounds
    fact's key exactly, the assigned variable inherits that fact directly
    (this is what lets `in_w = in_w - in_x0` — canonicalizing, via the
    sub-of-negation rule in Canon.lean plus substituting in_x0's own
    definition, to the SAME string as an earlier `dx + in_w <= out_w`
    fact — carry the bound forward onto the new `in_w`). Otherwise any
    exprBound mentioning the assigned key is dropped (sound default).

    The cross-term step handles the companion half of the libheif-overlay
    idiom: the SAME proven sum-bound gets split across TWO variables
    assigned in different arms of a LATER if/else (`out_x0`/`in_w` on the
    `dx<0` arm, only `out_x0` on the other, `in_w` left untouched) — so
    neither arm alone re-establishes a single-variable fact that survives
    `FlowState.merge`'s intersection. Trying every other known scalar `Y`
    as a partner for the just-assigned `X`, substituting through
    `symbolicDefs` on BOTH sides, lets each arm independently re-derive
    the SAME plain (unsubstituted) two-variable key — which DOES survive
    the merge, because both arms agree on it exactly. This can only add a
    fact when an existing one's canonical form is matched byte-for-byte;
    it never fabricates a bound that wasn't already proven. -/
private def transferExprBoundOnAssign (ctx : VerifyCtx) (lhs rhs : Syntax.Expr) (state : FlowState)
    : FlowState :=
  let defs := state.symbolicDefs
  let lhsC := canon ctx.program lhs
  let rhsC := canon ctx.program rhs defs
  let state1 :=
    match state.getExprBound rhsC with
    | some boundC => (state.clearExprBoundsMentioning lhsC).setExprBound lhsC boundC
    | none => state.clearExprBoundsMentioning lhsC
  let state2 :=
    match boundKeyFromExpr? lhs with
    | none => state1
    | some xKey =>
        (crossTermCandidates ctx state).foldl
          (fun st yName =>
            if yName == xKey then st
            else
              let yExpr := Syntax.Expr.var yName { line := 0, col := 0 }
              let yC := canon ctx.program yExpr defs
              match state.getExprBound (joinAdd rhsC yC) with
              | some boundC => st.setExprBound (joinAdd lhsC (canon ctx.program yExpr)) boundC
              | none => st)
          state1
  match boundKeyFromExpr? lhs with
  | none => state2
  | some key =>
      if !(exprMentions key rhs) then state2.setSymbolicDef key rhs
      else
        -- Self-referential (`W = W - offset`, libheif's border-clip
        -- shape): never useful as a symbolicDef (see `exprMentions`'s
        -- docstring), but exactly the shape that lets whatever bound W
        -- already carried (its function-entry marker, or a narrower one
        -- from an earlier clip — see `Verify.initFlowStateFromParams`
        -- and `Verify.clipPostcondition`) survive the reassignment: `W`
        -- can only SHRINK here, so `W_new + offset = W_old <= priorBound`
        -- is exactly as sound as the `W_old` fact it's built from.
        match rhs, state.getExprBound key with
        | .binOp .sub (.var key' _) offset _, some priorBound =>
            if key' == key then
              -- Plain (unsubstituted) offset key, deliberately: this fact
              -- is looked up again post-merge (once `symbolicDefs` has
              -- been reset), from `BoundsCheck.check2DIndex`, using the
              -- SAME plain access-path key the offset variable has there.
              state2.setExprBound (joinAdd lhsC (canon ctx.program offset)) priorBound
            else state2
        | _, _ => state2

private def applyScalarAssign (ctx : VerifyCtx) (lhs rhs : Syntax.Expr) (state : FlowState)
    : FlowState :=
  let state := transferExprBoundOnAssign ctx lhs rhs state
  match boundKeyFromExpr? lhs with
  | none => state
  | some key =>
      match resolveExprInt ctx rhs with
      | some v =>
          let s1 := state.setRange key (IRange.point v)
          if v != 0 then s1.setNonZero key else s1.clearNonZero key
      | none =>
          match selfShiftDelta? ctx key rhs with
          | some d =>
              match state.getRange key with
              | some r => (state.setRange key (r.shift d)).clearNonZero key
              | none => (state.clearRange key).clearNonZero key
          | none => (state.clearRange key).clearNonZero key

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
      | some d, some r => (state.setRange key (r.shift d)).clearNonZero key
      | _, _ => (state.clearRange key).clearNonZero key

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
      | some d, some r => (state.setRange key (r.shift d)).clearNonZero key
      | some _, none => (state.clearRange key).clearNonZero key
      | none, _ => state

/-- Called for a `varDecl` initializer: seeds a point range when the
    initializer resolves to a known integer, otherwise leaves it unknown
    (never clears — the variable has no prior tracked range to go stale). -/
def applyDeclRange (ctx : VerifyCtx) (name : String) (init : Syntax.Expr) (state : FlowState)
    : FlowState :=
  match resolveExprInt ctx init with
  | some v =>
      let s1 := state.setRange name (IRange.point v)
      if v != 0 then s1.setNonZero name else s1.clearNonZero name
  | none => state

/-- Bounds checks over expressions (array index, memcpy-shaped sinks, and
    range invalidation/update on writes). -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  -- FEL-68: sizeof(expr)'s operand is never evaluated in C, so there's no
  -- array access, memcpy call, or write inside it to bounds-check.
  | .sizeOfExpr _ _ => state
  | .binOp op lhs rhs loc =>
      match op with
      | .addAssign | .subAssign | .mulAssign | .divAssign | .modAssign
      | .andAssign | .orAssign | .xorAssign | .shlAssign | .shrAssign =>
          let s1 := checkExpr ctx lhs state
          let s2 := checkExpr ctx rhs s1
          applyScalarCompound ctx op lhs rhs s2
      | .div | .mod =>
          let s1 := checkExpr ctx lhs state
          let s2 := checkExpr ctx rhs s1
          if isProvablyNonzero ctx s2 rhs then s2
          else
            s2.addViolation
              (mkDivByZeroViolation ctx loc expr (if op == .div then "division" else "modulo"))
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
