import CCC.Verify.TypeSize

namespace CCC.Verify.PointerSafety

/-- Access-path key for a pointer-valued expression: a plain variable, or a
    struct field reached through `.`/`->` off a plain variable. Using the
    same key scheme as the bounds-range tracker (FEL-44/FEL-57 groundwork) so
    a pointer stored in a struct field (`s.p`, `s->p`) is tracked exactly
    like a local variable instead of silently falling through unchecked. -/
private def ptrKeyOfExpr? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | .arrow (.var obj _) field _ => some (obj ++ "->" ++ field)
  | .member (.var obj _) field _ => some (obj ++ "." ++ field)
  | _ => none

private def isPointerTy (ty : Syntax.CType) : Bool :=
  match ty with
  | .pointer _ => true
  | _ => false

/-- Is this expression a spelling of the null pointer constant? Mirrors
    `BranchAnalysis`'s recognizer so `p = NULL;` (which preprocesses to a
    cast of an int literal) is treated the same as `p = 0;` (FEL-49 #2). -/
private def isZeroLiteral (expr : Syntax.Expr) : Bool :=
  match expr with
  | .nullLit _ => true
  | .intLit v _ => v == 0
  | .cast _ (.intLit v _) _ => v == 0
  | .cast _ (.nullLit _) _ => true
  | _ => false

/-- Classify a call as a fresh-allocation call (malloc/calloc/strdup/
    aligned_alloc), returning its known size if resolvable — `none` for the
    size means "allocated, but we don't know how much" (FEL-47: this must
    still be tracked as `nullable`, not silently dropped to `uninitialized`
    the way an unresolvable `malloc(n)` used to be). -/
private def allocCallInfo? (ctx : VerifyCtx) (expr : Syntax.Expr) : Option (Option Nat) :=
  match expr with
  | .call "malloc" [sizeExpr] _ => some (resolveExprNat ctx sizeExpr)
  | .call "calloc" [nExpr, szExpr] _ =>
      let sz := match resolveExprNat ctx nExpr, resolveExprNat ctx szExpr with
        | some n, some s => some (n * s)
        | _, _ => none
      some sz
  | .call "strdup" [_] _ => some none
  | .call "aligned_alloc" [_alignExpr, sizeExpr] _ => some (resolveExprNat ctx sizeExpr)
  | _ => none

/-- `realloc(ptr, size)`: the old allocation (and its whole alias group) is
    freed, and a fresh nullable pointer of the new size is produced. -/
private def reallocCallInfo? (ctx : VerifyCtx) (expr : Syntax.Expr)
    : Option (Syntax.Expr × Option Nat) :=
  match expr with
  | .call "realloc" [ptrExpr, sizeExpr] _ => some (ptrExpr, resolveExprNat ctx sizeExpr)
  | _ => none

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

private def mkUnresolvedDerefViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    : Syntax.SafetyViolation :=
  { property := .noUseAfterFree
    loc := loc
    expr := reprStr expr
    message := "Cannot verify liveness of this pointer expression (not a tracked variable or struct field)"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some "Rewrite via a named pointer variable so CCC can track its lifetime, or add an explicit bounds/liveness check" }

private def mkUninitDerefViolation (ctx : VerifyCtx) (loc : Syntax.Loc) (expr : Syntax.Expr)
    (name : String) : Syntax.SafetyViolation :=
  { property := .noNullDeref
    loc := loc
    expr := reprStr expr
    message := s!"Dereference of pointer '{name}' that was never initialized"
    context := [s!"function: {ctx.currentFun}"]
    suggestion := some s!"Initialize '{name}' (e.g. via malloc, or address-of a valid object) before dereferencing" }

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

/-- Pointer liveness check for a dereference/index/arrow whose base is
    `ptrExpr`. `fullExpr`/`loc` identify the overall access for reporting.

    FEL-44: an unresolvable base (pointer arithmetic, a call result, a
    double dereference, …) used to be silently accepted because there was
    nothing to look up. That is a soundness hole — we now report it as a
    "cannot verify" violation instead, and a resolved-but-`uninitialized`
    pointer (declared but never assigned) is now flagged too. -/
private def checkDereferenceable (ctx : VerifyCtx) (state : FlowState)
    (ptrExpr : Syntax.Expr) (fullExpr : Syntax.Expr) (loc : Syntax.Loc) : FlowState :=
  match ptrKeyOfExpr? ptrExpr with
  | some name =>
      match state.getPtr name with
      | some .freed => state.addViolation (mkUseAfterFreeViolation ctx loc fullExpr)
      | some .uninitialized => state.addViolation (mkUninitDerefViolation ctx loc fullExpr name)
      | some ps =>
          if Syntax.PtrState.isDereferenceable ps then
            state.addEvidence (.ptrLive name ps)
          else
            -- `.nullable` falls here; NullCheck reports the null-deref for it.
            state
      | none =>
          -- No pointer state at all: check if the variable has a known
          -- non-pointer type (a real bug: `*x` on an `int`), otherwise this
          -- is a name we simply never modelled (e.g. a global) — leave it
          -- to whatever narrower check applies rather than over-claiming.
          match state.getType name with
          | some ty =>
              if isPointerTy ty then state
              else state.addViolation (mkDerefNonPointerViolation ctx loc fullExpr name ty)
          | none => state
  | none =>
      state.addViolation (mkUnresolvedDerefViolation ctx loc fullExpr)

private def applyFreeTransition (ctx : VerifyCtx) (state : FlowState)
    (arg : Syntax.Expr) (fullExpr : Syntax.Expr) (loc : Syntax.Loc) : FlowState :=
  match ptrKeyOfExpr? arg with
  | some name =>
      match state.getPtr name with
      | some .freed => state.addViolation (mkDoubleFreeViolation ctx loc fullExpr)
      | some (.stackLocal _) => state.addViolation (mkInvalidFreeViolation ctx loc fullExpr)
      | some (.uninitialized) => state.addViolation (mkInvalidFreeViolation ctx loc fullExpr)
      | some _ =>
          -- Mark the freed name AND all its aliases as freed
          let group := state.getAliasGroup name
          group.foldl (fun (st : FlowState) n => st.setPtr n .freed) state
      | none => state
  | none => state

/-- FEL-48 (partial interprocedural step): if `fn` is known (via the
    whole-program `funcFreesParam` scan) to call `free()` on one of its
    parameters, propagate that transition to the matching argument at this
    call site — so `release(p); *p = 1;` is caught even though the actual
    `free` call is textually inside `release`, not here. -/
private def applyCalleeFreeSummaries (ctx : VerifyCtx) (fn : String) (args : List Syntax.Expr)
    (fullExpr : Syntax.Expr) (loc : Syntax.Loc) (state : FlowState) : FlowState :=
  let rec go (idx : Nat) (remaining : List Syntax.Expr) (st : FlowState) : FlowState :=
    match remaining with
    | [] => st
    | a :: rest =>
        let st' := if ctx.freesParamAt fn idx then applyFreeTransition ctx st a fullExpr loc else st
        go (idx + 1) rest st'
  go 0 args state

/-- Shared transition for "pointer variable/field is (re)assigned to `rhs`":
    used by both a `varDecl` initializer and a plain `lhs = rhs` assignment.
    Handles fresh allocation (malloc/calloc/strdup/aligned_alloc), `realloc`
    (frees the old allocation's alias group first), aliasing a live pointer,
    and assignment of a null constant (any spelling). -/
private def transitionPtrWrite (ctx : VerifyCtx) (state : FlowState) (name : String)
    (rhs : Syntax.Expr) : FlowState :=
  match allocCallInfo? ctx rhs with
  | some sizeOpt => (state.removeAliasesFor name).setPtr name (.nullable sizeOpt)
  | none =>
      match reallocCallInfo? ctx rhs with
      | some (origPtr, sizeOpt) =>
          let s1 :=
            match ptrKeyOfExpr? origPtr with
            | some oldName =>
                let group := state.getAliasGroup oldName
                group.foldl (fun (st : FlowState) n => st.setPtr n .freed) state
            | none => state
          (s1.removeAliasesFor name).setPtr name (.nullable sizeOpt)
      | none =>
          match rhs with
          | .var rhsName _ =>
              match state.getPtr rhsName with
              | some rhsState =>
                  let s1 := state.removeAliasesFor name
                  let s2 := s1.setPtr name rhsState
                  s2.addAlias name rhsName
              | none => state
          | _ =>
              if isZeroLiteral rhs then
                (state.removeAliasesFor name).setPtr name (.nullable none)
              else state

/-- Pointer liveness checks over expressions (use-after-free + free
    transitions + allocation/alias tracking on write). -/
partial def checkExpr (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  match expr with
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => state
  -- FEL-68: sizeof(expr)'s operand is never evaluated in C
  -- (`sizeof(*null_ptr)` is well-defined and never dereferences), so no
  -- use-after-free/double-free tracking applies inside it either.
  | .sizeOfExpr _ _ => state
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
        applyCalleeFreeSummaries ctx fn args expr loc s1
  | .assign lhs rhs _loc =>
      let s1 := checkExpr ctx lhs state
      let s2 := checkExpr ctx rhs s1
      match ptrKeyOfExpr? lhs with
      | some name =>
          match s2.getType name with
          | some lhsTy => if isPointerTy lhsTy then transitionPtrWrite ctx s2 name rhs else s2
          | none =>
              -- No declared scalar type for this key (typical for a struct
              -- field like `s.p`, since field types aren't in `varTypes`):
              -- only treat as a pointer transition when the RHS is itself
              -- clearly pointer-shaped, so we don't misfire on plain
              -- integer field assignments like `r->len = 9999`.
              match allocCallInfo? ctx rhs, reallocCallInfo? ctx rhs, rhs with
              | some _, _, _ => transitionPtrWrite ctx s2 name rhs
              | _, some _, _ => transitionPtrWrite ctx s2 name rhs
              | _, _, .var rhsName _ =>
                  if (s2.getPtr rhsName).isSome then transitionPtrWrite ctx s2 name rhs else s2
              | _, _, _ => s2
      | none => s2
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
        | .pointer _ => transitionPtrWrite ctx s1 name initExpr
        | _ => s1
      s2
  | none => typedState

end CCC.Verify.PointerSafety
