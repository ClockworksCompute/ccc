import CCC.Syntax.AST
import CCC.Syntax.PtrState
import CCC.Verify.Range

namespace CCC.Verify

/-- Read-only context available during verification.

    `funcFreesParam` is a coarse whole-program summary (FEL-48, partial):
    for each user-defined function name, whether a direct (unconditional or
    conditional — this scan does not distinguish) call to `free()` on each
    parameter position appears anywhere in its body. It lets a call site
    treat `release(p); *p = 1;` as a use-after-free even though `free` was
    called inside `release`, not directly. This is NOT a full call-graph
    fixed point (recursive functions and multi-hop aliasing are not
    modelled) — see FEL-58 for the complete interprocedural design. -/
structure VerifyCtx where
  structs : List Syntax.StructDef
  currentFun : String
  funcFreesParam : List (String × List Bool) := []
  -- FEL-56/57/58 (libheif-class detection, scoped): the whole program, so
  -- the symbolic-bounds mechanism (CCC/Verify/Canon.lean) can resolve
  -- negation-wrapper function calls, and a coarse whole-program
  -- "pointer parameter capacity = product of two other parameters"
  -- inference (see `paramCapacity` below) can look up a callee's own
  -- parameter names.
  program : Syntax.Program := { structs := [], unions := [], enums := [], typedefs := [],
                                 globals := [], externs := [], functions := [] }
  -- For (fn, pointerParamIdx): the callee's OWN parameter names (by
  -- position) whose product is that pointer parameter's byte capacity,
  -- inferred from every call site consistently passing an argument there
  -- whose tracked allocation size is exactly that product (see
  -- `Verify.buildParamCapacityTable`). Scoped to this one "(ptr, width,
  -- height)" parameter-group idiom — NOT a general interprocedural
  -- summary system (that's the rest of FEL-58).
  paramCapacity : List (String × List (Nat × (String × String))) := []
  -- Name -> 0-based parameter index, for the CURRENT function only (set
  -- once per `verifyFunction` call) — lets a checker ask "is this
  -- variable one of my OWN parameters, and if so which one" without
  -- needing the full `FunDef` threaded everywhere.
  currentParamIndex : List (String × Nat) := []
  deriving Inhabited

namespace VerifyCtx

/-- Does the named function free its `idx`-th parameter (0-based) somewhere
    in its body, per the coarse whole-program scan? -/
def freesParamAt (ctx : VerifyCtx) (fn : String) (idx : Nat) : Bool :=
  match ctx.funcFreesParam.find? (·.1 == fn) with
  | some (_, flags) => flags.getD idx false
  | none => false

/-- The inferred (widthParamName, heightParamName) for a pointer parameter
    at `idx` of the CURRENT function, if the whole-program scan found one. -/
def capacityParamsAt (ctx : VerifyCtx) (fn : String) (idx : Nat) : Option (String × String) :=
  match ctx.paramCapacity.find? (·.1 == fn) with
  | some (_, entries) => (entries.find? (·.1 == idx)).map (·.2)
  | none => none

end VerifyCtx

/-- Per-function flow-sensitive verifier state. -/
structure FlowState where
  ptrStates  : List (String × Syntax.PtrState)
  varTypes   : List (String × Syntax.CType)
  bounds     : List (String × IRange)
  aliases    : List (String × String)   -- (alias, origin) pointer alias pairs
  -- Keys (same access-path scheme as `bounds`) known to be nonzero at this
  -- point — a separate, coarser fact than an `IRange` (which can't cleanly
  -- represent "any value except 0" when the surrounding range is otherwise
  -- unconstrained). Used to prove a division/modulo divisor safe without
  -- needing to know its sign or a tight bound — established by `x != 0`
  -- (or the false branch of `x == 0`) on ANY integer key, not just
  -- pointers (unlike `ptrStates`/`ptrNonNull`, which only track pointer
  -- liveness).
  nonZeroKeys : List String
  -- FEL-56/57/58 (scoped symbolic bounds): canon-string facts "lhs <= rhs"
  -- (both sides are `CCC.Verify.canon` output, so e.g. a plain variable's
  -- key is just its name, and a sum's key is the canonicalized sum). See
  -- Canon.lean's docstring for exactly what canon-equality does and does
  -- not prove; consulted by BoundsCheck's symbolic 2-D index check and
  -- kept sound by the same kill-on-write discipline as `bounds`/
  -- `nonZeroKeys` (cleared on any write not recognized as preserving it).
  exprBounds : List (String × String)
  -- Last-assigned expression per key, consulted (bounded, via
  -- `CCC.Verify.canon`'s `fuel` parameter) to canonicalize an expression
  -- "as if" a variable's definition were inlined — see Canon.lean's
  -- docstring. NOT merged across branches (kept empty after any
  -- `FlowState.merge`): only meaningful within the single straight-line
  -- sequence where it was established, which is all the one scoped use
  -- site (BoundsCheck's `transferExprBoundOnAssign`) needs.
  symbolicDefs : List (String × Syntax.Expr)
  evidence   : List Syntax.SafetyEvidence
  violations : List Syntax.SafetyViolation
  deriving Inhabited

namespace FlowState

def empty : FlowState := ⟨[], [], [], [], [], [], [], [], []⟩

def getPtr (state : FlowState) (name : String) : Option Syntax.PtrState :=
  (state.ptrStates.find? (·.1 == name)).map (·.2)

def setPtr (state : FlowState) (name : String) (ps : Syntax.PtrState) : FlowState :=
  { state with ptrStates := (name, ps) :: state.ptrStates.filter (·.1 != name) }

def getType (state : FlowState) (name : String) : Option Syntax.CType :=
  (state.varTypes.find? (·.1 == name)).map (·.2)

def setType (state : FlowState) (name : String) (ty : Syntax.CType) : FlowState :=
  { state with varTypes := (name, ty) :: state.varTypes.filter (·.1 != name) }

/-- Get the tracked range for a key (variable name or access-path key like "obj->field"). -/
def getRange (state : FlowState) (name : String) : Option IRange :=
  (state.bounds.find? (·.1 == name)).map (·.2)

/-- Backwards-compatible alias: the old API name. -/
def getBound (state : FlowState) (name : String) : Option IRange := state.getRange name

def setRange (state : FlowState) (name : String) (r : IRange) : FlowState :=
  { state with bounds := (name, r) :: state.bounds.filter (·.1 != name) }

def setBound (state : FlowState) (name : String) (r : IRange) : FlowState := state.setRange name r

/-- Remove all tracked range information for a key (used when a write invalidates
    facts we cannot precisely re-derive). -/
def clearRange (state : FlowState) (name : String) : FlowState :=
  { state with bounds := state.bounds.filter (·.1 != name) }

/-- Remove range information for every key with the given string prefix
    (used when a struct pointer is reassigned: kill every "obj->..." key). -/
def clearRangesWithPrefix (state : FlowState) (pfx : String) : FlowState :=
  { state with bounds := state.bounds.filter (fun kv => !(kv.1.startsWith pfx)) }

/-- Only tighten the upper bound of `name`'s range, leaving the lower bound
    (if any) untouched. This is what a `i < n` branch fact should do — it must
    not erase a previously-established `i ≥ 0` fact. -/
def tightenHiExclusive (state : FlowState) (name : String) (v : Int) : FlowState :=
  let cur := (state.getRange name).getD IRange.unknown
  state.setRange name (cur.withHiExclusive v)

/-- Only tighten the lower bound of `name`'s range. -/
def tightenLo (state : FlowState) (name : String) (v : Int) : FlowState :=
  let cur := (state.getRange name).getD IRange.unknown
  state.setRange name (cur.withLo v)

def isNonZero (state : FlowState) (key : String) : Bool :=
  state.nonZeroKeys.any (· == key)

def setNonZero (state : FlowState) (key : String) : FlowState :=
  if state.isNonZero key then state
  else { state with nonZeroKeys := key :: state.nonZeroKeys }

def clearNonZero (state : FlowState) (key : String) : FlowState :=
  { state with nonZeroKeys := state.nonZeroKeys.filter (· != key) }

def getExprBound (state : FlowState) (canonKey : String) : Option String :=
  (state.exprBounds.find? (·.1 == canonKey)).map (·.2)

def setExprBound (state : FlowState) (canonKey boundCanon : String) : FlowState :=
  { state with exprBounds := (canonKey, boundCanon) :: state.exprBounds.filter (·.1 != canonKey) }

def clearExprBound (state : FlowState) (canonKey : String) : FlowState :=
  { state with exprBounds := state.exprBounds.filter (·.1 != canonKey) }

/-- Clear every exprBound fact whose canonical key or bound MENTIONS
    `name` as a substring token (over-approximate but sound: this can only
    drop facts, never fabricate one, and dropping a fact can only make a
    later check more conservative). Used when a variable's write can't be
    shown to preserve any fact that names it (see BoundsCheck's
    canon-based transfer, which handles the one case that DOES preserve
    facts: a write whose canon exactly matches an existing fact's key). -/
def clearExprBoundsMentioning (state : FlowState) (name : String) : FlowState :=
  let keep := fun (kv : String × String) =>
    (kv.1.splitOn name).length == 1 && (kv.2.splitOn name).length == 1
  { state with exprBounds := state.exprBounds.filter keep }

def setSymbolicDef (state : FlowState) (key : String) (def_ : Syntax.Expr) : FlowState :=
  { state with symbolicDefs := (key, def_) :: state.symbolicDefs.filter (·.1 != key) }

def addViolation (state : FlowState) (v : Syntax.SafetyViolation) : FlowState :=
  { state with violations := state.violations ++ [v] }

def addEvidence (state : FlowState) (e : Syntax.SafetyEvidence) : FlowState :=
  { state with evidence := state.evidence ++ [e] }

/-- Register that `alias` points to the same allocation as `origin`. -/
def addAlias (state : FlowState) (alias origin : String) : FlowState :=
  if alias == origin then state
  else { state with aliases := (alias, origin) :: state.aliases }

/-- Remove all alias links involving `name` (used when pointer is reassigned). -/
def removeAliasesFor (state : FlowState) (name : String) : FlowState :=
  { state with aliases := state.aliases.filter (fun p => p.1 != name && p.2 != name) }

/-- Get all names in the alias group containing `name` (transitive closure).
    Uses bounded iteration (fuel) to guarantee termination. -/
def getAliasGroup (state : FlowState) (name : String) : List String :=
  let rec expand (group : List String) (fuel : Nat) : List String :=
    match fuel with
    | 0 => group
    | fuel' + 1 =>
        let next := state.aliases.foldl (fun acc (a, b) =>
          let aIn := acc.any (· == a)
          let bIn := acc.any (· == b)
          match aIn, bIn with
          | true, false => b :: acc
          | false, true => a :: acc
          | _, _ => acc) group
        if next.length == group.length then group
        else expand next fuel'
  expand [name] 8  -- fuel=8 handles chains up to 8 deep

private def insertName (names : List String) (name : String) : List String :=
  if names.any (· == name) then names else name :: names

private def collectNames {α : Type} (entries : List (String × α)) : List String :=
  entries.foldl (fun acc entry => insertName acc entry.1) []

private def collectAllNames {α β : Type}
    (a : List (String × α)) (b : List (String × β)) : List String :=
  (collectNames a).foldl insertName (collectNames b)

private def mergeSizeOpt (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (Nat.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

private def mergePtrState (a b : Syntax.PtrState) : Syntax.PtrState :=
  let size := mergeSizeOpt (Syntax.PtrState.knownSize a) (Syntax.PtrState.knownSize b)
  match a, b with
  | .freed, _ | _, .freed => .freed
  | .nullable _, _ | _, .nullable _ => .nullable size
  | .checkedLive _, .checkedLive _ => .checkedLive size
  | .checkedLive _, .heapLive _ | .heapLive _, .checkedLive _ => .heapLive size
  | .heapLive _, .heapLive _ => .heapLive size
  | .stackLocal _, .stackLocal _ => .stackLocal size
  | .uninitialized, _ | _, .uninitialized => .uninitialized
  | _, _ => .uninitialized

end FlowState

/-- Merge two flow states after if/else. Conservative: worst case per variable. -/
def FlowState.merge (a b : FlowState) : FlowState :=
  let ptrNames : List String := FlowState.collectAllNames a.ptrStates b.ptrStates
  let mergedPtrs : List (String × Syntax.PtrState) :=
    ptrNames.foldl
      (fun acc name =>
        match a.getPtr name, b.getPtr name with
        | some pa, some pb => (name, FlowState.mergePtrState pa pb) :: acc
        | some pa, none => (name, pa) :: acc
        | none, some pb => (name, pb) :: acc
        | none, none => acc)
      []

  let typeNames : List String := FlowState.collectAllNames a.varTypes b.varTypes
  let mergedTypes : List (String × Syntax.CType) :=
    typeNames.foldl
      (fun acc name =>
        match a.getType name, b.getType name with
        | some ta, some tb =>
            let ty : Syntax.CType := if ta == tb then ta else ta
            (name, ty) :: acc
        | some ta, none => (name, ta) :: acc
        | none, some tb => (name, tb) :: acc
        | none, none => acc)
      []

  let boundNames : List String := FlowState.collectAllNames a.bounds b.bounds
  -- Sound merge: a range is only kept when BOTH branches know one for this
  -- key. If either branch cleared it (or never had it), the joined value is
  -- unknown — propagating a single-sided bound here would be unsound (the
  -- branch that lacks it may have reassigned the variable to anything).
  let mergedBounds : List (String × IRange) :=
    boundNames.foldl
      (fun acc name =>
        match a.getRange name, b.getRange name with
        | some ra, some rb => (name, IRange.merge ra rb) :: acc
        | _, _ => acc)
      []

  -- Merge aliases: union, deduplicate
  let mergedAliases : List (String × String) :=
    (a.aliases ++ b.aliases).foldl
      (fun acc pair =>
        if acc.any (fun p => p.1 == pair.1 && p.2 == pair.2) then acc
        else pair :: acc)
      []

  -- Nonzero-ness is only kept when BOTH branches established it — same
  -- soundness reasoning as `mergedBounds` above.
  let mergedNonZero : List String :=
    a.nonZeroKeys.filter (fun k => b.isNonZero k)

  -- Same for exprBounds: keep a fact only when both branches agree on the
  -- exact same bound for the exact same key.
  let mergedExprBounds : List (String × String) :=
    a.exprBounds.filter (fun kv => b.getExprBound kv.1 == some kv.2)

  { ptrStates := mergedPtrs
    varTypes := mergedTypes
    bounds := mergedBounds
    aliases := mergedAliases
    nonZeroKeys := mergedNonZero
    exprBounds := mergedExprBounds
    symbolicDefs := []
    evidence := a.evidence ++ b.evidence
    violations := a.violations ++ b.violations }

end CCC.Verify
