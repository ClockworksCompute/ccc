import CCC.Syntax.AST
import CCC.Syntax.PtrState

namespace CCC.Verify

/-- Read-only context available during verification. -/
structure VerifyCtx where
  structs : List Syntax.StructDef
  currentFun : String
  deriving Inhabited

/-- Per-function flow-sensitive verifier state. -/
structure FlowState where
  ptrStates  : List (String × Syntax.PtrState)
  varTypes   : List (String × Syntax.CType)
  bounds     : List (String × Nat)
  aliases    : List (String × String)   -- (alias, origin) pointer alias pairs
  evidence   : List Syntax.SafetyEvidence
  violations : List Syntax.SafetyViolation
  deriving Inhabited

namespace FlowState

def empty : FlowState := ⟨[], [], [], [], [], []⟩

def getPtr (state : FlowState) (name : String) : Option Syntax.PtrState :=
  (state.ptrStates.find? (·.1 == name)).map (·.2)

def setPtr (state : FlowState) (name : String) (ps : Syntax.PtrState) : FlowState :=
  { state with ptrStates := (name, ps) :: state.ptrStates.filter (·.1 != name) }

def getType (state : FlowState) (name : String) : Option Syntax.CType :=
  (state.varTypes.find? (·.1 == name)).map (·.2)

def setType (state : FlowState) (name : String) (ty : Syntax.CType) : FlowState :=
  { state with varTypes := (name, ty) :: state.varTypes.filter (·.1 != name) }

def getBound (state : FlowState) (name : String) : Option Nat :=
  (state.bounds.find? (·.1 == name)).map (·.2)

def setBound (state : FlowState) (name : String) (bound : Nat) : FlowState :=
  { state with bounds := (name, bound) :: state.bounds.filter (·.1 != name) }

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
  let mergedBounds : List (String × Nat) :=
    boundNames.foldl
      (fun acc name =>
        match a.getBound name, b.getBound name with
        | some ba, some bb => (name, Nat.min ba bb) :: acc
        | _, _ => acc)
      []

  -- Merge aliases: union, deduplicate
  let mergedAliases : List (String × String) :=
    (a.aliases ++ b.aliases).foldl
      (fun acc pair =>
        if acc.any (fun p => p.1 == pair.1 && p.2 == pair.2) then acc
        else pair :: acc)
      []

  { ptrStates := mergedPtrs
    varTypes := mergedTypes
    bounds := mergedBounds
    aliases := mergedAliases
    evidence := a.evidence ++ b.evidence
    violations := a.violations ++ b.violations }

end CCC.Verify
