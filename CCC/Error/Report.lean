/-
  CCC/Error/Report.lean — Error message formatting

  Consumes SafetyViolation and ProgramVerifyResult, produces human-readable
  error messages. This is the user-facing output layer.
-/

import CCC.Syntax.PtrState

namespace CCC.Error

open CCC.Syntax

/-- Get a specific line from source text (1-indexed). -/
def getSourceLine (source : String) (line : Nat) : Option String :=
  let lines := source.splitOn "\n"
  if line > 0 && line ≤ lines.length then
    lines[line - 1]?
  else
    none

/-- Format a SafetyProperty as a short label. -/
def propertyLabel : SafetyProperty → String
  | .bufferBounds    => "Buffer bounds violation"
  | .noUseAfterFree  => "Use-after-free"
  | .noDoubleFree    => "Double free"
  | .noNullDeref     => "Null pointer dereference"
  | .noStackOverflow => "Stack buffer overflow"

/-- Format a single violation with source context. -/
def formatViolation (v : SafetyViolation) (source : String) : String :=
  let header := s!"ERROR: Memory safety violation at line {v.loc.line}:"
  let srcLine := match getSourceLine source v.loc.line with
    | some l => s!"  {l.trimAscii.toString}"
    | none   => s!"  {v.expr}"
  let underline := "  " ++ String.ofList (List.replicate v.expr.length '^')
  let msg := s!"  {v.message}"
  let ctxLines := v.context.map (s!"  " ++ ·) |>.foldl (· ++ "\n" ++ ·) ""
  let suggestion := match v.suggestion with
    | some s => s!"\n  Fix: {s}"
    | none   => ""
  s!"{header}\n{srcLine}\n{underline}\n{msg}{ctxLines}{suggestion}"

/-- Count specific types of evidence. -/
private def countPtrOps (evidence : List SafetyEvidence) : Nat :=
  evidence.filter (fun e => match e with
    | .ptrLive _ _ => true
    | .nullChecked _ _ => true
    | _ => false) |>.length

private def countArrayChecks (evidence : List SafetyEvidence) : Nat :=
  evidence.filter (fun e => match e with
    | .staticBounds _ _ _ => true
    | .dynamicBoundsChecked _ _ => true
    | .stackBounded _ _ => true
    | _ => false) |>.length

private def countStaticBounds (evidence : List SafetyEvidence) : Nat :=
  evidence.filter (fun e => match e with
    | .staticBounds _ _ _ => true
    | .stackBounded _ _ => true
    | _ => false) |>.length

private def countDynamicBounds (evidence : List SafetyEvidence) : Nat :=
  evidence.filter (fun e => match e with
    | .dynamicBoundsChecked _ _ => true
    | _ => false) |>.length

/-- Format the rejection report for an unsafe program. -/
def formatResult (result : ProgramVerifyResult) (source : String) (filename : String) : String :=
  if result.isSafe then
    s!"Compiling {filename}... no violations found."
  else
    let violations := result.allViolations
    let formatted := violations.map (formatViolation · source)
    let header := s!"Compiling {filename}..."
    let body := formatted.foldl (· ++ "\n\n" ++ ·) ""
    let summary := s!"\n{violations.length} memory safety violation(s) found. Compilation aborted."
    s!"{header}{body}\n{summary}"

/-- Stage of compilation reached. -/
inductive CompileStage where
  | verified       -- safety checks passed, assembly generated (no linking)
  | linked (size : Nat) -- assembled and linked to binary with measured size
  deriving Repr, Inhabited

/-- Format the success report for a safe program. Stage-truthful: only claims
    what was actually achieved. -/
def formatSuccess (result : ProgramVerifyResult) (filename : String)
    (stage : CompileStage) : String :=
  let nFuns := result.totalFunctions
  let allEv := result.allEvidence
  let ptrOps := countPtrOps allEv
  let arrChecks := countArrayChecks allEv
  let staticB := countStaticBounds allEv
  let dynamicB := countDynamicBounds allEv
  let baseName := filename.replace ".c" ""
  let stageMsg := match stage with
    | .verified => s!"  ✓ Verified: {baseName} (assembly generated)"
    | .linked size =>
        let sizeStr := if size ≥ 1024 then s!"{size / 1024}KB" else s!"{size}B"
        s!"  ✓ Linked: {baseName} ({sizeStr})"
  s!"Compiling {filename}...\n" ++
  s!"  ✓ {nFuns} functions analyzed\n" ++
  s!"  ✓ {ptrOps} pointer operations verified\n" ++
  s!"  ✓ {arrChecks} array accesses verified ({staticB} static, {dynamicB} runtime-bounded)\n" ++
  s!"  ✓ 0 memory safety violations\n" ++
  stageMsg

end CCC.Error
