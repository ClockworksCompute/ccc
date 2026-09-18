import CCC.Verify.BoundsCheck
import CCC.Verify.PointerSafety
import CCC.Verify.NullCheck
import CCC.Verify.BranchAnalysis
import CCC.Verify.SymbolCheck

namespace CCC.Verify

-- ══════════════════════════════════════════════════════════════
-- FEL-48 (partial): whole-program "does this function free parameter i"
-- scan, consulted by PointerSafety at call sites. A coarse, unconditional,
-- non-path-sensitive textual scan — see the VerifyCtx docstring in
-- FlowState.lean for exactly what it does and does not model.
-- ══════════════════════════════════════════════════════════════

private partial def exprCallsFreeOn (name : String) (e : Syntax.Expr) : Bool :=
  match e with
  | .call "free" [.var n _] _ => n == name
  | .call _ args _ => args.any (exprCallsFreeOn name)
  | .binOp _ l r _ => exprCallsFreeOn name l || exprCallsFreeOn name r
  | .unOp _ o _ => exprCallsFreeOn name o
  | .index a i _ => exprCallsFreeOn name a || exprCallsFreeOn name i
  | .member o _ _ => exprCallsFreeOn name o
  | .arrow p _ _ => exprCallsFreeOn name p
  | .assign l r _ => exprCallsFreeOn name l || exprCallsFreeOn name r
  | .ternary c t e2 _ => exprCallsFreeOn name c || exprCallsFreeOn name t || exprCallsFreeOn name e2
  | .cast _ o _ => exprCallsFreeOn name o
  | .comma l r _ => exprCallsFreeOn name l || exprCallsFreeOn name r
  | .initList es _ => es.any (exprCallsFreeOn name)
  | .callFnPtr f args _ => exprCallsFreeOn name f || args.any (exprCallsFreeOn name)
  | _ => false

private partial def stmtCallsFreeOn (name : String) (s : Syntax.Stmt) : Bool :=
  match s with
  | .varDecl _ _ init _ =>
      match init with
      | some e => exprCallsFreeOn name e
      | none => false
  | .exprStmt e _ => exprCallsFreeOn name e
  | .ret v _ =>
      match v with
      | some e => exprCallsFreeOn name e
      | none => false
  | .ifElse c t e _ =>
      exprCallsFreeOn name c || t.any (stmtCallsFreeOn name) || e.any (stmtCallsFreeOn name)
  | .while_ c b _ => exprCallsFreeOn name c || b.any (stmtCallsFreeOn name)
  | .for_ i c st b _ =>
      (match i with | some s2 => stmtCallsFreeOn name s2 | none => false) ||
      (match c with | some e => exprCallsFreeOn name e | none => false) ||
      (match st with | some e => exprCallsFreeOn name e | none => false) ||
      b.any (stmtCallsFreeOn name)
  | .block ss _ => ss.any (stmtCallsFreeOn name)
  | .switch_ scrut cases _ =>
      exprCallsFreeOn name scrut ||
      cases.any (fun (_, body, _) => body.any (stmtCallsFreeOn name))
  | .doWhile b c _ => b.any (stmtCallsFreeOn name) || exprCallsFreeOn name c
  | .break_ _ | .continue_ _ | .emptyStmt _ | .goto_ _ _ => false
  | .label_ _ body _ => stmtCallsFreeOn name body

/-- For one function, the per-parameter "frees this parameter somewhere in
    the body" flags, in parameter order. -/
private def freeSummaryFor (f : Syntax.FunDef) : List Bool :=
  f.params.map (fun p => f.body.any (stmtCallsFreeOn p.name))

private def buildFreesParamTable (prog : Syntax.Program) : List (String × List Bool) :=
  prog.functions.map (fun f => (f.name, freeSummaryFor f))

-- ══════════════════════════════════════════════════════════════
-- Seeding flow state from function parameters.
-- ══════════════════════════════════════════════════════════════

private def ptrStateForParam (ty : Syntax.CType) : Option Syntax.PtrState :=
  match ty with
  | .pointer _ => some (.checkedLive none)
  -- An array-typed parameter decays to a pointer; its real capacity is
  -- whatever the caller actually passed, which we don't know at this
  -- function's entry. The old code asserted `.stackLocal (some n)` here,
  -- which confidently (and wrongly) treated every call site's buffer as
  -- being exactly `n` elements long — see FEL-48. Tracking it as unknown
  -- is honest: it stops bounds-checking the parameter rather than checking
  -- it against a size that isn't real. (The complete fix — checking the
  -- actual argument size at each call site — is the interprocedural
  -- summary work tracked in FEL-58.)
  | .array _ _ => some (.checkedLive none)
  | _ => none

private def initialRangeForParam (ty : Syntax.CType) : Option IRange :=
  match ty with
  | .unsigned _ => some (IRange.unknown.withLo 0)
  | .sizeT => some (IRange.unknown.withLo 0)
  | _ => none

/-- Seed flow state from function parameters. -/
def initFlowStateFromParams (params : List Syntax.Param) : FlowState :=
  params.foldl
    (fun st p =>
      let st1 := st.setType p.name p.ty
      let st2 :=
        match ptrStateForParam p.ty with
        | some ps => st1.setPtr p.name ps
        | none => st1
      match initialRangeForParam p.ty with
      | some r => st2.setRange p.name r
      | none => st2)
    FlowState.empty

private partial def branchEndsWithReturn (stmts : List Syntax.Stmt) : Bool :=
  match stmts.reverse with
  | [] => false
  | last :: _ =>
      match last with
      | .ret _ _ => true
      | .block inner _ => branchEndsWithReturn inner
      | _ => false

private def applyExprChecks (ctx : VerifyCtx) (expr : Syntax.Expr) (state : FlowState) : FlowState :=
  let s1 := PointerSafety.checkExpr ctx expr state
  let s2 := NullCheck.checkExpr ctx expr s1
  let s3 := BoundsCheck.checkExpr ctx expr s2
  s3

/-- Extract a bound-key from a variable or field expression. -/
private def boundKeyOf? (expr : Syntax.Expr) : Option String :=
  match expr with
  | .var name _ => some name
  | .arrow (.var obj _) field _ => some (boundKeyForField obj field)
  | .member (.var obj _) field _ => some (obj ++ "." ++ field)
  | _ => none

/-- State-aware transitive bound inference for loop conditions.
    When the condition is `lhs < rhs` (or `<=`) and `rhs` has a known
    (exclusive) upper bound in the flow state, propagate that bound to
    `lhs`. This handles patterns like `while (i < g->count)` where
    `g->count` was previously bounded by an early-return check. -/
private partial def inferTransitiveBounds (cond : Syntax.Expr) (state : FlowState) : FlowState :=
  match cond with
  | .binOp .lt lhs rhs _ =>
      match boundKeyOf? lhs, boundKeyOf? rhs with
      | some lhsKey, some rhsKey =>
          match (state.getRange rhsKey).bind (·.hi) with
          | some rhsHi =>
              let newHi := if rhsHi > 0 then rhsHi - 1 else 0
              state.tightenHiExclusive lhsKey newHi
          | none => state
      | _, _ => state
  | .binOp .le lhs rhs _ =>
      match boundKeyOf? lhs, boundKeyOf? rhs with
      | some lhsKey, some rhsKey =>
          match (state.getRange rhsKey).bind (·.hi) with
          | some rhsHi => state.tightenHiExclusive lhsKey rhsHi
          | none => state
      | _, _ => state
  | .binOp .and_ lhs rhs _ =>
      let s1 := inferTransitiveBounds lhs state
      inferTransitiveBounds rhs s1
  | _ => state

-- ══════════════════════════════════════════════════════════════
-- Loop fixpoint (FEL-43). A single-pass analysis of a loop body only ever
-- sees "iteration 1 starting from the pre-loop state" — a use-after-free
-- that only manifests on the second trip around a `while` is invisible.
-- We approximate a fixpoint: run the body a few times, WIDENING the
-- tracked state via `FlowState.merge` each round and discarding the
-- violations/evidence found during those warm-up rounds (otherwise the
-- exact same static bug would be reported once per warm-up iteration),
-- then run one final real pass whose findings are kept. Bounded fuel
-- (3 rounds) rather than a true fixpoint check — cheap and sufficient for
-- the pointer-state/range lattices in play here.
-- ══════════════════════════════════════════════════════════════

/-- Run `f`, then restore the violations/evidence that were on `st` before
    the call — i.e. keep `f`'s state-transition effect but discard whatever
    NEW findings it produced. -/
private def silently (f : FlowState → FlowState) (st : FlowState) : FlowState :=
  let preV := st.violations
  let preE := st.evidence
  let result := f st
  { result with violations := preV, evidence := preE }

/-- Like `FlowState.merge`, but keeps `a`'s violations/evidence verbatim
    instead of concatenating both sides — used internally by the fixpoint
    warm-up loop, where both sides are known to carry the same (silenced)
    findings and a real `merge` would double them. -/
private def mergeStateOnly (a b : FlowState) : FlowState :=
  { FlowState.merge a b with violations := a.violations, evidence := a.evidence }

/-- Iterate `oneIter` (one full loop-body pass, entry state → exit state)
    towards a fixpoint approximation, then run one real, violation-keeping
    pass from the settled state. `entry` must already carry every violation
    genuinely found before the loop — those survive unchanged. -/
private partial def fixpointBody (oneIter : FlowState → FlowState) (entry : FlowState)
    (fuel : Nat := 3) : FlowState :=
  let rec settle (cur : FlowState) (n : Nat) : FlowState :=
    match n with
    | 0 => cur
    | n' + 1 =>
        let afterSilent := silently oneIter cur
        settle (mergeStateOnly cur afterSilent) n'
  let settled := settle entry fuel
  let finalAfter := oneIter settled
  { FlowState.merge settled finalAfter with
      violations := finalAfter.violations
      evidence := finalAfter.evidence }

mutual

/-- Single-pass statement analysis. -/
partial def analyzeStmts (ctx : VerifyCtx) (stmts : List Syntax.Stmt) (state : FlowState) : FlowState :=
  match stmts with
  | [] => state
  | stmt :: rest =>
      let s1 := analyzeStmt ctx stmt state
      match stmt with
      | .ret _ _ => s1
      | _ => analyzeStmts ctx rest s1

partial def analyzeStmt (ctx : VerifyCtx) (stmt : Syntax.Stmt) (state : FlowState) : FlowState :=
  match stmt with
  | .varDecl name ty init _ =>
      let s1 := PointerSafety.handleVarDecl ctx name ty init state
      match init with
      | some expr =>
          let s2 := NullCheck.checkExpr ctx expr s1
          let s3 := BoundsCheck.checkExpr ctx expr s2
          BoundsCheck.applyDeclRange ctx name expr s3
      | none => s1

  | .exprStmt expr _ => applyExprChecks ctx expr state

  | .ret val _ =>
      match val with
      | some expr => applyExprChecks ctx expr state
      | none => state

  | .ifElse cond thenBody elseBody _ =>
      let sCond := applyExprChecks ctx cond state
      let (thenFacts, elseFacts) := extractFacts cond
      let thenStart := applyFacts thenFacts sCond
      let elseStart := applyFacts elseFacts sCond
      let thenEnd := analyzeStmts ctx thenBody thenStart
      let elseEnd := analyzeStmts ctx elseBody elseStart
      -- FEL-41: `analyzeStmts` only ever APPENDS violations/evidence, never
      -- reorders or removes them, so both branches' findings begin with an
      -- exact copy of `sCond`'s. Extract just the NEW findings each branch
      -- contributed so we can combine them without double-counting the
      -- shared prefix — and, critically, WITHOUT ever discarding a
      -- branch's findings just because that branch happens to `return`.
      let thenNewV := thenEnd.violations.drop sCond.violations.length
      let thenNewE := thenEnd.evidence.drop sCond.evidence.length
      let elseNewV := elseEnd.violations.drop sCond.violations.length
      let elseNewE := elseEnd.evidence.drop sCond.evidence.length
      let combinedV := sCond.violations ++ thenNewV ++ elseNewV
      let combinedE := sCond.evidence ++ thenNewE ++ elseNewE
      let thenReturns := branchEndsWithReturn thenBody
      let elseReturns := branchEndsWithReturn elseBody
      if thenReturns && !elseReturns then
        { elseEnd with violations := combinedV, evidence := combinedE }
      else if elseReturns && !thenReturns then
        { thenEnd with violations := combinedV, evidence := combinedE }
      else
        { FlowState.merge thenEnd elseEnd with violations := combinedV, evidence := combinedE }

  | .while_ cond body _ =>
      let (thenFacts, elseFacts) := extractFacts cond
      let oneIter : FlowState → FlowState := fun st =>
        let sCondIter := applyExprChecks ctx cond st
        let bodyStart := inferTransitiveBounds cond (applyFacts thenFacts sCondIter)
        analyzeStmts ctx body bodyStart
      let bodyResult := fixpointBody oneIter state
      let exitState := silently (fun st => applyFacts elseFacts (applyExprChecks ctx cond st)) state
      { FlowState.merge exitState bodyResult with
          violations := bodyResult.violations, evidence := bodyResult.evidence }

  | .for_ init cond step body _ =>
      let sInit :=
        match init with
        | some initStmt => analyzeStmt ctx initStmt state
        | none => state
      let thenFactsElseFacts : (List BranchFact) × (List BranchFact) :=
        match cond with
        | some condExpr => extractFacts condExpr
        | none => ([], [])
      let thenFacts := thenFactsElseFacts.1
      let elseFacts := thenFactsElseFacts.2
      let oneIter : FlowState → FlowState := fun st =>
        let sCond :=
          match cond with
          | some condExpr => applyExprChecks ctx condExpr st
          | none => st
        let bodyStart0 := applyFacts thenFacts sCond
        let bodyStart :=
          match cond with
          | some condExpr => inferTransitiveBounds condExpr bodyStart0
          | none => bodyStart0
        let bodyEnd0 := analyzeStmts ctx body bodyStart
        match step with
        | some stepExpr => applyExprChecks ctx stepExpr bodyEnd0
        | none => bodyEnd0
      let bodyResult := fixpointBody oneIter sInit
      let exitState := silently (fun st =>
          match cond with
          | some condExpr => applyFacts elseFacts (applyExprChecks ctx condExpr st)
          | none => st) sInit
      { FlowState.merge exitState bodyResult with
          violations := bodyResult.violations, evidence := bodyResult.evidence }

  | .block stmts _ => analyzeStmts ctx stmts state

  -- Phase 2 Stmt
  | .switch_ scrut cases _ =>
      -- Each case is analysed fresh from the switch-entry state rather than
      -- threading the previous case's exit state through (FEL-49 #3): the
      -- old sequential fold meant `case 1: free(p); break; case 2: *p=1;`
      -- was seen as "free, THEN dereference", a false use-after-free/
      -- double-free on the extremely common break-terminated switch shape.
      -- This trades soundness on genuine (break-less) fall-through for
      -- eliminating that false positive — a fall-through bug across cases
      -- is comparatively rare and, being a miss rather than a false alarm,
      -- is the safer direction to be wrong in for a tool people need to
      -- trust.
      let sCond := applyExprChecks ctx scrut state
      let caseEnds := cases.map (fun (_, body, _) => analyzeStmts ctx body sCond)
      caseEnds.foldl (fun acc caseEnd =>
        let newV := caseEnd.violations.drop sCond.violations.length
        let newE := caseEnd.evidence.drop sCond.evidence.length
        { FlowState.merge acc caseEnd with
            violations := acc.violations ++ newV
            evidence := acc.evidence ++ newE }) sCond

  | .doWhile body cond _ =>
      let oneIter : FlowState → FlowState := fun st =>
        applyExprChecks ctx cond (analyzeStmts ctx body st)
      fixpointBody oneIter state

  | .break_ _ | .continue_ _ | .emptyStmt _ => state

  | .goto_ _ _ => state

  | .label_ _ body _ => analyzeStmt ctx body state

end

/-- Does a function's body contain any `goto`/label control flow? Loop
    fixpointing (above) covers `while`/`for`/`do-while`; a hand-rolled loop
    built from `goto` is not modelled by the structural analysis at all
    (there is no general CFG here — see FEL-43's follow-up), so such
    functions are marked `degraded` rather than silently claiming full
    precision. -/
private partial def stmtHasGoto (s : Syntax.Stmt) : Bool :=
  match s with
  | .goto_ _ _ | .label_ _ _ _ => true
  | .ifElse _ t e _ => t.any stmtHasGoto || e.any stmtHasGoto
  | .while_ _ b _ => b.any stmtHasGoto
  | .for_ i _ _ b _ =>
      (match i with | some s2 => stmtHasGoto s2 | none => false) || b.any stmtHasGoto
  | .block ss _ => ss.any stmtHasGoto
  | .switch_ _ cases _ => cases.any (fun (_, body, _) => body.any stmtHasGoto)
  | .doWhile b _ _ => b.any stmtHasGoto
  | _ => false

/-- Verify one function body. -/
def verifyFunction (ctx : VerifyCtx) (f : Syntax.FunDef) : Syntax.FunVerifyResult :=
  let initState := initFlowStateFromParams f.params
  let finalState := analyzeStmts ctx f.body initState
  let status : Syntax.VerifyStatus :=
    if f.body.any stmtHasGoto then .degraded else .verified
  { funName := f.name
    status := status
    violations := finalState.violations
    evidence := finalState.evidence }

/-- Verify all functions and produce a report. -/
def verifyProgramReport (prog : Syntax.Program) : Syntax.ProgramVerifyResult :=
  -- Phase 0: Symbol validation (undefined functions, arity mismatches)
  let symbolViolations := SymbolCheck.checkProgram prog
  -- Phase 0.5: coarse whole-program "frees its parameter" summaries (FEL-48)
  let freesTable := buildFreesParamTable prog
  -- Phase 1: Per-function flow-sensitive analysis
  let baseCtx : VerifyCtx := { structs := prog.structs, currentFun := "", funcFreesParam := freesTable }
  let results : List Syntax.FunVerifyResult :=
    prog.functions.map (fun f =>
      verifyFunction { baseCtx with currentFun := f.name } f)
  -- Prepend symbol violations as a synthetic result
  let symbolResult : Syntax.FunVerifyResult :=
    { funName := "program"
      status := .verified
      violations := symbolViolations
      evidence := [] }
  { results := if symbolViolations.isEmpty then results
               else symbolResult :: results }

end CCC.Verify
