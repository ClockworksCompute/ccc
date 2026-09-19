import CCC.Verify.BoundsCheck
import CCC.Verify.PointerSafety
import CCC.Verify.NullCheck
import CCC.Verify.BranchAnalysis
import CCC.Verify.SymbolCheck
import CCC.Verify.Canon

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

/-- Seed flow state from function parameters. Also seeds, for every
    parameter, the trivial fact `name <= "@name"` — an immutable marker
    (`canon` never produces a `@`-prefixed key, so it can't collide with a
    real expression) standing for "this parameter's value as passed by
    the caller". True by construction at function entry; what makes it
    useful is that `transferExprBoundOnAssign`'s self-subtraction step
    (FEL-56/57/58) can carry it forward across a `W = W - offset`-shaped
    reassignment, and `clipPostcondition` across the "saturating clip"
    idiom — both are exactly the shapes libheif's overlay clipping uses to
    shrink `in_w`/`in_h` before they're used as a flattened-index capacity
    (`BoundsCheck.check2DIndex`), where the CALLER's original argument —
    not whatever the parameter has been reassigned to by the time of the
    access — is the value that actually bounds the allocation. -/
def initFlowStateFromParams (params : List Syntax.Param) : FlowState :=
  params.foldl
    (fun st p =>
      let st1 := st.setType p.name p.ty
      let st2 :=
        match ptrStateForParam p.ty with
        | some ps => st1.setPtr p.name ps
        | none => st1
      let st3 :=
        match initialRangeForParam p.ty with
        | some r => st2.setRange p.name r
        | none => st2
      st3.setExprBound p.name ("@" ++ p.name))
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

/-- Parallel to `inferTransitiveBounds`, but for the scoped symbolic
    exprBounds table (FEL-56/57/58): unconditionally records
    `canon(lhs) <= canon(rhs)` for a `<`/`<=` loop condition, regardless of
    whether either side is a plain tracked variable or has a numeric
    bound. This is what lets `while (col < in_w)` relate `col` to `in_w`
    symbolically even though `in_w` is a parameter with no numeric value —
    see `CCC/Verify/Canon.lean`'s docstring for what canon-equality does
    and does not prove. -/
private def inferExprBoundFromCond (ctx : VerifyCtx) (cond : Syntax.Expr) (state : FlowState)
    : FlowState :=
  match cond with
  | .binOp .lt lhs rhs _ => state.setExprBound (canon ctx.program lhs) (canon ctx.program rhs)
  | .binOp .le lhs rhs _ => state.setExprBound (canon ctx.program lhs) (canon ctx.program rhs)
  | .binOp .and_ lhs rhs _ =>
      inferExprBoundFromCond ctx rhs (inferExprBoundFromCond ctx lhs state)
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

-- ══════════════════════════════════════════════════════════════
-- FEL-56/57/58 (libheif-class detection, scoped): recognize the
-- "saturating clip" idiom and a coarse interprocedural pointer-capacity
-- inference. See CCC/Verify/Canon.lean's docstring for the soundness
-- contract these build on. Neither is a general relational/interprocedural
-- system — see FEL-56/57/58 in Linear for what's still open.
-- ══════════════════════════════════════════════════════════════

/-- Assignment statements appearing directly in a statement list (not
    inside a nested loop/if — this idiom's clip assignment is always a
    single top-level statement in the guard's body). -/
private partial def collectTopLevelAssigns (stmts : List Syntax.Stmt)
    : List (Syntax.Expr × Syntax.Expr) :=
  (stmts.map (fun s =>
    match s with
    | .exprStmt (.assign lhs rhs _) _ => [(lhs, rhs)]
    | .block ss _ => collectTopLevelAssigns ss
    | _ => [])).flatten

private def firstSome {α β : Type} (xs : List α) (f : α → Option β) : Option β :=
  match xs with
  | [] => none
  | x :: rest => match f x with | some v => some v | none => firstSome rest f

/-- `if (SUM > BOUND) { KEY := BOUND - OTHER; }` with no else, where `SUM`
    is structurally `OTHER + KEY` (either order) — establishes the
    postcondition `OTHER + KEY <= BOUND` regardless of which branch
    executes: by the negated condition if not taken, algebraically (the
    subtraction exactly cancels) if taken. Returns
    `(canon(OTHER+KEY), canon(BOUND), canon(KEY))` on a match — the third
    element lets the caller ALSO chain KEY's own pre-existing bound
    forward across this statement (see the `.ifElse` case below): KEY's
    new value is <= its old value in BOTH branches here (unchanged in the
    implicit else; `BOUND - OTHER` is exactly what the guard condition
    `OTHER + KEY_old > BOUND` proves is smaller than `KEY_old` in the
    then-branch), so whatever KEY was already known to be bounded by
    remains a valid bound after this idiom, however many times removed
    from the parameter's original entry value. This is the general,
    reusable "clip idiom" this ticket's corpus entry needs — see
    `docs/corpus-results.md` / Linear FEL-56 for exactly what it does and
    does not prove. -/
private def clipPostcondition (ctx : VerifyCtx) (cond : Syntax.Expr)
    (thenBody elseBody : List Syntax.Stmt) : Option (String × String × String) :=
  if !elseBody.isEmpty then none else
  match cond with
  | .binOp op sumExpr boundExpr _ =>
      if op != .gt && op != .ge then none else
      match sumExpr with
      | .binOp .add opA opB _ =>
          let assigns := collectTopLevelAssigns thenBody
          firstSome assigns (fun (lhs, rhs) =>
            let keyC := canon ctx.program lhs
            let otherOpt : Option Syntax.Expr :=
              if canon ctx.program opA == keyC then some opB
              else if canon ctx.program opB == keyC then some opA
              else none
            match otherOpt with
            | none => none
            | some otherExpr =>
                let rhs' := match rhs with
                  | .cast _ inner _ => inner
                  | _ => rhs
                match rhs' with
                | .binOp .sub b' o' _ =>
                    if canon ctx.program b' == canon ctx.program boundExpr &&
                       canon ctx.program o' == canon ctx.program otherExpr then
                      some (canon ctx.program (Syntax.Expr.binOp .add otherExpr lhs { line := 0, col := 0 }),
                            canon ctx.program boundExpr,
                            keyC)
                    else none
                | _ => none)
      | _ => none
  | _ => none

/-- Every `varDecl`/assignment of the shape `name = malloc(A*B)` /
    `name = calloc(A,B)` inside one function's body (syntactic only, no
    FlowState needed — used only to build the whole-program capacity
    table below). -/
private partial def stmtMallocFactors (s : Syntax.Stmt)
    : List (String × Syntax.Expr × Syntax.Expr) :=
  let ofInit (name : String) (initExpr : Syntax.Expr) : List (String × Syntax.Expr × Syntax.Expr) :=
    match initExpr with
    | .call "malloc" [.binOp .mul a b _] _ => [(name, a, b)]
    | .call "calloc" [a, b] _ => [(name, a, b)]
    | _ => []
  match s with
  | .varDecl name _ (some initExpr) _ => ofInit name initExpr
  | .exprStmt (.assign (.var name _) rhs _) _ => ofInit name rhs
  | .block ss _ => (ss.map stmtMallocFactors).flatten
  | .ifElse _ t e _ => (t.map stmtMallocFactors).flatten ++ (e.map stmtMallocFactors).flatten
  | .while_ _ b _ => (b.map stmtMallocFactors).flatten
  | .for_ _ _ _ b _ => (b.map stmtMallocFactors).flatten
  | .doWhile b _ _ => (b.map stmtMallocFactors).flatten
  | .switch_ _ cases _ => (cases.map (fun c => (c.2.1.map stmtMallocFactors).flatten)).flatten
  | .label_ _ body _ => stmtMallocFactors body
  | _ => []

private partial def collectCallsExpr (e : Syntax.Expr) : List (String × List Syntax.Expr) :=
  match e with
  | .call fn args _ => (fn, args) :: (args.map collectCallsExpr).flatten
  | .binOp _ l r _ => collectCallsExpr l ++ collectCallsExpr r
  | .unOp _ o _ => collectCallsExpr o
  | .index a i _ => collectCallsExpr a ++ collectCallsExpr i
  | .member o _ _ => collectCallsExpr o
  | .arrow p _ _ => collectCallsExpr p
  | .assign l r _ => collectCallsExpr l ++ collectCallsExpr r
  | .ternary c t e2 _ => collectCallsExpr c ++ collectCallsExpr t ++ collectCallsExpr e2
  | .cast _ o _ => collectCallsExpr o
  | .comma l r _ => collectCallsExpr l ++ collectCallsExpr r
  | .initList es _ => (es.map collectCallsExpr).flatten
  | .callFnPtr f args _ => collectCallsExpr f ++ (args.map collectCallsExpr).flatten
  | _ => []

private partial def stmtCalls (s : Syntax.Stmt) : List (String × List Syntax.Expr) :=
  match s with
  | .varDecl _ _ init _ => match init with | some e => collectCallsExpr e | none => []
  | .exprStmt e _ => collectCallsExpr e
  | .ret v _ => match v with | some e => collectCallsExpr e | none => []
  | .ifElse c t e _ =>
      collectCallsExpr c ++ (t.map stmtCalls).flatten ++ (e.map stmtCalls).flatten
  | .while_ c b _ => collectCallsExpr c ++ (b.map stmtCalls).flatten
  | .for_ i c st b _ =>
      (match i with | some s2 => stmtCalls s2 | none => []) ++
      (match c with | some e => collectCallsExpr e | none => []) ++
      (match st with | some e => collectCallsExpr e | none => []) ++
      (b.map stmtCalls).flatten
  | .block ss _ => (ss.map stmtCalls).flatten
  | .switch_ scrut cases _ =>
      collectCallsExpr scrut ++ (cases.map (fun c => (c.2.1.map stmtCalls).flatten)).flatten
  | .doWhile b c _ => (b.map stmtCalls).flatten ++ collectCallsExpr c
  | .label_ _ body _ => stmtCalls body
  | _ => []

/-- FEL-58 (partial, scoped): whole-program scan for the "(pointer, width,
    height)" parameter-group idiom. If EVERY call site passing a pointer
    argument known (at that call site) to have byte-capacity `A*B` ALSO
    passes `A` and `B` at two other positions of the SAME call, infer the
    callee's parameter at that position has capacity
    `calleeParam[j] * calleeParam[k]` (using the callee's OWN parameter
    names). Purely syntactic (no FlowState) — this only needs to notice
    the SHAPE `malloc(A*B)` feeding a variable that's later passed
    alongside `A`/`B` positionally; it doesn't need to re-run the
    verifier. -/
private def buildParamCapacityTable (prog : Syntax.Program)
    : List (String × List (Nat × (String × String))) :=
  let allEntries : List (String × Nat × String × String) :=
    (prog.functions.map (fun callerFn =>
      let mallocFactors := (callerFn.body.map stmtMallocFactors).flatten
      let calls := (callerFn.body.map stmtCalls).flatten
      (calls.map (fun (fnName, args) =>
        match prog.functions.find? (·.name == fnName) with
        | none => []
        | some callee =>
            let argsIdx := args.zipIdx
            (argsIdx.map (fun (argExpr, i) =>
              match argExpr with
              | .var argName _ =>
                  match mallocFactors.find? (·.1 == argName) with
                  | none => []
                  | some (_, wExpr, hExpr) =>
                      -- `reprStr` (used elsewhere for opaque error-message
                      -- text) bakes in each expr's source `Loc`, so two
                      -- occurrences of the SAME variable at different
                      -- positions (the malloc call vs. the later argument
                      -- list) never compare equal that way. `canon` is the
                      -- position-independent structural key this needs.
                      let wStr := canon prog wExpr
                      let hStr := canon prog hExpr
                      let findPos (target : String) : Option Nat :=
                        (argsIdx.find? (fun (a, j) => j != i && canon prog a == target)).map (·.2)
                      match findPos wStr, findPos hStr with
                      | some j, some k =>
                          if j == k then [] else
                          let calleeParamsIdx := callee.params.zipIdx
                          match (calleeParamsIdx.find? (·.2 == j)).map (·.1),
                                (calleeParamsIdx.find? (·.2 == k)).map (·.1) with
                          | some pj, some pk => [(fnName, i, pj.name, pk.name)]
                          | _, _ => []
                      | _, _ => []
              | _ => [])).flatten)).flatten)).flatten
  let names := allEntries.foldl (fun acc e => if acc.contains e.1 then acc else acc ++ [e.1]) []
  names.map (fun name =>
    (name, (allEntries.filter (·.1 == name)).map (fun e => (e.2.1, (e.2.2.1, e.2.2.2)))))

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
        let merged := { FlowState.merge thenEnd elseEnd with violations := combinedV, evidence := combinedE }
        match clipPostcondition ctx cond thenBody elseBody with
        | some (sumC, boundC, keyC) =>
            let merged1 := merged.setExprBound sumC boundC
            -- Chain KEY's pre-existing bound (its function-entry marker,
            -- or whatever it had already been narrowed to by an earlier
            -- clip) forward across this reassignment — see the docstring
            -- on `clipPostcondition` above for why this is sound.
            match sCond.getExprBound keyC with
            | some priorBound => merged1.setExprBound keyC priorBound
            | none => merged1
        | none => merged

  | .while_ cond body _ =>
      let (thenFacts, elseFacts) := extractFacts cond
      let oneIter : FlowState → FlowState := fun st =>
        let sCondIter := applyExprChecks ctx cond st
        let bodyStart := inferExprBoundFromCond ctx cond (inferTransitiveBounds cond (applyFacts thenFacts sCondIter))
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
          | some condExpr => inferExprBoundFromCond ctx condExpr (inferTransitiveBounds condExpr bodyStart0)
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

/-- FEL-67: find the LOCATION of the first `goto`/label in a function body,
    not just a bare `Bool` — so the report (and the `degradedBy` evidence
    entry below) can point at the exact line, not just say "somewhere".
    Loop fixpointing (above) covers `while`/`for`/`do-while`; a hand-rolled
    loop built from `goto` is not modelled by the structural analysis at
    all (there is no general CFG here — see FEL-43's follow-up), so such
    functions are marked `degraded` rather than silently claiming full
    precision. -/
private partial def firstGotoLoc (s : Syntax.Stmt) : Option Syntax.Loc :=
  match s with
  | .goto_ _ loc | .label_ _ _ loc => some loc
  | .ifElse _ t e _ =>
      match firstSome t firstGotoLoc with
      | some l => some l
      | none => firstSome e firstGotoLoc
  | .while_ _ b _ => firstSome b firstGotoLoc
  | .for_ i _ _ b _ =>
      match i with
      | some s2 => (match firstGotoLoc s2 with | some l => some l | none => firstSome b firstGotoLoc)
      | none => firstSome b firstGotoLoc
  | .block ss _ => firstSome ss firstGotoLoc
  | .switch_ _ cases _ => firstSome cases (fun (_, body, _) => firstSome body firstGotoLoc)
  | .doWhile b _ _ => firstSome b firstGotoLoc
  | _ => none

/-- Does a case body end with a statement that transfers control OUT of the
    case (so it cannot fall through into the next one)? `.block` unwraps
    to its last statement, matching `branchEndsWithReturn`'s convention. -/
private partial def stmtEndsTerminal (stmts : List Syntax.Stmt) : Bool :=
  match stmts.reverse with
  | [] => false
  | last :: _ =>
      match last with
      | .ret _ _ | .break_ _ | .continue_ _ | .goto_ _ _ => true
      | .block inner _ => stmtEndsTerminal inner
      | _ => false

/-- FEL-49 #3 traded soundness on genuine (break-less) fall-through in a
    `switch` for eliminating a false use-after-free/double-free on the far
    more common break-terminated shape — see the `.switch_` case in
    `analyzeStmt` above. That trade is only honest if a case that DOES
    fall through is flagged as reduced-precision rather than silently
    treated as `verified`. The syntactically last case needs no
    terminator (nothing to fall through TO), so it's excluded. -/
private def firstFallthroughCaseLoc
    (cases : List (Option Int × List Syntax.Stmt × Syntax.Loc)) : Option Syntax.Loc :=
  firstSome cases.dropLast (fun (_, body, loc) =>
    if stmtEndsTerminal body then none else some loc)

/-- Find the location of the first `switch` anywhere in a function body
    (including nested inside other statements) that has a fall-through
    case, per `firstFallthroughCaseLoc` above. -/
private partial def firstSwitchFallthroughLoc (s : Syntax.Stmt) : Option Syntax.Loc :=
  match s with
  | .switch_ _ cases _ =>
      match firstFallthroughCaseLoc cases with
      | some l => some l
      | none => firstSome cases (fun (_, body, _) => firstSome body firstSwitchFallthroughLoc)
  | .ifElse _ t e _ =>
      match firstSome t firstSwitchFallthroughLoc with
      | some l => some l
      | none => firstSome e firstSwitchFallthroughLoc
  | .while_ _ b _ => firstSome b firstSwitchFallthroughLoc
  | .for_ i _ _ b _ =>
      match i with
      | some s2 => (match firstSwitchFallthroughLoc s2 with
          | some l => some l
          | none => firstSome b firstSwitchFallthroughLoc)
      | none => firstSome b firstSwitchFallthroughLoc
  | .block ss _ => firstSome ss firstSwitchFallthroughLoc
  | .doWhile b _ _ => firstSome b firstSwitchFallthroughLoc
  | .label_ _ body _ => firstSwitchFallthroughLoc body
  | _ => none

/-- Does this expression contain a call to `setjmp`/`sigsetjmp` anywhere,
    however deeply nested (`if (setjmp(jb))`, `int r = setjmp(jb);`, a
    bare `setjmp(jb);` statement — all real, common usages)? `setjmp`'s
    control-flow semantics (one call site, potentially many returns, one
    for the direct call and one per matching `longjmp`) are not a shape
    the structural flow analysis models at all — a function using it was
    designed to be reported `exempt` (`VerifyStatus.exempt`'s own doc
    comment: "uses EXEMPT features (varargs, setjmp); verification
    skipped"), but until this fix NOTHING in the verifier ever actually
    produced `.exempt` for any function, for any reason — every function
    using `setjmp` was silently analysed as if it were ordinary control
    flow and reported fully `verified` regardless, directly contradicting
    FEL-65's epic DoD bullet 7 ("never call a skipped function
    verified"). -/
private partial def exprCallsSetjmp (e : Syntax.Expr) : Bool :=
  match e with
  | .call fn args _ => fn == "setjmp" || fn == "sigsetjmp" || args.any exprCallsSetjmp
  | .callFnPtr fn args _ => exprCallsSetjmp fn || args.any exprCallsSetjmp
  | .binOp _ l r _ => exprCallsSetjmp l || exprCallsSetjmp r
  | .unOp _ o _ => exprCallsSetjmp o
  | .index a i _ => exprCallsSetjmp a || exprCallsSetjmp i
  | .member o _ _ => exprCallsSetjmp o
  | .arrow p _ _ => exprCallsSetjmp p
  | .assign l r _ => exprCallsSetjmp l || exprCallsSetjmp r
  | .ternary c t e2 _ => exprCallsSetjmp c || exprCallsSetjmp t || exprCallsSetjmp e2
  | .cast _ o _ => exprCallsSetjmp o
  | .comma l r _ => exprCallsSetjmp l || exprCallsSetjmp r
  | .initList es _ => es.any exprCallsSetjmp
  | .sizeOfExpr o _ => exprCallsSetjmp o
  | .intLit _ _ | .charLit _ _ | .sizeOf _ _ | .strLit _ _ | .nullLit _ | .floatLit _ _ | .var _ _ => false

private partial def stmtCallsSetjmp (s : Syntax.Stmt) : Bool :=
  match s with
  | .varDecl _ _ init _ => match init with | some e => exprCallsSetjmp e | none => false
  | .exprStmt e _ => exprCallsSetjmp e
  | .ret v _ => match v with | some e => exprCallsSetjmp e | none => false
  | .ifElse c t e _ => exprCallsSetjmp c || t.any stmtCallsSetjmp || e.any stmtCallsSetjmp
  | .while_ c b _ => exprCallsSetjmp c || b.any stmtCallsSetjmp
  | .for_ i c st b _ =>
      (match i with | some s2 => stmtCallsSetjmp s2 | none => false) ||
      (match c with | some e => exprCallsSetjmp e | none => false) ||
      (match st with | some e => exprCallsSetjmp e | none => false) ||
      b.any stmtCallsSetjmp
  | .block ss _ => ss.any stmtCallsSetjmp
  | .switch_ scrut cases _ =>
      exprCallsSetjmp scrut || cases.any (fun (_, body, _) => body.any stmtCallsSetjmp)
  | .doWhile b c _ => b.any stmtCallsSetjmp || exprCallsSetjmp c
  | .label_ _ body _ => stmtCallsSetjmp body
  | .break_ _ | .continue_ _ | .goto_ _ _ | .emptyStmt _ => false

/-- Verify one function body. FEL-67: a function is `degraded` (not
    `verified`) when it uses `goto`/labels or has a switch case that can
    fall through — both are real gaps in the structural analysis (FEL-43,
    FEL-49 #3), and previously this status was computed but never
    surfaced: `--verify-report` printed `verified (0 violations)` for such
    a function regardless, and `ccc` exited 0. The `degradedBy` evidence
    entries recorded here are what let the report name the actual
    construct and line, not just say "degraded" with no reason.

    FEL-65 epic DoD bullet 7 follow-up: a function calling `setjmp` is
    `exempt` (verification skipped, not merely degraded) — worse than
    `degraded`, not milder, since the structural analysis's single-return
    assumption is fundamentally wrong for it, not just imprecise.
    `exempt` wins over `degraded` when a function has both (matches
    `ProgramVerifyResult.worstStatus`'s existing ordering). Variadic
    FUNCTION DEFINITIONS (as opposed to variadic external declarations,
    which already parse fine) are a separate, larger, pre-existing gap —
    `int f(int n, ...) { ... }` isn't correctly parsed at all today (its
    `...` parameter is dropped, corrupting arity checking), so there is
    no function-level `isVariadic` flag yet to exempt on; not attempted
    here. -/
def verifyFunction (ctx : VerifyCtx) (f : Syntax.FunDef) : Syntax.FunVerifyResult :=
  let paramIdx := f.params.zipIdx.map (fun (p, i) => (p.name, i))
  let ctx := { ctx with currentFun := f.name, currentParamIndex := paramIdx }
  let initState := initFlowStateFromParams f.params
  let finalState := analyzeStmts ctx f.body initState
  let gotoLoc? := firstSome f.body firstGotoLoc
  let fallthroughLoc? := firstSome f.body firstSwitchFallthroughLoc
  let degradeEvidence : List Syntax.SafetyEvidence :=
    (match gotoLoc? with
      | some l => [Syntax.SafetyEvidence.degradedBy "goto"
          "function uses goto/labels; there is no general control-flow graph here, so hand-rolled control flow is not modelled" l]
      | none => []) ++
    (match fallthroughLoc? with
      | some l => [Syntax.SafetyEvidence.degradedBy "switch-fallthrough"
          "a switch case does not end in break/return/continue/goto; fall-through between cases is not modelled" l]
      | none => [])
  let usesSetjmp : Bool := f.body.any stmtCallsSetjmp
  let status : Syntax.VerifyStatus :=
    if usesSetjmp then .exempt
    else if gotoLoc?.isSome || fallthroughLoc?.isSome then .degraded
    else .verified
  let exemptEvidence : List Syntax.SafetyEvidence :=
    if usesSetjmp then
      [Syntax.SafetyEvidence.exemptedBy "setjmp"
        "function calls setjmp; its multiple-return control flow is not modelled at all" f.loc]
    else []
  { funName := f.name
    status := status
    violations := finalState.violations
    evidence := finalState.evidence ++ degradeEvidence ++ exemptEvidence }

/-- Verify all functions and produce a report. -/
def verifyProgramReport (prog : Syntax.Program) : Syntax.ProgramVerifyResult :=
  -- Phase 0: Symbol validation (undefined functions, arity mismatches)
  let symbolViolations := SymbolCheck.checkProgram prog
  -- Phase 0.5: coarse whole-program summaries (FEL-48, FEL-58 partial)
  let freesTable := buildFreesParamTable prog
  let capacityTable := buildParamCapacityTable prog
  -- Phase 1: Per-function flow-sensitive analysis
  let baseCtx : VerifyCtx :=
    { structs := prog.structs, currentFun := "", funcFreesParam := freesTable
      program := prog, paramCapacity := capacityTable }
  let results : List Syntax.FunVerifyResult :=
    prog.functions.map (fun f => verifyFunction baseCtx f)
  -- Prepend symbol violations as a synthetic result
  let symbolResult : Syntax.FunVerifyResult :=
    { funName := "program"
      status := .verified
      violations := symbolViolations
      evidence := [] }
  { results := if symbolViolations.isEmpty then results
               else symbolResult :: results }

end CCC.Verify
