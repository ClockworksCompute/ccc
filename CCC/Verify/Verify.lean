import CCC.Verify.BoundsCheck
import CCC.Verify.PointerSafety
import CCC.Verify.NullCheck
import CCC.Verify.BranchAnalysis
import CCC.Verify.SymbolCheck

namespace CCC.Verify

private def ptrStateForParam (ty : Syntax.CType) : Option Syntax.PtrState :=
  match ty with
  | .pointer _ => some (.checkedLive none)
  | .array _ n => some (.stackLocal (some n))
  | _ => none

/-- Seed flow state from function parameters. -/
def initFlowStateFromParams (params : List Syntax.Param) : FlowState :=
  params.foldl
    (fun st p =>
      let st1 := st.setType p.name p.ty
      match ptrStateForParam p.ty with
      | some ps => st1.setPtr p.name ps
      | none => st1)
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
    bound in the flow state, propagate that bound to `lhs`.
    This handles patterns like `while (i < g->count)` where
    `g->count` was previously bounded by an early-return check. -/
private def inferTransitiveBounds (cond : Syntax.Expr) (state : FlowState) : FlowState :=
  match cond with
  | .binOp .lt lhs rhs _ =>
      -- lhs < rhs: rhs has exclusive bound B means rhs < B, i.e. rhs ≤ B-1
      -- so lhs < rhs ≤ B-1, meaning lhs ≤ B-2, i.e. lhs exclusive bound = B-1
      match boundKeyOf? lhs, boundKeyOf? rhs with
      | some lhsKey, some rhsKey =>
          match state.getBound rhsKey with
          | some rhsBound =>
              if rhsBound > 0 then state.setBound lhsKey (rhsBound - 1)
              else state.setBound lhsKey 0
          | none => state
      | _, _ => state
  | .binOp .le lhs rhs _ =>
      -- lhs <= rhs: rhs has exclusive bound B means rhs < B
      -- so lhs ≤ rhs < B, meaning lhs exclusive bound = B
      match boundKeyOf? lhs, boundKeyOf? rhs with
      | some lhsKey, some rhsKey =>
          match state.getBound rhsKey with
          | some rhsBound => state.setBound lhsKey rhsBound
          | none => state
      | _, _ => state
  | .binOp .and_ lhs rhs _ =>
      let s1 := inferTransitiveBounds lhs state
      inferTransitiveBounds rhs s1
  | _ => state

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
          BoundsCheck.checkExpr ctx expr s2
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
      let thenReturns := branchEndsWithReturn thenBody
      let elseReturns := branchEndsWithReturn elseBody
      if thenReturns && !elseReturns then
        elseEnd
      else if elseReturns && !thenReturns then
        thenEnd
      else
        FlowState.merge thenEnd elseEnd

  | .while_ cond body _ =>
      let sCond := applyExprChecks ctx cond state
      let (thenFacts, elseFacts) := extractFacts cond
      let bodyStart := applyFacts thenFacts sCond
      let bodyStart := inferTransitiveBounds cond bodyStart
      let bodyEnd := analyzeStmts ctx body bodyStart
      let exitState := applyFacts elseFacts sCond
      FlowState.merge exitState bodyEnd

  | .for_ init cond step body _ =>
      let sInit :=
        match init with
        | some initStmt => analyzeStmt ctx initStmt state
        | none => state
      let sCond :=
        match cond with
        | some condExpr => applyExprChecks ctx condExpr sInit
        | none => sInit
      let thenFactsElseFacts : (List BranchFact) × (List BranchFact) :=
        match cond with
        | some condExpr => extractFacts condExpr
        | none => ([], [])
      let thenFacts := thenFactsElseFacts.1
      let elseFacts := thenFactsElseFacts.2
      let bodyStart := applyFacts thenFacts sCond
      let bodyStart := match cond with
        | some condExpr => inferTransitiveBounds condExpr bodyStart
        | none => bodyStart
      let bodyEnd0 := analyzeStmts ctx body bodyStart
      let bodyEnd :=
        match step with
        | some stepExpr => applyExprChecks ctx stepExpr bodyEnd0
        | none => bodyEnd0
      let exitState := applyFacts elseFacts sCond
      FlowState.merge exitState bodyEnd

  | .block stmts _ => analyzeStmts ctx stmts state

  -- Phase 2 Stmt
  | .switch_ scrut cases _ =>
      let sCond := applyExprChecks ctx scrut state
      cases.foldl (fun st (_, body, _) =>
        analyzeStmts ctx body st) sCond

  | .doWhile body cond _ =>
      let sBody := analyzeStmts ctx body state
      let sCond := applyExprChecks ctx cond sBody
      FlowState.merge state sCond

  | .break_ _ | .continue_ _ | .emptyStmt _ => state

  | .goto_ _ _ => state

  | .label_ _ body _ => analyzeStmt ctx body state

end

/-- Verify one function body. -/
def verifyFunction (ctx : VerifyCtx) (f : Syntax.FunDef) : Syntax.FunVerifyResult :=
  let initState := initFlowStateFromParams f.params
  let finalState := analyzeStmts ctx f.body initState
  { funName := f.name
    status := .verified
    violations := finalState.violations
    evidence := finalState.evidence }

/-- Verify all functions and produce a report. -/
def verifyProgramReport (prog : Syntax.Program) : Syntax.ProgramVerifyResult :=
  -- Phase 0: Symbol validation (undefined functions, arity mismatches)
  let symbolViolations := SymbolCheck.checkProgram prog
  -- Phase 1: Per-function flow-sensitive analysis
  let baseCtx : VerifyCtx := { structs := prog.structs, currentFun := "" }
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
