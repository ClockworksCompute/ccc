/-
  CCC/Verify/SymbolCheck.lean — Symbol existence & arity validation

  Pre-pass before flow-sensitive analysis. Walks every Expr.call and checks:
  1. The function name exists in the program or builtin list
  2. The argument count matches the declared parameter count

  Violations are reported as SafetyViolation so they flow through the
  existing verifyProgram → rejection path.
-/
import CCC.Verify.FlowState

namespace CCC.Verify.SymbolCheck

/-- Built-in functions and their arities. -/
private def builtins : List (String × Nat) :=
  [("malloc", 1), ("free", 1), ("memcpy", 3)]

/-- Build symbol table: function name → arity. -/
private def buildSymbolTable (prog : Syntax.Program) : List (String × Nat) :=
  let userFns := prog.functions.map (fun f => (f.name, f.params.length))
  builtins ++ userFns

private def lookupSymbol (table : List (String × Nat)) (name : String) : Option Nat :=
  (table.find? (·.1 == name)).map (·.2)

private def mkViolation (loc : Syntax.Loc) (expr : Syntax.Expr) (msg : String)
    (fn : String) (suggestion : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds  -- reuse existing property; semantically "invalid program"
    loc := loc
    expr := reprStr expr
    message := msg
    context := [s!"function: {fn}"]
    suggestion := some suggestion }

/-- Collect all violations from a single expression tree. -/
partial def checkExpr (table : List (String × Nat)) (currentFun : String)
    (expr : Syntax.Expr) : List Syntax.SafetyViolation :=
  match expr with
  | .call fn args loc =>
      let argViolations := (args.map (checkExpr table currentFun)).flatten
      let callViolations : List Syntax.SafetyViolation :=
        match lookupSymbol table fn with
        | none =>
            [mkViolation loc expr
              s!"Call to undefined function '{fn}'"
              currentFun
              s!"Define function '{fn}' or check spelling"]
        | some expectedArity =>
            if args.length != expectedArity then
              [mkViolation loc expr
                s!"Function '{fn}' expects {expectedArity} argument(s), got {args.length}"
                currentFun
                s!"Pass exactly {expectedArity} argument(s) to '{fn}'"]
            else
              []
      argViolations ++ callViolations
  | .binOp _ lhs rhs _ =>
      checkExpr table currentFun lhs ++ checkExpr table currentFun rhs
  | .unOp _ operand _ => checkExpr table currentFun operand
  | .index arr idx _ =>
      checkExpr table currentFun arr ++ checkExpr table currentFun idx
  | .member obj _ _ => checkExpr table currentFun obj
  | .arrow ptr _ _ => checkExpr table currentFun ptr
  | .assign lhs rhs _ =>
      checkExpr table currentFun lhs ++ checkExpr table currentFun rhs
  | .intLit _ _ | .charLit _ _ | .var _ _ | .sizeOf _ _ => []

/-- Collect all violations from a statement tree. -/
partial def checkStmt (table : List (String × Nat)) (currentFun : String)
    (stmt : Syntax.Stmt) : List Syntax.SafetyViolation :=
  match stmt with
  | .varDecl _ _ init _ =>
      match init with
      | some expr => checkExpr table currentFun expr
      | none => []
  | .exprStmt expr _ => checkExpr table currentFun expr
  | .ret val _ =>
      match val with
      | some expr => checkExpr table currentFun expr
      | none => []
  | .ifElse cond thenBody elseBody _ =>
      checkExpr table currentFun cond ++
      (thenBody.map (checkStmt table currentFun)).flatten ++
      (elseBody.map (checkStmt table currentFun)).flatten
  | .while_ cond body _ =>
      checkExpr table currentFun cond ++
      (body.map (checkStmt table currentFun)).flatten
  | .for_ init cond step body _ =>
      let initV := match init with
        | some s => checkStmt table currentFun s
        | none => []
      let condV := match cond with
        | some e => checkExpr table currentFun e
        | none => []
      let stepV := match step with
        | some e => checkExpr table currentFun e
        | none => []
      let bodyV := (body.map (checkStmt table currentFun)).flatten
      initV ++ condV ++ stepV ++ bodyV
  | .block stmts _ => (stmts.map (checkStmt table currentFun)).flatten

/-- Run symbol validation across the entire program.
    Returns violations for undefined functions and arity mismatches. -/
def checkProgram (prog : Syntax.Program) : List Syntax.SafetyViolation :=
  let table := buildSymbolTable prog
  (prog.functions.map (fun f =>
    (f.body.map (checkStmt table f.name)).flatten
  )).flatten

end CCC.Verify.SymbolCheck
