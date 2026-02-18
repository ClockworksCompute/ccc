/-
  CCC/Verify/SymbolCheck.lean — Symbol existence & arity validation

  Pre-pass before flow-sensitive analysis. Walks every Expr.call and checks:
  1. The function name exists in the program (defined or declared via prototype)
  2. The argument count matches the declared parameter count
     (variadic functions accept >= declared params)

  Undefined functions are NOT reported as violations — the linker catches those.
  The verifier's job is memory safety (P1-P5), not symbol resolution.
-/
import CCC.Verify.FlowState

namespace CCC.Verify.SymbolCheck

/-- Symbol table entry: arity and whether the function is variadic. -/
structure SymEntry where
  arity      : Nat
  isVariadic : Bool
  deriving Repr, Inhabited

/-- Build symbol table from function definitions and extern declarations.
    Definitions take priority over extern declarations (forward decl pattern). -/
private def buildSymbolTable (prog : Syntax.Program) : List (String × SymEntry) :=
  -- User-defined functions (exact arity, not variadic)
  let userFns := prog.functions.map (fun f =>
    (f.name, { arity := f.params.length, isVariadic := false : SymEntry }))
  -- Extern declarations (from prototypes / #include headers)
  let externFns := prog.externs.map (fun e =>
    (e.name, { arity := e.params.length, isVariadic := e.isVariadic : SymEntry }))
  -- Definitions first so lookup prefers them over extern decls
  userFns ++ externFns

private def lookupSymbol (table : List (String × SymEntry)) (name : String) : Option SymEntry :=
  (table.find? (·.1 == name)).map (·.2)

private def mkViolation (loc : Syntax.Loc) (expr : Syntax.Expr) (msg : String)
    (fn : String) (suggestion : String) : Syntax.SafetyViolation :=
  { property := .bufferBounds
    loc := loc
    expr := reprStr expr
    message := msg
    context := [s!"function: {fn}"]
    suggestion := some suggestion }

/-- Collect all violations from a single expression tree. -/
partial def checkExpr (table : List (String × SymEntry)) (currentFun : String)
    (expr : Syntax.Expr) : List Syntax.SafetyViolation :=
  match expr with
  | .call fn args loc =>
      let argViolations := (args.map (checkExpr table currentFun)).flatten
      let callViolations : List Syntax.SafetyViolation :=
        match lookupSymbol table fn with
        | none =>
            -- Unknown function: not a memory safety violation.
            -- The linker will catch genuinely missing symbols.
            []
        | some entry =>
            if entry.isVariadic then
              -- Variadic: must have at least the declared params
              if args.length < entry.arity then
                [mkViolation loc expr
                  s!"Variadic function '{fn}' expects at least {entry.arity} argument(s), got {args.length}"
                  currentFun
                  s!"Pass at least {entry.arity} argument(s) to '{fn}'"]
              else
                []
            else
              if args.length != entry.arity then
                [mkViolation loc expr
                  s!"Function '{fn}' expects {entry.arity} argument(s), got {args.length}"
                  currentFun
                  s!"Pass exactly {entry.arity} argument(s) to '{fn}'"]
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
  -- Phase 2 Expr
  | .strLit _ _ | .nullLit _ | .floatLit _ _ => []
  | .ternary c t e _ =>
      checkExpr table currentFun c ++ checkExpr table currentFun t ++ checkExpr table currentFun e
  | .cast _ operand _ => checkExpr table currentFun operand
  | .comma l r _ =>
      checkExpr table currentFun l ++ checkExpr table currentFun r
  | .initList elems _ => (elems.map (checkExpr table currentFun)).flatten
  | .callFnPtr fn args _ =>
      checkExpr table currentFun fn ++ (args.map (checkExpr table currentFun)).flatten

/-- Collect all violations from a statement tree. -/
partial def checkStmt (table : List (String × SymEntry)) (currentFun : String)
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
  -- Phase 2 Stmt
  | .switch_ scrut cases _ =>
      checkExpr table currentFun scrut ++
      (cases.map (fun (_, body, _) => (body.map (checkStmt table currentFun)).flatten)).flatten
  | .doWhile body cond _ =>
      (body.map (checkStmt table currentFun)).flatten ++
      checkExpr table currentFun cond
  | .break_ _ | .continue_ _ | .emptyStmt _ => []
  | .goto_ _ _ => []
  | .label_ _ body _ => checkStmt table currentFun body

/-- Run symbol validation across the entire program.
    Returns violations for arity mismatches only.
    Undefined functions are silently accepted (linker catches them). -/
def checkProgram (prog : Syntax.Program) : List Syntax.SafetyViolation :=
  let table := buildSymbolTable prog
  (prog.functions.map (fun f =>
    (f.body.map (checkStmt table f.name)).flatten
  )).flatten

end CCC.Verify.SymbolCheck
