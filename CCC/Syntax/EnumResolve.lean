/-
  CCC/Syntax/EnumResolve.lean — resolve enum constant names to their
  integer values.

  FEL-68 (emitter completeness): `enum Color { RED, GREEN, BLUE };` was
  parsed and its values correctly computed into `Program.enums`, but
  nothing ever consulted that table when an enum constant NAME was used
  as an expression. `RED` parses as a plain `Expr.var "RED"` — the same
  node an ordinary variable reference produces — and since no variable
  named `RED` exists anywhere, this failed emission outright with
  "unknown variable 'RED'". Enums are used constantly in real C headers
  (error codes, flags, state machines), so this was an immediate, hard
  compile failure for essentially any real library that declares one and
  uses a member by name anywhere — not a silent-wrong-value bug like
  several of the other FEL-68 gaps, but a blocking one.

  This module is a single, pure, post-parse AST rewrite: compute every
  enum constant's resolved value (per C's "0, then previous+1 unless
  overridden" rule) across the whole program, then walk every function
  body and global initializer replacing `Expr.var name` with
  `Expr.intLit value` wherever `name` matches. Run automatically at the
  end of `Parse.parseProgram`, so every caller (the verifier, both
  emitters, `--verify-report`, and every test helper that calls
  `parseProgram` directly) sees an already-resolved program uniformly —
  no separate pass to remember to invoke.

  `switch` case labels (`case RED:`) and array sizes (`char buf[BUF];`)
  need a resolved value DURING PARSING, before this module's own
  post-parse `resolveProgram` walk ever runs — so `Parse.parseEnumDef`
  also calls `resolveEnumValues` directly as each `enum` is declared,
  registering the results into `ParseState.enumValues`, which
  `Parse.parseArraySuffix` and `Parse.parseSwitchCases` both consult.

  Known limitation, narrow and explicitly out of scope for this slice
  (see FEL-68 in the project tracker for follow-ups):
  - No lexical scope tracking: a local variable or parameter that happens
    to share a name with an enum constant is (incorrectly, but rarely in
    real code) ALSO replaced by the constant's value. The same "practical
    C subset" tradeoff the rest of this compiler already makes elsewhere.
-/

import CCC.Syntax.AST

namespace CCC.Syntax.EnumResolve

/-- Resolve one enum's member values in declaration order: the first
    member defaults to 0, each subsequent member defaults to
    (previous resolved value + 1) unless it carries an explicit
    `= value`, in which case the running default resumes counting up
    from THAT value — exactly C's rule. Exported: `Parse.parseEnumDef`
    calls this directly too, to register each enum's resolved values
    into `ParseState.enumValues` AS IT PARSES (rather than only after
    the whole program is parsed, which is what this module's own
    post-parse `resolveProgram` rewrite does) — needed for the places
    the parser demands a compile-time-constant integer immediately,
    before this module's own whole-program pass ever runs: array sizes
    (`char buf[BUF_SIZE];`) and `switch` case labels (`case RED:`). Both
    call sites must agree on the exact same resolved values, which is
    exactly why this one function is shared rather than reimplemented
    in the parser. -/
def resolveEnumValues (values : List (String × Option Int)) : List (String × Int) :=
  let (resolved, _) := values.foldl
    (fun (acc, nextDefault) (name, explicit?) =>
      let v := explicit?.getD nextDefault
      (acc ++ [(name, v)], v + 1))
    ([], (0 : Int))
  resolved

/-- Every enum constant → its resolved value, across every `enum` in the
    program. Flat, not per-enum-type: C enum constants share the
    enclosing scope's namespace (`enum Color { RED };` puts `RED`
    directly in scope, not as `Color.RED`). -/
def buildEnumTable (prog : Program) : List (String × Int) :=
  (prog.enums.map (fun e => resolveEnumValues e.values)).flatten

mutual

private partial def resolveExpr (table : List (String × Int)) (e : Expr) : Expr :=
  match e with
  | .var name loc =>
      match table.find? (·.1 == name) with
      | some (_, v) => .intLit v loc
      | none => e
  | .binOp op l r loc => .binOp op (resolveExpr table l) (resolveExpr table r) loc
  | .unOp op o loc => .unOp op (resolveExpr table o) loc
  | .index a i loc => .index (resolveExpr table a) (resolveExpr table i) loc
  | .member o f loc => .member (resolveExpr table o) f loc
  | .arrow p f loc => .arrow (resolveExpr table p) f loc
  | .call fn args loc => .call fn (args.map (resolveExpr table)) loc
  | .assign l r loc => .assign (resolveExpr table l) (resolveExpr table r) loc
  | .ternary c t e2 loc =>
      .ternary (resolveExpr table c) (resolveExpr table t) (resolveExpr table e2) loc
  | .cast ty o loc => .cast ty (resolveExpr table o) loc
  | .comma l r loc => .comma (resolveExpr table l) (resolveExpr table r) loc
  | .initList es loc => .initList (es.map (resolveExpr table)) loc
  | .callFnPtr fn args loc => .callFnPtr (resolveExpr table fn) (args.map (resolveExpr table)) loc
  | .sizeOfExpr o loc => .sizeOfExpr (resolveExpr table o) loc
  | .intLit _ _ | .charLit _ _ | .sizeOf _ _ | .strLit _ _ | .nullLit _ | .floatLit _ _ => e

private partial def resolveStmt (table : List (String × Int)) (s : Stmt) : Stmt :=
  match s with
  | .varDecl name ty init loc => .varDecl name ty (init.map (resolveExpr table)) loc
  | .exprStmt e loc => .exprStmt (resolveExpr table e) loc
  | .ret v loc => .ret (v.map (resolveExpr table)) loc
  | .ifElse c t e loc =>
      .ifElse (resolveExpr table c) (t.map (resolveStmt table)) (e.map (resolveStmt table)) loc
  | .while_ c b loc => .while_ (resolveExpr table c) (b.map (resolveStmt table)) loc
  | .for_ i c st b loc =>
      .for_ (i.map (resolveStmt table)) (c.map (resolveExpr table)) (st.map (resolveExpr table))
        (b.map (resolveStmt table)) loc
  | .block ss loc => .block (ss.map (resolveStmt table)) loc
  | .switch_ scrut cases loc =>
      -- Note: only the scrutinee and case BODIES go through the table
      -- here; the case LABELS themselves are already resolved to plain
      -- ints during parsing (see `Parse.parseSwitchCases`).
      .switch_ (resolveExpr table scrut)
        (cases.map (fun (v, body, l) => (v, body.map (resolveStmt table), l))) loc
  | .doWhile b c loc => .doWhile (b.map (resolveStmt table)) (resolveExpr table c) loc
  | .label_ name body loc => .label_ name (resolveStmt table body) loc
  | .break_ _ | .continue_ _ | .goto_ _ _ | .emptyStmt _ => s

end

private def resolveFunDef (table : List (String × Int)) (f : FunDef) : FunDef :=
  { f with body := f.body.map (resolveStmt table) }

private def resolveGlobalDecl (table : List (String × Int)) (g : GlobalDecl) : GlobalDecl :=
  { g with init := g.init.map (resolveExpr table) }

/-- Rewrite every use of a known enum constant NAME as an expression
    (function bodies and global initializers) into its resolved integer
    literal. A no-op program-wide walk is skipped entirely when there are
    no enums at all, which is the common case. -/
def resolveProgram (prog : Program) : Program :=
  let table := buildEnumTable prog
  if table.isEmpty then prog
  else
    { prog with
        functions := prog.functions.map (resolveFunDef table)
        globals := prog.globals.map (resolveGlobalDecl table) }

end CCC.Syntax.EnumResolve
