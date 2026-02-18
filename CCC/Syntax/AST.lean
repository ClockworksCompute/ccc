/-
  CCC/Syntax/AST.lean — Deeply embedded C subset AST

  This is THE shared type. Parser produces it, verifier reads it, emitter reads it.
  DE-1: pure data only, no string emission in this file.
-/

namespace CCC.Syntax

/-- Source location — line and column. Attached to every Expr and Stmt node. -/
structure Loc where
  line : Nat
  col  : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- C types in our subset. -/
inductive CType where
  | void
  | int
  | char
  | long
  | bool
  | unsigned (inner : CType)  -- unsigned int, unsigned char, unsigned long
  | pointer (elem : CType)
  | array (elem : CType) (size : Nat)
  | struct_ (name : String)
  | sizeT                     -- size_t, resolves to Nat for bounds
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Binary operators. -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | mod
  -- Comparison
  | eq | ne | lt | gt | le | ge
  -- Logical
  | and_ | or_
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Unary operators. -/
inductive UnOp where
  | neg     -- -x
  | not_    -- !x
  | deref   -- *p
  | addrOf  -- &x
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Expressions. Every variant carries a Loc. -/
inductive Expr where
  | intLit  (val : Int) (loc : Loc)
  | charLit (val : Char) (loc : Loc)
  | var     (name : String) (loc : Loc)
  | binOp   (op : BinOp) (lhs rhs : Expr) (loc : Loc)
  | unOp    (op : UnOp) (operand : Expr) (loc : Loc)
  | index   (arr : Expr) (idx : Expr) (loc : Loc)
  | member  (obj : Expr) (field : String) (loc : Loc)
  | arrow   (ptr : Expr) (field : String) (loc : Loc)
  | call    (fn : String) (args : List Expr) (loc : Loc)
  | sizeOf  (ty : CType) (loc : Loc)
  | assign  (lhs rhs : Expr) (loc : Loc)
  deriving Repr, Inhabited

/-- Statements. Every variant carries a Loc. -/
inductive Stmt where
  | varDecl  (name : String) (ty : CType) (init : Option Expr) (loc : Loc)
  | exprStmt (expr : Expr) (loc : Loc)
  | ret      (val : Option Expr) (loc : Loc)
  | ifElse   (cond : Expr) (thenBody : List Stmt) (elseBody : List Stmt) (loc : Loc)
  | while_   (cond : Expr) (body : List Stmt) (loc : Loc)
  | for_     (init : Option Stmt) (cond : Option Expr) (step : Option Expr)
             (body : List Stmt) (loc : Loc)
  | block    (stmts : List Stmt) (loc : Loc)
  deriving Repr, Inhabited

/-- Function parameter. -/
structure Param where
  name : String
  ty   : CType
  deriving Repr, Inhabited, BEq

/-- Function definition. -/
structure FunDef where
  name   : String
  ret    : CType
  params : List Param
  body   : List Stmt
  loc    : Loc
  deriving Repr, Inhabited

/-- Struct definition. Fields are (name, type) pairs. -/
structure StructDef where
  name   : String
  fields : List (String × CType)
  loc    : Loc
  deriving Repr, Inhabited

/-- Top-level program: struct definitions + function definitions. -/
structure Program where
  structs   : List StructDef
  functions : List FunDef
  deriving Repr, Inhabited

-- Convenience accessors
namespace Expr

def loc : Expr → Loc
  | .intLit _ l | .charLit _ l | .var _ l => l
  | .binOp _ _ _ l | .unOp _ _ l => l
  | .index _ _ l | .member _ _ l | .arrow _ _ l => l
  | .call _ _ l | .sizeOf _ l | .assign _ _ l => l

end Expr

namespace Stmt

def loc : Stmt → Loc
  | .varDecl _ _ _ l | .exprStmt _ l | .ret _ l => l
  | .ifElse _ _ _ l | .while_ _ _ l | .for_ _ _ _ _ l | .block _ l => l

end Stmt

end CCC.Syntax
