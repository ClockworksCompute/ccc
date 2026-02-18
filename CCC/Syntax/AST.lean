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

/-- C types — full C99 coverage (minus _Complex, _Atomic, VLAs). -/
inductive CType where
  -- Phase 1 types (existing)
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
  -- Phase 2 types (new)
  | float_                     -- float
  | double_                    -- double
  | short                      -- short
  | longLong                   -- long long
  | signed (inner : CType)    -- signed int, signed char
  | enum_ (name : String)     -- enum type reference
  | union_ (name : String)    -- union type reference
  | funcPtr (ret : CType) (params : List CType)  -- function pointer type
  | typedef_ (name : String)  -- typedef reference (resolved later)
  | const_ (inner : CType)    -- const qualifier
  | volatile_ (inner : CType) -- volatile qualifier
  | restrict_ (inner : CType) -- restrict qualifier
  deriving Repr, Inhabited

partial def CType.beq : CType → CType → Bool
  | .void, .void => true
  | .int, .int => true
  | .char, .char => true
  | .long, .long => true
  | .bool, .bool => true
  | .sizeT, .sizeT => true
  | .float_, .float_ => true
  | .double_, .double_ => true
  | .short, .short => true
  | .longLong, .longLong => true
  | .unsigned a, .unsigned b => CType.beq a b
  | .signed a, .signed b => CType.beq a b
  | .pointer a, .pointer b => CType.beq a b
  | .array a n, .array b m => CType.beq a b && n == m
  | .struct_ a, .struct_ b => a == b
  | .enum_ a, .enum_ b => a == b
  | .union_ a, .union_ b => a == b
  | .funcPtr r1 p1, .funcPtr r2 p2 =>
      CType.beq r1 r2 && p1.length == p2.length &&
      (List.zip p1 p2).all (fun (a, b) => CType.beq a b)
  | .typedef_ a, .typedef_ b => a == b
  | .const_ a, .const_ b => CType.beq a b
  | .volatile_ a, .volatile_ b => CType.beq a b
  | .restrict_ a, .restrict_ b => CType.beq a b
  | _, _ => false

instance : BEq CType where beq := CType.beq

/-- Binary operators. -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | mod
  -- Comparison
  | eq | ne | lt | gt | le | ge
  -- Logical
  | and_ | or_
  -- Bitwise (Phase 2)
  | bitAnd | bitOr | bitXor | shl | shr
  -- Compound assignment (Phase 2)
  | addAssign | subAssign | mulAssign | divAssign | modAssign
  | andAssign | orAssign | xorAssign | shlAssign | shrAssign
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Unary operators. -/
inductive UnOp where
  | neg     -- -x
  | not_    -- !x
  | deref   -- *p
  | addrOf  -- &x
  -- Phase 2
  | bitNot    -- ~x (bitwise complement)
  | preInc    -- ++x
  | preDec    -- --x
  | postInc   -- x++
  | postDec   -- x--
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Expressions. Every variant carries a Loc. -/
inductive Expr where
  -- Phase 1 (existing)
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
  -- Phase 2 (new)
  | strLit    (val : String) (loc : Loc)
  | ternary   (cond : Expr) (then_ : Expr) (else_ : Expr) (loc : Loc)
  | cast      (ty : CType) (operand : Expr) (loc : Loc)
  | comma     (left : Expr) (right : Expr) (loc : Loc)
  | initList  (elems : List Expr) (loc : Loc)
  | callFnPtr (fnExpr : Expr) (args : List Expr) (loc : Loc)
  | nullLit   (loc : Loc)
  | floatLit  (val : Float) (loc : Loc)
  deriving Repr, Inhabited

/-- Statements. Every variant carries a Loc. -/
inductive Stmt where
  -- Phase 1 (existing)
  | varDecl  (name : String) (ty : CType) (init : Option Expr) (loc : Loc)
  | exprStmt (expr : Expr) (loc : Loc)
  | ret      (val : Option Expr) (loc : Loc)
  | ifElse   (cond : Expr) (thenBody : List Stmt) (elseBody : List Stmt) (loc : Loc)
  | while_   (cond : Expr) (body : List Stmt) (loc : Loc)
  | for_     (init : Option Stmt) (cond : Option Expr) (step : Option Expr)
             (body : List Stmt) (loc : Loc)
  | block    (stmts : List Stmt) (loc : Loc)
  -- Phase 2 (new)
  | switch_    (scrutinee : Expr) (cases : List (Option Int × List Stmt × Loc)) (loc : Loc)
  | doWhile    (body : List Stmt) (cond : Expr) (loc : Loc)
  | break_     (loc : Loc)
  | continue_  (loc : Loc)
  | goto_      (label : String) (loc : Loc)
  | label_     (name : String) (body : Stmt) (loc : Loc)
  | emptyStmt  (loc : Loc)
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

/-- Enum definition. -/
structure EnumDef where
  name    : String
  values  : List (String × Option Int)  -- name, optional explicit value
  loc     : Loc
  deriving Repr, Inhabited

/-- Union definition. Fields are (name, type) pairs. -/
structure UnionDef where
  name   : String
  fields : List (String × CType)
  loc    : Loc
  deriving Repr, Inhabited

/-- Typedef: alias name → target type. -/
structure TypedefDecl where
  name   : String
  target : CType
  loc    : Loc
  deriving Repr, Inhabited

/-- Global variable declaration. -/
structure GlobalDecl where
  name     : String
  ty       : CType
  init     : Option Expr
  isExtern : Bool
  isStatic : Bool
  loc      : Loc
  deriving Repr, Inhabited

/-- Forward declaration (extern function). -/
structure ExternDecl where
  name       : String
  ret        : CType
  params     : List Param
  isVariadic : Bool := false
  loc        : Loc
  deriving Repr, Inhabited

/-- Top-level program: all definitions. -/
structure Program where
  structs   : List StructDef
  unions    : List UnionDef
  enums     : List EnumDef
  typedefs  : List TypedefDecl
  globals   : List GlobalDecl
  externs   : List ExternDecl
  functions : List FunDef
  deriving Repr, Inhabited

-- Convenience accessors
namespace Expr

def loc : Expr → Loc
  | .intLit _ l | .charLit _ l | .var _ l => l
  | .binOp _ _ _ l | .unOp _ _ l => l
  | .index _ _ l | .member _ _ l | .arrow _ _ l => l
  | .call _ _ l | .sizeOf _ l | .assign _ _ l => l
  -- Phase 2
  | .strLit _ l | .ternary _ _ _ l | .cast _ _ l => l
  | .comma _ _ l | .initList _ l | .callFnPtr _ _ l => l
  | .nullLit l | .floatLit _ l => l

end Expr

namespace Stmt

def loc : Stmt → Loc
  | .varDecl _ _ _ l | .exprStmt _ l | .ret _ l => l
  | .ifElse _ _ _ l | .while_ _ _ l | .for_ _ _ _ _ l | .block _ l => l
  -- Phase 2
  | .switch_ _ _ l | .doWhile _ _ l => l
  | .break_ l | .continue_ l | .goto_ _ l | .label_ _ _ l | .emptyStmt l => l

end Stmt

end CCC.Syntax
