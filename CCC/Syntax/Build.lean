/-
  CCC/Syntax/Build.lean — Convenience constructors for hand-built test ASTs

  Used by CCC02 (verifier) and CCC03 (emitter) to build test programs
  without needing the parser. Enables parallel development.
-/

import CCC.Syntax.AST

namespace CCC.Syntax.Build

/-- Make a source location from a line number. -/
def loc (line : Nat) : Loc := ⟨line, 1⟩

-- ══════════════════════════════════════════════════════════════
-- Expressions
-- ══════════════════════════════════════════════════════════════

def intLit (val : Int) (line : Nat := 0) : Expr := .intLit val (loc line)
def charLit (val : Char) (line : Nat := 0) : Expr := .charLit val (loc line)
def var (name : String) (line : Nat := 0) : Expr := .var name (loc line)

def binOp (op : BinOp) (l r : Expr) (line : Nat := 0) : Expr := .binOp op l r (loc line)
def add (l r : Expr) (line : Nat := 0) : Expr := binOp .add l r line
def sub (l r : Expr) (line : Nat := 0) : Expr := binOp .sub l r line
def mul (l r : Expr) (line : Nat := 0) : Expr := binOp .mul l r line
def div (l r : Expr) (line : Nat := 0) : Expr := binOp .div l r line
def mod_ (l r : Expr) (line : Nat := 0) : Expr := binOp .mod l r line
def lt (l r : Expr) (line : Nat := 0) : Expr := binOp .lt l r line
def gt (l r : Expr) (line : Nat := 0) : Expr := binOp .gt l r line
def le (l r : Expr) (line : Nat := 0) : Expr := binOp .le l r line
def ge (l r : Expr) (line : Nat := 0) : Expr := binOp .ge l r line
def eq (l r : Expr) (line : Nat := 0) : Expr := binOp .eq l r line
def ne (l r : Expr) (line : Nat := 0) : Expr := binOp .ne l r line
def and_ (l r : Expr) (line : Nat := 0) : Expr := binOp .and_ l r line
def or_ (l r : Expr) (line : Nat := 0) : Expr := binOp .or_ l r line

def unOp (op : UnOp) (e : Expr) (line : Nat := 0) : Expr := .unOp op e (loc line)
def neg (e : Expr) (line : Nat := 0) : Expr := unOp .neg e line
def not_ (e : Expr) (line : Nat := 0) : Expr := unOp .not_ e line
def deref (e : Expr) (line : Nat := 0) : Expr := unOp .deref e line
def addrOf (e : Expr) (line : Nat := 0) : Expr := unOp .addrOf e line

def call (fn : String) (args : List Expr) (line : Nat := 0) : Expr := .call fn args (loc line)
def index (arr : Expr) (idx : Expr) (line : Nat := 0) : Expr := .index arr idx (loc line)
def member (obj : Expr) (field : String) (line : Nat := 0) : Expr := .member obj field (loc line)
def arrow (ptr : Expr) (field : String) (line : Nat := 0) : Expr := .arrow ptr field (loc line)
def assign (l r : Expr) (line : Nat := 0) : Expr := .assign l r (loc line)
def sizeOfTy (ty : CType) (line : Nat := 0) : Expr := .sizeOf ty (loc line)

-- ══════════════════════════════════════════════════════════════
-- Statements
-- ══════════════════════════════════════════════════════════════

def varDecl (name : String) (ty : CType) (init : Option Expr := none) (line : Nat := 0) : Stmt :=
  .varDecl name ty init (loc line)

def exprStmt (e : Expr) (line : Nat := 0) : Stmt := .exprStmt e (loc line)

def ret (val : Option Expr := none) (line : Nat := 0) : Stmt := .ret val (loc line)
def retVal (e : Expr) (line : Nat := 0) : Stmt := .ret (some e) (loc line)

def ifElse (cond : Expr) (t : List Stmt) (e : List Stmt := []) (line : Nat := 0) : Stmt :=
  .ifElse cond t e (loc line)

def while_ (cond : Expr) (body : List Stmt) (line : Nat := 0) : Stmt :=
  .while_ cond body (loc line)

def for_ (init : Option Stmt) (cond : Option Expr) (step : Option Expr)
    (body : List Stmt) (line : Nat := 0) : Stmt :=
  .for_ init cond step body (loc line)

def block (stmts : List Stmt) (line : Nat := 0) : Stmt := .block stmts (loc line)

-- ══════════════════════════════════════════════════════════════
-- Top-level definitions
-- ══════════════════════════════════════════════════════════════

def param (name : String) (ty : CType) : Param := { name, ty }

def funDef (name : String) (retTy : CType) (params : List Param) (body : List Stmt) : FunDef :=
  { name, ret := retTy, params, body, loc := loc 1 }

def structDef (name : String) (fields : List (String × CType)) : StructDef :=
  { name, fields, loc := loc 1 }

def program (structs : List StructDef := []) (fns : List FunDef) : Program :=
  { structs, functions := fns }

-- ══════════════════════════════════════════════════════════════
-- Common patterns
-- ══════════════════════════════════════════════════════════════

/-- `malloc(n)` call — returns a pointer that needs null-checking. -/
def malloc (sizeExpr : Expr) (line : Nat := 0) : Expr := call "malloc" [sizeExpr] line

/-- `free(ptr)` call. -/
def free (ptr : Expr) (line : Nat := 0) : Expr := call "free" [ptr] line

/-- `memcpy(dst, src, n)` call. -/
def memcpy (dst src n : Expr) (line : Nat := 0) : Expr := call "memcpy" [dst, src, n] line

/-- `sizeof(T)` expression. -/
def sizeOf (ty : CType) (line : Nat := 0) : Expr := .sizeOf ty (loc line)

/-- Variable declaration with initializer: `int x = expr;` -/
def varInit (name : String) (ty : CType) (init : Expr) (line : Nat := 0) : Stmt :=
  .varDecl name ty (some init) (loc line)

/-- Null check pattern: `if (ptr == 0) { return -1; }` -/
def nullCheck (ptrName : String) (line : Nat := 0) : Stmt :=
  ifElse (eq (var ptrName line) (intLit 0 line))
         [retVal (intLit (-1) line) line]
         []
         line

end CCC.Syntax.Build
