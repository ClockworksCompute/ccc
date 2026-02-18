/-
  CCC/IR/IR.lean — Target-independent intermediate representation

  Sits between AST lowering and backend code generation.
  Virtual registers (infinite supply), typed loads/stores,
  structured control flow labels.

  Types only — no lowering logic in this file.
-/

import CCC.Syntax.AST

namespace CCC.IR

open CCC.Syntax

/-- Virtual register — infinite supply, allocated by lowering. -/
structure VReg where
  id : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

namespace VReg
def v (n : Nat) : VReg := ⟨n⟩
instance : ToString VReg where toString (r : VReg) := s!"v{r.id}"
end VReg

/-- IR binary operations. -/
inductive IRBinOp where
  -- Integer arithmetic
  | add | sub | mul | sdiv | udiv | smod | umod
  -- Floating-point arithmetic
  | fadd | fsub | fmul | fdiv
  -- Comparison (returns 0 or 1)
  | eq | ne | slt | sgt | sle | sge   -- signed
  | ult | ugt | ule | uge             -- unsigned
  | feq | fne | flt | fgt | fle | fge -- float
  -- Bitwise
  | and_ | or_ | xor_ | shl | lshr | ashr
  -- Logical
  | logAnd | logOr
  deriving Repr, Inhabited, BEq

/-- IR unary operations. -/
inductive IRUnOp where
  | neg     -- integer negate
  | fneg    -- float negate
  | not_    -- logical not (0→1, nonzero→0)
  | bitNot  -- bitwise complement
  | intToFloat | floatToInt          -- conversion
  | sext | zext | trunc             -- width changes
  deriving Repr, Inhabited, BEq

/-- IR type widths for loads/stores. -/
inductive IRWidth where
  | w8 | w16 | w32 | w64 | wf32 | wf64
  deriving Repr, Inhabited, BEq

/-- IR instructions — virtual-register, typed, target-independent. -/
inductive IRInstr where
  -- Local variable access
  | loadLocal    (dst : VReg) (name : String) (width : IRWidth)
  | storeLocal   (src : VReg) (name : String) (width : IRWidth)
  -- Memory access (address in register)
  | loadMem      (dst : VReg) (addr : VReg) (width : IRWidth)
  | storeMem     (addr : VReg) (src : VReg) (width : IRWidth)
  -- Constants
  | loadImm      (dst : VReg) (val : Int)
  | loadFloat    (dst : VReg) (val : Float)
  | loadAddr     (dst : VReg) (symbol : String)     -- address of global/string
  | leaLocal     (dst : VReg) (name : String)        -- address of local variable
  -- Arithmetic
  | binop        (op : IRBinOp) (dst : VReg) (lhs : VReg) (rhs : VReg)
  | unop         (op : IRUnOp) (dst : VReg) (src : VReg)
  -- Calls
  | call         (fn : String) (args : List VReg) (dst : Option VReg)
  | callIndirect (fp : VReg) (args : List VReg) (dst : Option VReg)
  -- Control flow
  | branch       (cond : VReg) (thenLabel : String) (elseLabel : String)
  | jump         (label : String)
  | ret          (val : Option VReg)
  | label        (name : String)
  -- Type conversion / extension
  | convert      (op : IRUnOp) (dst : VReg) (src : VReg) (fromWidth : IRWidth) (toWidth : IRWidth)
  -- Address computation
  | offsetAddr   (dst : VReg) (base : VReg) (offset : VReg) (scale : Nat)
  | addImm       (dst : VReg) (src : VReg) (imm : Int)
  -- Comparison + branch (fused for peephole)
  | cmpBranch    (op : IRBinOp) (lhs : VReg) (rhs : VReg) (thenLabel : String) (elseLabel : String)
  -- Switch (multi-way branch)
  | switch_      (scrutinee : VReg) (cases : List (Int × String)) (defaultLabel : String)
  -- Misc
  | comment      (text : String)
  | phi          (dst : VReg) (sources : List (String × VReg))  -- SSA phi node
  | nop
  deriving Repr, Inhabited

/-- Local variable slot with type and stack offset. -/
structure IRLocal where
  name   : String
  ty     : CType
  offset : Nat       -- filled in by backend
  deriving Repr, Inhabited

/-- IR function definition. -/
structure IRFunction where
  name       : String
  params     : List (String × CType)
  returnType : CType
  locals     : List IRLocal
  body       : List IRInstr
  deriving Repr, Inhabited

/-- Global data item (for .data / .rodata sections). -/
inductive IRData where
  | bytes    (label : String) (data : List UInt8)
  | string   (label : String) (val : String)      -- null-terminated
  | zeroed   (label : String) (size : Nat)         -- .bss
  | intVal   (label : String) (val : Int) (width : IRWidth)
  deriving Repr, Inhabited

/-- IR program — all functions + global data. -/
structure IRProgram where
  functions   : List IRFunction
  globals     : List (String × CType × Option IRData)  -- name, type, initializer
  rodata      : List IRData                              -- string literals, etc.
  deriving Repr, Inhabited

/-- IR generation state — used by lowering passes. -/
structure IRGenState where
  nextReg    : Nat
  instrs     : List IRInstr
  locals     : List IRLocal
  labelCount : Nat
  deriving Repr, Inhabited

namespace IRGenState

def empty : IRGenState :=
  { nextReg := 0, instrs := [], locals := [], labelCount := 0 }

def freshReg (st : IRGenState) : VReg × IRGenState :=
  (⟨st.nextReg⟩, { st with nextReg := st.nextReg + 1 })

def freshLabel (st : IRGenState) (pfx : String) : String × IRGenState :=
  (s!".L_{pfx}_{st.labelCount}", { st with labelCount := st.labelCount + 1 })

def emit (st : IRGenState) (instr : IRInstr) : IRGenState :=
  { st with instrs := st.instrs ++ [instr] }

def addLocal (st : IRGenState) (local_ : IRLocal) : IRGenState :=
  { st with locals := st.locals ++ [local_] }

end IRGenState

/-- IR generation monad. -/
abbrev IRGenM := StateT IRGenState (Except String)

namespace IRGenM

def freshReg : IRGenM VReg := do
  let st ← get
  let (reg, st') := st.freshReg
  set st'
  pure reg

def freshLabel (pfx : String) : IRGenM String := do
  let st ← get
  let (lbl, st') := st.freshLabel pfx
  set st'
  pure lbl

def emit (instr : IRInstr) : IRGenM Unit := do
  modify (·.emit instr)

def addLocal (local_ : IRLocal) : IRGenM Unit := do
  modify (·.addLocal local_)

end IRGenM

end CCC.IR
