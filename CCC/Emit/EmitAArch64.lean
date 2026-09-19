/-
  CCC/Emit/EmitAArch64.lean — AArch64 code generation backend

  Targets macOS Apple Silicon (Mach-O, AAPCS64).
  Mirror of EmitX86.lean but emits AArch64 instructions.
-/
import CCC.Syntax.AST
import CCC.Emit.AArch64
import CCC.Emit.EmitX86
import CCC.Emit.Runtime

set_option autoImplicit false

namespace CCC.Emit

open CCC.Syntax

-- ═══════════════════════════════════════════════════════════════
-- Label conversion
-- ═══════════════════════════════════════════════════════════════

def labelIdToArm (l : LabelId) : ArmLabel :=
  { fn := l.fn, kind := l.kind, idx := l.idx }

def armLabelToId (l : ArmLabel) : LabelId :=
  { fn := l.fn, kind := l.kind, idx := l.idx }

-- ═══════════════════════════════════════════════════════════════
-- Codegen state
-- ═══════════════════════════════════════════════════════════════

structure ArmCodegenState where
  localOffsets : List (String × Int)
  structDefs   : List CCC.Syntax.StructDef
  typedefs     : List CCC.Syntax.TypedefDecl
  globalNames  : List (String × CType)
  nextOffset   : Int
  labelCounter : Nat
  currentFn    : String
  instrs       : List ArmInstr
  dataSection  : List String
  loopStack    : List LoopCtx
  -- FEL-59 (--harden, prototype): when true, every `.index` access through
  -- a POINTER-typed base (not a local `.array _ n`, whose size is already
  -- known at compile time) gets a runtime bounds check against the
  -- allocation-size registry in `runtime/ccc_runtime.c` before the access.
  -- Defaults to false everywhere except the explicit --harden path, so
  -- ordinary compilation is byte-for-byte unchanged.
  harden       : Bool := false
  -- FEL-68: declared parameter TYPES for every known function (from both
  -- definitions and extern prototypes), used by `emitArmCall` to size the
  -- 9th+ (stack-passed) argument's packed slot from the CALLEE's own
  -- declared type — the semantically correct source (C argument
  -- promotion follows the visible prototype's parameter type, not
  -- whatever type the caller's own expression happens to look like) —
  -- rather than `inferExprType`'s necessarily coarser guess about the
  -- argument expression itself (which, e.g., reports a bare integer
  -- literal as `.long` regardless of the narrower type it will actually
  -- be stored as). Falls back to `inferExprType` per-argument when the
  -- callee isn't in this table (an unprototyped/unknown function, which
  -- `SymbolCheck` already tolerates elsewhere) or doesn't have enough
  -- declared parameters for the position in question (e.g. the variadic
  -- tail of a `printf`-shaped call).
  funcParamTypes : List (String × List CType) := []

abbrev ArmCodegenM := StateT ArmCodegenState (Except String)

def armArgRegs : List ArmReg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

-- ═══════════════════════════════════════════════════════════════
-- Helpers
-- ═══════════════════════════════════════════════════════════════

def emitArmInstr (instr : ArmInstr) : ArmCodegenM Unit := do
  modify fun st => { st with instrs := st.instrs ++ [instr] }

def freshArmLabel (kind : String) : ArmCodegenM ArmLabel := do
  let st ← get
  let lbl : ArmLabel := { fn := st.currentFn, kind := kind, idx := st.labelCounter }
  set { st with labelCounter := st.labelCounter + 1 }
  pure lbl

/-- Push register to stack (AArch64 has no push instruction) -/
def emitArmPush (reg : ArmReg) : ArmCodegenM Unit := do
  emitArmInstr (.raw s!"    str {reg.toStr64}, [sp, #-16]!")

/-- Pop register from stack -/
def emitArmPop (reg : ArmReg) : ArmCodegenM Unit := do
  emitArmInstr (.raw s!"    ldr {reg.toStr64}, [sp], #16")

/-- Emit add or sub immediate depending on sign of offset -/
def emitAddOrSubImm (rd : ArmReg) (rn : ArmReg) (off : Int) : ArmCodegenM Unit := do
  if off == 0 then
    if rd != rn then emitArmInstr (.mov_reg rd rn)
  else if off > 0 then
    emitArmInstr (.add_imm rd rn off)
  else
    emitArmInstr (.sub_imm rd rn (-off))

/-- Load a value of type `ty` from [`rn`, #`off`] into x0, choosing the width- and
    signedness-correct instruction: sign-extending loads (`ldrsb`/`ldrsh`/`ldrsw`) for signed
    sub-word C types (so e.g. a negative `int`/`short`/`char` reloads correctly as a negative
    64-bit value), zero-extending loads (`ldrb`/`ldrh`/`ldr w`) for unsigned ones. -/
def emitArmLoadWidth (structDefs : List StructDef) (typedefs : List TypedefDecl)
    (rn : ArmReg) (off : Int) (ty : CType) : ArmCodegenM Unit := do
  let sz := cTypeSize structDefs ty
  let signed := isSignedTy (resolveType typedefs ty)
  if sz = 1 then
    if signed then emitArmInstr (.ldrsb .x0 rn off) else emitArmInstr (.ldrb .x0 rn off)
  else if sz = 2 then
    if signed then emitArmInstr (.ldrsh .x0 rn off) else emitArmInstr (.ldrh .x0 rn off)
  else if sz ≤ 4 then
    if signed then emitArmInstr (.ldrsw .x0 rn off) else emitArmInstr (.ldr_w .x0 rn off)
  else
    emitArmInstr (.ldr .x0 rn off)

/-- Store `reg` to [`rn`, #`off`] with the instruction matching a `sz`-byte C type. -/
def emitArmStoreWidth (reg : ArmReg) (rn : ArmReg) (off : Int) (sz : Nat) : ArmCodegenM Unit := do
  if sz = 1 then      emitArmInstr (.strb reg rn off)
  else if sz = 2 then emitArmInstr (.strh reg rn off)
  else if sz ≤ 4 then emitArmInstr (.str_w reg rn off)
  else                 emitArmInstr (.str reg rn off)

/-- Load from [x29, #off] with correct size + signedness instruction.
    When |off| > 255, use scratch x9 to materialise the address first
    (AArch64 unscaled load/store only supports [-256, 255]). -/
def emitLoadLocal (structDefs : List StructDef) (typedefs : List TypedefDecl)
    (off : Int) (ty : CType) : ArmCodegenM Unit := do
  if off.natAbs > 255 then
    emitAddOrSubImm .x9 .x29 off
    emitArmLoadWidth structDefs typedefs .x9 0 ty
  else
    emitArmLoadWidth structDefs typedefs .x29 off ty

/-- Store to [x29, #off] with correct size instruction.
    When |off| > 255, use scratch x9 to materialise the address first. -/
def emitStoreLocal (reg : ArmReg) (off : Int) (sz : Nat) : ArmCodegenM Unit := do
  if off.natAbs > 255 then
    emitAddOrSubImm .x9 .x29 off
    emitArmStoreWidth reg .x9 0 sz
  else
    emitArmStoreWidth reg .x29 off sz

/-- Load value from address in x0 based on type (width + signedness aware). -/
def emitArmLoadFromAddr (ty : CType) : ArmCodegenM Unit := do
  let st ← get
  emitArmLoadWidth st.structDefs st.typedefs .x0 0 ty

/-- Store x1 to address in x0 based on type size -/
def emitArmStoreToAddr (sz : Nat) : ArmCodegenM Unit := do
  emitArmStoreWidth .x1 .x0 0 sz

-- ═══════════════════════════════════════════════════════════════
-- Expression and statement codegen
-- ═══════════════════════════════════════════════════════════════

mutual

partial def emitArmLValueAddr (env : TypeEnv) (expr : Expr) : ArmCodegenM CType := do
  match expr with
  | .var name _ =>
      let st ← get
      match lookupOffset st.localOffsets name with
      | none =>
          -- Check global variables
          match st.globalNames.find? (fun (n, _) => n == name) with
          | some (_, ty) =>
              emitArmInstr (.adrp .x0 s!"_{name}")
              emitArmInstr (.add_sym .x0 .x0 s!"_{name}")
              pure ty
          | none => throw s!"unknown variable '{name}'"
      | some off =>
          emitAddOrSubImm .x0 .x29 off
          match lookupVarType env name with
          | some ty => pure ty
          | none => pure .long
  | .unOp .deref operand _ =>
      emitArmExpr env operand
      let st ← get
      let ty := resolveType st.typedefs (inferExprType env st.structDefs operand)
      match ty with
      | .pointer elem => pure elem
      | _ => pure .long
  | .index arr idx _ =>
      emitArmExpr env arr
      emitArmPush .x0
      emitArmExpr env idx
      emitArmInstr (.mov_reg .x1 .x0)
      emitArmPop .x0
      let st ← get
      let arrTy := resolveType st.typedefs (inferExprType env st.structDefs arr)
      let elemTy := resolveType st.typedefs (match arrTy with
        | .pointer elem => elem
        | .array elem _ => elem
        | _ => .long)
      let elemSize := cTypeSize st.structDefs elemTy
      -- FEL-59 (--harden, prototype): x0=base, x1=index at this point.
      -- A POINTER-typed base (heap allocation or parameter — anything
      -- whose real size isn't visible at compile time) gets a runtime
      -- check; a local `.array _ n` is left alone (its size is already
      -- known here, and the static verifier already checks what it can
      -- for those). Saves/restores x0/x1 across the call since `bl`
      -- clobbers caller-saved registers.
      if st.harden then
        match arrTy with
        | .pointer _ =>
            emitArmPush .x0
            emitArmPush .x1
            emitArmInstr (.mov_imm .x2 (Int.ofNat elemSize))
            emitArmInstr (.bl "ccc_check_index")
            emitArmPop .x1
            emitArmPop .x0
        | _ => pure ()
      else pure ()
      -- x0 = base, x1 = index; compute x0 = x0 + x1 * elemSize
      if elemSize = 1 then
        emitArmInstr (.add_reg .x0 .x0 .x1)
      else if elemSize = 2 then
        emitArmInstr (.raw "    add x0, x0, x1, lsl #1")
      else if elemSize = 4 then
        emitArmInstr (.raw "    add x0, x0, x1, lsl #2")
      else if elemSize = 8 then
        emitArmInstr (.raw "    add x0, x0, x1, lsl #3")
      else
        emitArmInstr (.mov_imm .x9 (Int.ofNat elemSize))
        emitArmInstr (.mul_reg .x1 .x1 .x9)
        emitArmInstr (.add_reg .x0 .x0 .x1)
      pure elemTy
  | .member obj field _ =>
      let st ← get
      let objTy := resolveType st.typedefs (inferExprType env st.structDefs obj)
      let structNameOpt := match objTy with
        | .struct_ sname => some sname
        | _ => none
      match structNameOpt with
      | none => throw s!"member access on non-struct value (got {repr objTy})"
      | some structName =>
          let _ ← emitArmLValueAddr env obj
          let st2 ← get
          let fieldTy := match lookupFieldType st2.structDefs structName field with
            | some ty => ty
            | none => .long
          match lookupFieldOffset st2.structDefs structName field with
          | none => throw s!"unknown field '{field}' on struct '{structName}'"
          | some off =>
              if off ≠ 0 then
                emitArmInstr (.add_imm .x0 .x0 off)
              pure fieldTy
  | .arrow ptr field _ =>
      emitArmExpr env ptr
      let st ← get
      let ptrTy := resolveType st.typedefs (inferExprType env st.structDefs ptr)
      match ptrTy with
      | .pointer (.struct_ structName) =>
          let fieldTy := match lookupFieldType st.structDefs structName field with
            | some ty => ty
            | none => .long
          match lookupFieldOffset st.structDefs structName field with
          | none => throw s!"unknown field '{field}' on struct '{structName}'"
          | some off =>
              if off ≠ 0 then
                emitArmInstr (.add_imm .x0 .x0 off)
              pure fieldTy
      | _ => throw s!"arrow access on non-pointer-to-struct (got {repr ptrTy})"
  | _ => throw "expression is not assignable (or lvalue not yet implemented)"

partial def emitArmExpr (env : TypeEnv) (expr : Expr) : ArmCodegenM Unit := do
  match expr with
  | .intLit n _ =>
      emitArmInstr (.mov_imm .x0 n)
  | .charLit c _ =>
      emitArmInstr (.mov_imm .x0 (Int.ofNat c.toNat))
  | .var name _ =>
      let st ← get
      match lookupOffset st.localOffsets name with
      | none =>
          -- Check global variables
          match st.globalNames.find? (fun (n, _) => n == name) with
          | some (_, ty) =>
              emitArmInstr (.adrp .x0 s!"_{name}")
              emitArmInstr (.add_sym .x0 .x0 s!"_{name}")
              match ty with
              | .array _ _ => pure ()  -- array decays to pointer (address already in x0)
              | _ => emitArmLoadFromAddr ty
          | none => throw s!"unknown variable '{name}'"
      | some off =>
          let ty := match lookupVarType env name with
            | some t => t
            | none => .long
          match ty with
          | .array _ _ =>
              emitAddOrSubImm .x0 .x29 off
          | _ =>
              emitLoadLocal st.structDefs st.typedefs off ty
  | .binOp op lhs rhs _ =>
      match op with
      | .add =>
          let st ← get
          let lty := resolveType st.typedefs (inferExprType env st.structDefs lhs)
          let rty := resolveType st.typedefs (inferExprType env st.structDefs rhs)
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.add_reg .x0 .x0 .x1)
          match narrowIntTruncKind st.structDefs lty rty with
          | some true => emitArmInstr (.sxtw .x0 .x0)
          | some false => emitArmInstr (.uxtw .x0 .x0)
          | none => pure ()
      | .sub =>
          let st ← get
          let lty := resolveType st.typedefs (inferExprType env st.structDefs lhs)
          let rty := resolveType st.typedefs (inferExprType env st.structDefs rhs)
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.sub_reg .x0 .x0 .x1)
          match narrowIntTruncKind st.structDefs lty rty with
          | some true => emitArmInstr (.sxtw .x0 .x0)
          | some false => emitArmInstr (.uxtw .x0 .x0)
          | none => pure ()
      | .mul =>
          let st ← get
          let lty := resolveType st.typedefs (inferExprType env st.structDefs lhs)
          let rty := resolveType st.typedefs (inferExprType env st.structDefs rhs)
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.mul_reg .x0 .x0 .x1)
          match narrowIntTruncKind st.structDefs lty rty with
          | some true => emitArmInstr (.sxtw .x0 .x0)
          | some false => emitArmInstr (.uxtw .x0 .x0)
          | none => pure ()
      | .div =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          if signed then emitArmInstr (.sdiv .x0 .x0 .x1)
          else emitArmInstr (.udiv .x0 .x0 .x1)
      | .mod =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          -- x0 = lhs, x1 = rhs; x0 % x1 = lhs - (lhs/rhs)*rhs
          if signed then emitArmInstr (.sdiv .x9 .x0 .x1)
          else emitArmInstr (.udiv .x9 .x0 .x1)
          emitArmInstr (.msub .x0 .x9 .x1 .x0)
      | .eq =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "eq")
      | .ne =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "ne")
      | .lt =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 (if signed then "lt" else "lo"))
      | .gt =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 (if signed then "gt" else "hi"))
      | .le =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 (if signed then "le" else "ls"))
      | .ge =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
                     && isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs rhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 (if signed then "ge" else "hs"))
      | .and_ =>
          let falseLbl ← freshArmLabel "and_false"
          let endLbl ← freshArmLabel "and_end"
          emitArmExpr env lhs
          emitArmInstr (.cmp_imm .x0 0)
          emitArmInstr (.b_cond "eq" falseLbl)
          emitArmExpr env rhs
          emitArmInstr (.cmp_imm .x0 0)
          emitArmInstr (.cset .x0 "ne")
          emitArmInstr (.b endLbl)
          emitArmInstr (.label_ falseLbl)
          emitArmInstr (.mov_imm .x0 0)
          emitArmInstr (.label_ endLbl)
      | .or_ =>
          let trueLbl ← freshArmLabel "or_true"
          let endLbl ← freshArmLabel "or_end"
          emitArmExpr env lhs
          emitArmInstr (.cmp_imm .x0 0)
          emitArmInstr (.b_cond "ne" trueLbl)
          emitArmExpr env rhs
          emitArmInstr (.cmp_imm .x0 0)
          emitArmInstr (.cset .x0 "ne")
          emitArmInstr (.b endLbl)
          emitArmInstr (.label_ trueLbl)
          emitArmInstr (.mov_imm .x0 1)
          emitArmInstr (.label_ endLbl)
      | .bitAnd =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.and_reg .x0 .x0 .x1)
      | .bitOr =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.orr_reg .x0 .x0 .x1)
      | .bitXor =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.eor_reg .x0 .x0 .x1)
      | .shl =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.lsl_reg .x0 .x0 .x1)
      | .shr =>
          let st ← get
          let signed := isSignedTy (resolveType st.typedefs (inferExprType env st.structDefs lhs))
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          if signed then emitArmInstr (.asr_reg .x0 .x0 .x1)
          else emitArmInstr (.lsr_reg .x0 .x0 .x1)
      -- Compound assignment ops
      | .addAssign => emitArmCompoundAssign env lhs rhs .add
      | .subAssign => emitArmCompoundAssign env lhs rhs .sub
      | .mulAssign => emitArmCompoundAssign env lhs rhs .mul
      | .divAssign => emitArmCompoundAssign env lhs rhs .div
      | .modAssign => emitArmCompoundAssign env lhs rhs .mod
      | .andAssign => emitArmCompoundAssign env lhs rhs .bitAnd
      | .orAssign => emitArmCompoundAssign env lhs rhs .bitOr
      | .xorAssign => emitArmCompoundAssign env lhs rhs .bitXor
      | .shlAssign => emitArmCompoundAssign env lhs rhs .shl
      | .shrAssign => emitArmCompoundAssign env lhs rhs .shr
  | .unOp op operand _ =>
      match op with
      | .neg =>
          emitArmExpr env operand
          emitArmInstr (.neg .x0 .x0)
      | .not_ =>
          emitArmExpr env operand
          emitArmInstr (.cmp_imm .x0 0)
          emitArmInstr (.cset .x0 "eq")
      | .deref =>
          emitArmExpr env operand
          let st ← get
          let ptrTy := resolveType st.typedefs (inferExprType env st.structDefs operand)
          let valTy := match ptrTy with
            | .pointer elem => elem
            | _ => .long
          emitArmLoadFromAddr valTy
      | .addrOf =>
          let _ ← emitArmLValueAddr env operand
          pure ()
      | .bitNot =>
          emitArmExpr env operand
          emitArmInstr (.mvn .x0 .x0)
      | .preInc =>
          let lhsTy ← emitArmLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          emitArmInstr (.mov_reg .x9 .x0)   -- x9 = addr
          emitArmLoadWidth st.structDefs st.typedefs .x9 0 lhsTy  -- x0 = old value
          emitArmInstr (.add_imm .x0 .x0 1)
          emitArmStoreWidth .x0 .x9 0 sz     -- store new value
      | .preDec =>
          let lhsTy ← emitArmLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmLoadWidth st.structDefs st.typedefs .x9 0 lhsTy
          emitArmInstr (.sub_imm .x0 .x0 1)
          emitArmStoreWidth .x0 .x9 0 sz
      | .postInc =>
          let lhsTy ← emitArmLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmLoadWidth st.structDefs st.typedefs .x9 0 lhsTy
          emitArmInstr (.mov_reg .x10 .x0)  -- x10 = old value (return this)
          emitArmInstr (.add_imm .x0 .x0 1)
          emitArmStoreWidth .x0 .x9 0 sz
          emitArmInstr (.mov_reg .x0 .x10)  -- return old
      | .postDec =>
          let lhsTy ← emitArmLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmLoadWidth st.structDefs st.typedefs .x9 0 lhsTy
          emitArmInstr (.mov_reg .x10 .x0)
          emitArmInstr (.sub_imm .x0 .x0 1)
          emitArmStoreWidth .x0 .x9 0 sz
          emitArmInstr (.mov_reg .x0 .x10)
  | .index arr idx loc_ =>
      let _ ← emitArmLValueAddr env (.index arr idx loc_)
      let st ← get
      let valTy := resolveType st.typedefs (inferExprType env st.structDefs (.index arr idx loc_))
      emitArmLoadFromAddr valTy
  | .member obj field loc_ =>
      let _ ← emitArmLValueAddr env (.member obj field loc_)
      let st ← get
      let valTy := resolveType st.typedefs (inferExprType env st.structDefs (.member obj field loc_))
      match valTy with
      | .array _ _ => pure ()
      | _ => emitArmLoadFromAddr valTy
  | .arrow ptr field loc_ =>
      let _ ← emitArmLValueAddr env (.arrow ptr field loc_)
      let st ← get
      let valTy := resolveType st.typedefs (inferExprType env st.structDefs (.arrow ptr field loc_))
      match valTy with
      | .array _ _ => pure ()
      | _ => emitArmLoadFromAddr valTy
  | .call fn args _ =>
      emitArmCall env fn args
  | .sizeOf ty _ =>
      let st ← get
      let resolvedTy := resolveType st.typedefs ty
      emitArmInstr (.mov_imm .x0 (Int.ofNat (cTypeSize st.structDefs resolvedTy)))
  | .sizeOfExpr operand _ =>
      -- FEL-68: mirrors the x86 emitter's `.sizeOfExpr` case — see its
      -- comment. The operand is never evaluated, only its inferred type.
      let st ← get
      let opTy := inferExprType env st.structDefs operand
      let resolvedTy := resolveType st.typedefs opTy
      emitArmInstr (.mov_imm .x0 (Int.ofNat (cTypeSize st.structDefs resolvedTy)))
  | .assign lhs rhs _ =>
      emitArmExpr env rhs
      emitArmPush .x0               -- push rhs value
      let lhsTy ← emitArmLValueAddr env lhs  -- x0 = address
      emitArmPop .x1                -- x1 = rhs value
      let st ← get
      let sz := cTypeSize st.structDefs lhsTy
      emitArmStoreToAddr sz         -- store x1 to [x0]
      emitArmInstr (.mov_reg .x0 .x1)  -- result = rhs value
  | .strLit val _ =>
      let st ← get
      let strLabel := s!".LC{st.labelCounter}"
      set { st with labelCounter := st.labelCounter + 1,
                     dataSection := st.dataSection ++ [s!"{strLabel}:", s!"    .asciz \"{val}\""] }
      emitArmInstr (.adrp .x0 strLabel)
      emitArmInstr (.add_sym .x0 .x0 strLabel)
  | .ternary cond thenExpr elseExpr _ =>
      let elseLbl ← freshArmLabel "tern_else"
      let endLbl ← freshArmLabel "tern_end"
      emitArmExpr env cond
      emitArmInstr (.cbz .x0 elseLbl)
      emitArmExpr env thenExpr
      emitArmInstr (.b endLbl)
      emitArmInstr (.label_ elseLbl)
      emitArmExpr env elseExpr
      emitArmInstr (.label_ endLbl)
  | .cast _ operand _ =>
      emitArmExpr env operand
  | .comma left right _ =>
      emitArmExpr env left
      emitArmExpr env right
  | .initList elems _ =>
      match elems with
      | [] => emitArmInstr (.mov_imm .x0 0)
      | _ =>
        for e in elems do
          emitArmExpr env e
  | .callFnPtr fnExpr args _ =>
      for arg in args.reverse do
        emitArmExpr env arg
        emitArmPush .x0
      let regsToUse := (armArgRegs.take args.length)
      for reg in regsToUse do
        emitArmPop reg
      emitArmExpr env fnExpr
      emitArmInstr (.blr .x0)
  | .nullLit _ => emitArmInstr (.mov_imm .x0 0)
  | .floatLit _ _ => emitArmInstr (.mov_imm .x0 0)

/-- Compound assignment: lhs op= rhs -/
partial def emitArmCompoundAssign (env : TypeEnv) (lhs : Expr) (rhs : Expr) (op : BinOp)
    : ArmCodegenM Unit := do
  -- Evaluate rhs first
  emitArmExpr env rhs
  emitArmPush .x0               -- push rhs
  -- Get lvalue address
  let lhsTy ← emitArmLValueAddr env lhs
  let st ← get
  let sz := cTypeSize st.structDefs lhsTy
  let lty := resolveType st.typedefs lhsTy
  let rty := resolveType st.typedefs (inferExprType env st.structDefs rhs)
  let lSigned := isSignedTy lty
  let signed := lSigned && isSignedTy rty
  emitArmInstr (.mov_reg .x9 .x0)   -- x9 = addr
  emitArmLoadWidth st.structDefs st.typedefs .x9 0 lhsTy  -- x0 = old value
  emitArmPop .x1                     -- x1 = rhs
  -- Perform operation: x0 = x0 op x1
  match op with
  | .add => emitArmInstr (.add_reg .x0 .x0 .x1)
  | .sub => emitArmInstr (.sub_reg .x0 .x0 .x1)
  | .mul => emitArmInstr (.mul_reg .x0 .x0 .x1)
  | .div => if signed then emitArmInstr (.sdiv .x0 .x0 .x1) else emitArmInstr (.udiv .x0 .x0 .x1)
  | .mod =>
      if signed then emitArmInstr (.sdiv .x10 .x0 .x1) else emitArmInstr (.udiv .x10 .x0 .x1)
      emitArmInstr (.msub .x0 .x10 .x1 .x0)
  | .bitAnd => emitArmInstr (.and_reg .x0 .x0 .x1)
  | .bitOr => emitArmInstr (.orr_reg .x0 .x0 .x1)
  | .bitXor => emitArmInstr (.eor_reg .x0 .x0 .x1)
  | .shl => emitArmInstr (.lsl_reg .x0 .x0 .x1)
  | .shr => if lSigned then emitArmInstr (.asr_reg .x0 .x0 .x1) else emitArmInstr (.lsr_reg .x0 .x0 .x1)
  | _ => pure ()
  -- Truncate add/sub/mul results back to the lhs width if it's a narrow (<=32-bit) int type
  match op with
  | .add | .sub | .mul =>
      match narrowIntTruncKind st.structDefs lty rty with
      | some true => emitArmInstr (.sxtw .x0 .x0)
      | some false => emitArmInstr (.uxtw .x0 .x0)
      | none => pure ()
  | _ => pure ()
  -- Store result back
  emitArmStoreWidth .x0 .x9 0 sz

/-- FEL-68 (was FEL-51): calls with more than `armArgRegs.length` (8)
    arguments used to throw "too many arguments" outright — the libheif
    corpus port had to fold a parameter into another one to fit under
    this limit. AAPCS64 passes the 9th+ argument on the caller's stack,
    in an "outgoing argument area" reserved just below the current sp at
    the moment of `bl`.

    Each stack argument is packed at its OWN natural size/alignment
    within that area, per `CCC.Syntax.Layout.packedOffsets` — see its
    docstring for why (Apple's arm64 ABI does not pad every stack
    argument to 8 bytes, unlike the base AAPCS64 spec; this was found
    empirically, by an earlier version of this function that used a
    uniform 8-byte stride failing a real `cc`-compiled-callee test while
    passing every CCC-only self-consistency test). The value is evaluated
    and stored WIDTH-CORRECTLY (`emitArmStoreWidth`, matching the arg's
    real C type size) to its packed slot IMMEDIATELY after reserving the
    area, before touching any register argument: a fixed-offset store
    never moves `sp`, and every earlier stack argument's own evaluation
    is itself balanced (any push/pop or nested call it contains nets to
    zero SP change), so `sp` is guaranteed to still equal the reserved
    area's base by the time each one executes. Register arguments (the
    first 8) are evaluated and handled afterwards via the pre-existing
    push-then-pop-in-reverse pattern, itself balanced too. -/
partial def emitArmCall (env : TypeEnv) (fn : String) (args : List Expr) : ArmCodegenM Unit := do
  let nRegArgs := min args.length armArgRegs.length
  let regArgs := args.take nRegArgs
  let stackArgs := args.drop nRegArgs
  if !stackArgs.isEmpty then
    let st ← get
    -- Prefer the callee's own declared parameter types (see
    -- `funcParamTypes`'s docstring on why); fall back to inferring each
    -- argument expression's type only when the callee isn't known or
    -- doesn't declare enough parameters for this position.
    let declared? := (st.funcParamTypes.find? (·.1 == fn)).map (·.2 |>.drop nRegArgs)
    let stackTypes := match declared? with
      | some declTys =>
          if declTys.length == stackArgs.length then
            declTys.map (resolveType st.typedefs)
          else
            stackArgs.map (fun a => resolveType st.typedefs (inferExprType env st.structDefs a))
      | none => stackArgs.map (fun a => resolveType st.typedefs (inferExprType env st.structDefs a))
    let (offsets, packedSize) := Layout.packedOffsets st.structDefs stackTypes
    let stackBytes := roundUp16 packedSize
    emitArmInstr (.sub_imm .sp .sp (Int.ofNat stackBytes))
    for ((arg, ty), off) in stackArgs.zip stackTypes |>.zip offsets do
      emitArmExpr env arg
      emitArmStoreWidth .x0 .sp (Int.ofNat off) (cTypeSize st.structDefs ty)
    -- Evaluate each register arg and push onto stack
    for arg in regArgs do
      emitArmExpr env arg
      emitArmPush .x0
    let regsToUse := (armArgRegs.take nRegArgs).reverse
    for reg in regsToUse do
      emitArmPop reg
    emitArmInstr (.bl (builtinName fn))
    emitArmInstr (.add_imm .sp .sp (Int.ofNat stackBytes))
  else
    -- Evaluate each register arg and push onto stack
    for arg in regArgs do
      emitArmExpr env arg
      emitArmPush .x0
    -- Pop into argument registers in reverse order
    let regsToUse := (armArgRegs.take nRegArgs).reverse
    for reg in regsToUse do
      emitArmPop reg
    emitArmInstr (.bl (builtinName fn))

end

-- ═══════════════════════════════════════════════════════════════
-- Statement codegen
-- ═══════════════════════════════════════════════════════════════

mutual

partial def emitArmStmt (env : TypeEnv) (retLabel : ArmLabel) (stmt : Stmt) : ArmCodegenM Unit := do
  match stmt with
  | .varDecl name ty init _ =>
      match init with
      | none => pure ()
      | some e =>
          emitArmExpr env e
          let st ← get
          match lookupOffset st.localOffsets name with
          | none => throw s!"missing stack slot for variable '{name}'"
          | some off =>
              let sz := cTypeSize st.structDefs ty
              emitStoreLocal .x0 off sz
  | .exprStmt e _ =>
      emitArmExpr env e
  | .ret val _ =>
      match val with
      | none => emitArmInstr (.mov_imm .x0 0)
      | some e => emitArmExpr env e
      emitArmInstr (.b retLabel)
  | .ifElse cond thenBody elseBody _ =>
      let elseLbl ← freshArmLabel "if_else"
      let endLbl ← freshArmLabel "if_end"
      emitArmExpr env cond
      emitArmInstr (.cbz .x0 elseLbl)
      emitArmStmts env retLabel thenBody
      emitArmInstr (.b endLbl)
      emitArmInstr (.label_ elseLbl)
      emitArmStmts env retLabel elseBody
      emitArmInstr (.label_ endLbl)
  | .while_ cond body _ =>
      let loopLbl ← freshArmLabel "while_loop"
      let endLbl ← freshArmLabel "while_end"
      let loopId := armLabelToId loopLbl
      let endId := armLabelToId endLbl
      modify fun st => { st with loopStack := ⟨endId, some loopId⟩ :: st.loopStack }
      emitArmInstr (.label_ loopLbl)
      emitArmExpr env cond
      emitArmInstr (.cbz .x0 endLbl)
      emitArmStmts env retLabel body
      emitArmInstr (.b loopLbl)
      emitArmInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .for_ init cond step body _ =>
      match init with
      | none => pure ()
      | some initStmt => emitArmStmt env retLabel initStmt
      let loopLbl ← freshArmLabel "for_loop"
      let stepLbl ← freshArmLabel "for_step"
      let endLbl ← freshArmLabel "for_end"
      let stepId := armLabelToId stepLbl
      let endId := armLabelToId endLbl
      modify fun st => { st with loopStack := ⟨endId, some stepId⟩ :: st.loopStack }
      emitArmInstr (.label_ loopLbl)
      match cond with
      | none => pure ()
      | some condExpr =>
          emitArmExpr env condExpr
          emitArmInstr (.cbz .x0 endLbl)
      emitArmStmts env retLabel body
      emitArmInstr (.label_ stepLbl)
      match step with
      | none => pure ()
      | some stepExpr => emitArmExpr env stepExpr
      emitArmInstr (.b loopLbl)
      emitArmInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .block stmts _ =>
      emitArmStmts env retLabel stmts
  | .switch_ scrutinee cases _ =>
      let endLbl ← freshArmLabel "switch_end"
      let endId := armLabelToId endLbl
      modify fun st => { st with loopStack := ⟨endId, none⟩ :: st.loopStack }
      emitArmExpr env scrutinee
      emitArmPush .x0
      let mut caseLbls : List (Option Int × ArmLabel) := []
      let mut defaultLbl : Option ArmLabel := none
      for c in cases do
        let (val, _, _) := c
        let lbl ← freshArmLabel "case"
        caseLbls := caseLbls ++ [(val, lbl)]
        match val with
        | none => defaultLbl := some lbl
        | _ => pure ()
      -- Emit comparisons
      for (val, lbl) in caseLbls do
        match val with
        | some v =>
            emitArmInstr (.ldr .x0 .sp 0)
            emitArmInstr (.mov_imm .x1 v)
            emitArmInstr (.cmp_reg .x0 .x1)
            emitArmInstr (.b_cond "eq" lbl)
        | none => pure ()
      match defaultLbl with
      | some dl => emitArmInstr (.b dl)
      | none => emitArmInstr (.b endLbl)
      -- Pop scrutinee
      emitArmPop .x0
      -- Emit case bodies
      let casePairs := List.zip cases caseLbls
      for ((_, body, _), (_, lbl)) in casePairs do
        emitArmInstr (.label_ lbl)
        emitArmStmts env retLabel body
      emitArmInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .doWhile body cond _ =>
      let loopLbl ← freshArmLabel "do_loop"
      let endLbl ← freshArmLabel "do_end"
      let loopId := armLabelToId loopLbl
      let endId := armLabelToId endLbl
      modify fun st => { st with loopStack := ⟨endId, some loopId⟩ :: st.loopStack }
      emitArmInstr (.label_ loopLbl)
      emitArmStmts env retLabel body
      emitArmExpr env cond
      emitArmInstr (.cbnz .x0 loopLbl)
      emitArmInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .break_ _ => do
      let st ← get
      match st.loopStack with
      | ctx :: _ => emitArmInstr (.b (labelIdToArm ctx.breakLabel))
      | [] => emitArmInstr (.comment "break: no enclosing loop")
  | .continue_ _ => do
      let st ← get
      match st.loopStack with
      | ctx :: _ =>
          match ctx.continueLabel with
          | some lbl => emitArmInstr (.b (labelIdToArm lbl))
          | none => emitArmInstr (.comment "continue: in switch, no target")
      | [] => emitArmInstr (.comment "continue: no enclosing loop")
  | .goto_ labelName _ =>
      let lbl : ArmLabel := { fn := "", kind := labelName, idx := 0 }
      emitArmInstr (.b lbl)
  | .label_ name body _ =>
      let lbl : ArmLabel := { fn := "", kind := name, idx := 0 }
      emitArmInstr (.label_ lbl)
      emitArmStmt env retLabel body
  | .emptyStmt _ => pure ()

partial def emitArmStmts (env : TypeEnv) (retLabel : ArmLabel) (stmts : List Stmt)
    : ArmCodegenM Unit := do
  for stmt in stmts do
    emitArmStmt env retLabel stmt

end

-- ═══════════════════════════════════════════════════════════════
-- Function and program emission
-- ═══════════════════════════════════════════════════════════════

/-- FEL-68 (was FEL-51): spill every parameter into its local stack slot.
    `List.zip params armArgRegs` used to silently TRUNCATE at 8 params —
    a function DEFINED with more than 8 parameters got no error (unlike
    the call-site throw this pairs with) and no spill code at all for the
    9th+ parameter, so that local's stack slot was left as whatever
    garbage was already on the stack: a genuine, silent correctness bug,
    not just a missing feature.

    The 9th+ parameter is spilled from the CALLER's outgoing
    stack-argument area (see `emitArmCall`'s docstring for the packed
    layout — computed HERE from these parameters' own declared types,
    which a correctly-typed call site necessarily agrees with) rather
    than a register. At the point `emitArmParamMoves` runs, the prologue
    has already executed `stp x29, x30, [sp, #-16]!` and `mov x29, sp`,
    so `x29` sits 16 bytes BELOW the incoming `sp` — the caller placed
    the packed stack-argument area starting at `[incoming_sp, #0]`,
    i.e. `[x29, #16 + packedOffset]`. Each is loaded width- and
    signedness-correctly (`emitArmLoadWidth`, matching `emitArmCall`'s
    width-correct store on the other end of this same value) into `x0`,
    then spilled into the local slot with a plain 64-bit store — the
    same convention the register-parameter path above already uses
    regardless of the parameter's real declared width. -/
def emitArmParamMoves (structDefs : List StructDef) (typedefs : List TypedefDecl)
    (params : List Param) (offsets : List (String × Int)) : ArmCodegenM Unit := do
  let regParams := params.take armArgRegs.length
  let stackParams := params.drop armArgRegs.length
  let pairs := List.zip regParams armArgRegs
  for pair in pairs do
    let (p, reg) := pair
    match lookupOffset offsets p.name with
    | none => throw s!"missing stack slot for parameter '{p.name}'"
    | some off =>
        emitArmInstr (.str reg .x29 off)
  if !stackParams.isEmpty then
    let stackTypes := stackParams.map (fun p => resolveType typedefs p.ty)
    let (packedOffs, _) := Layout.packedOffsets structDefs stackTypes
    for ((p, ty), packedOff) in stackParams.zip stackTypes |>.zip packedOffs do
      match lookupOffset offsets p.name with
      | none => throw s!"missing stack slot for parameter '{p.name}'"
      | some off =>
          emitArmLoadWidth structDefs typedefs .x29 (16 + Int.ofNat packedOff) ty
          emitArmInstr (.str .x0 .x29 off)

def emitArmFunction (structDefs : List StructDef) (typedefs : List TypedefDecl)
    (globalNames : List (String × CType)) (fn : FunDef) (harden : Bool := false)
    (funcParamTypes : List (String × List CType) := [])
    : Except String (List ArmInstr × List String) := do
  let paramBindings : TypeEnv := fn.params.map (fun (p : Param) => (p.name, p.ty))
  let localBindings : TypeEnv := collectVarDecls fn.body
  let stackBindings : TypeEnv := paramBindings ++ localBindings
  let allBindings : TypeEnv := stackBindings ++ globalNames
  let offsets := assignOffsets structDefs stackBindings
  let localsSize : Nat := match offsets.getLast? with
    | some (_, lastOff) => roundUp16 (Int.natAbs lastOff)
    | none => 0
  let initialState : ArmCodegenState := {
    localOffsets := offsets
    structDefs := structDefs
    typedefs := typedefs
    globalNames := globalNames
    nextOffset := -(Int.ofNat (localsSize + 16))
    labelCounter := 0
    currentFn := fn.name
    instrs := []
    dataSection := []
    loopStack := []
    harden := harden
    funcParamTypes := funcParamTypes
  }
  let env : TypeEnv := allBindings
  let retLabel : ArmLabel := { fn := fn.name, kind := "ret", idx := 0 }
  let codegen : ArmCodegenM Unit := do
    -- Prologue
    emitArmInstr (.stp .x29 .x30 .sp (-16))      -- stp x29, x30, [sp, #-16]!
    emitArmInstr (.mov_reg .x29 .sp)               -- mov x29, sp
    if localsSize > 0 then
      emitArmInstr (.sub_imm .sp .sp (Int.ofNat localsSize))
    -- Spill parameters
    emitArmParamMoves structDefs typedefs fn.params offsets
    -- Body
    emitArmStmts env retLabel fn.body
    -- Default return 0 for non-void
    if fn.ret == .void then
      pure ()
    else
      emitArmInstr (.mov_imm .x0 0)
    -- Return label and epilogue
    emitArmInstr (.label_ retLabel)
    emitArmInstr (.mov_reg .sp .x29)
    emitArmInstr (.raw "    ldp x29, x30, [sp], #16")
    emitArmInstr .ret
  let (_, finalState) ← codegen.run initialState
  pure (finalState.instrs, finalState.dataSection)

/-- Render a complete AArch64 function to assembly lines -/
def renderArmFunction (name : String) (instrs : List ArmInstr) : List String :=
  [s!".globl _{name}", s!".p2align 2", s!"_{name}:"] ++ instrs.map ArmInstr.render

/-- Emit an entire program as AArch64 assembly -/
def emitProgramAArch64 (prog : CCC.Syntax.Program) (harden : Bool := false)
    : Except String String := do
  let globalNames : List (String × CType) := prog.globals.map (fun g => (g.name, g.ty))
  -- FEL-68: declared parameter types for every function definition AND
  -- extern prototype in this program, keyed by name — see
  -- `ArmCodegenState.funcParamTypes`'s docstring for why `emitArmCall`
  -- needs this rather than inferring each stack argument's type from the
  -- caller's own expression. Definitions take priority over externs when
  -- both name the same function (mirrors `SymbolCheck.buildSymbolTable`'s
  -- own precedence for the same reason: a forward-declared-then-defined
  -- function's real definition is the more trustworthy source).
  let funcParamTypes : List (String × List CType) :=
    (prog.functions.map (fun f => (f.name, f.params.map (·.ty)))) ++
    (prog.externs.map (fun e => (e.name, e.params.map (·.ty))))
  let mut allInstrs : List String := []
  let mut allData : List String := []
  for fn in prog.functions do
    let (instrs, dataLines) ←
      emitArmFunction prog.structs prog.typedefs globalNames fn harden funcParamTypes
    allInstrs := allInstrs ++ renderArmFunction fn.name instrs
    allData := allData ++ dataLines
  -- Emit global variable storage
  let mut globalDataLines : List String := []
  let mut globalBssLines : List String := []
  for g in prog.globals do
    if g.isExtern then continue
    let sz := cTypeSize prog.structs g.ty
    let alignPow := if sz ≥ 8 then 3 else if sz ≥ 4 then 2 else if sz ≥ 2 then 1 else 0
    match g.init with
    | none =>
        -- Uninitialized → BSS
        globalBssLines := globalBssLines ++ [s!".globl _{g.name}",
          s!".zerofill __DATA,__bss,_{g.name},{sz},{alignPow}"]
    | some (.initList elems _) =>
        -- FEL-68: a global ARRAY's brace initializer (`int tbl[8] = {1,2,3};`)
        -- — previously the parser didn't even register a global array's
        -- SYMBOL at all (`static const int tbl[8] = {...}` vanished from
        -- the program entirely, worse than merely losing its values), and
        -- when it did register one, the initializer was parsed and
        -- discarded, so it fell to the `none` branch above and came out
        -- all-zero. Real C libraries lean heavily on this exact pattern
        -- for lookup/CRC/coefficient tables. Each element is emitted with
        -- the directive matching the ARRAY'S ELEMENT type's size (not the
        -- whole array's), matching real ABI layout; C zero-pads any
        -- trailing elements the initializer list didn't provide.
        let elemTy := match g.ty with
          | .array e _ => e
          | _ => g.ty
        let elemSz := max 1 (cTypeSize prog.structs elemTy)
        let elemAlignPow := if elemSz ≥ 8 then 3 else if elemSz ≥ 4 then 2 else if elemSz ≥ 2 then 1 else 0
        let count := match g.ty with
          | .array _ n => n
          | _ => elems.length
        let directiveFor (v : Int) : String :=
          if elemSz ≤ 1 then s!"    .byte {v}"
          else if elemSz ≤ 2 then s!"    .short {v}"
          else if elemSz ≤ 4 then s!"    .long {v}"
          else s!"    .quad {v}"
        let valueOf (e : Expr) : Int :=
          match e with
          | .intLit n _ => n
          | .charLit c _ => Int.ofNat c.toNat
          | _ => 0
        globalDataLines := globalDataLines ++
          [s!".globl _{g.name}", s!".p2align {elemAlignPow}", s!"_{g.name}:"]
        for i in List.range count do
          let v := match elems[i]? with
            | some e => valueOf e
            | none => 0
          globalDataLines := globalDataLines ++ [directiveFor v]
    | some initExpr =>
        -- Initialized → DATA
        let val := match initExpr with
          | .intLit n _ => n
          | .charLit c _ => Int.ofNat c.toNat
          | _ => 0
        globalDataLines := globalDataLines ++ [s!".globl _{g.name}", s!".p2align {alignPow}", s!"_{g.name}:"]
        if sz ≤ 1 then
          globalDataLines := globalDataLines ++ [s!"    .byte {val}"]
        else if sz ≤ 4 then
          globalDataLines := globalDataLines ++ [s!"    .long {val}"]
        else
          globalDataLines := globalDataLines ++ [s!"    .quad {val}"]
  let textSection := [".section __TEXT,__text"] ++ allInstrs
  let cstringSection :=
    if allData.isEmpty then []
    else [".section __TEXT,__cstring"] ++ allData
  let dataSection :=
    if globalDataLines.isEmpty then []
    else [".section __DATA,__data"] ++ globalDataLines
  let bssSection := globalBssLines  -- .zerofill is self-contained
  let lines := textSection ++ cstringSection ++ dataSection ++ bssSection
  pure (String.intercalate "\n" lines ++ "\n")

end CCC.Emit
