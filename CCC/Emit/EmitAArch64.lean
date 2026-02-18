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

/-- Load from [x29, #off] with correct size instruction -/
def emitLoadLocal (off : Int) (sz : Nat) : ArmCodegenM Unit := do
  if sz = 1 then
    emitArmInstr (.ldrb .x0 .x29 off)
  else if sz ≤ 4 then
    emitArmInstr (.ldr_w .x0 .x29 off)
  else
    emitArmInstr (.ldr .x0 .x29 off)

/-- Store to [x29, #off] with correct size instruction -/
def emitStoreLocal (reg : ArmReg) (off : Int) (sz : Nat) : ArmCodegenM Unit := do
  if sz = 1 then
    emitArmInstr (.strb reg .x29 off)
  else if sz ≤ 4 then
    emitArmInstr (.str_w reg .x29 off)
  else
    emitArmInstr (.str reg .x29 off)

/-- Load value from address in x0 based on type -/
def emitArmLoadFromAddr (ty : CType) : ArmCodegenM Unit := do
  let st ← get
  let sz := cTypeSize st.structDefs ty
  if sz = 1 then
    emitArmInstr (.ldrb .x0 .x0 0)
  else if sz ≤ 4 then
    emitArmInstr (.ldr_w .x0 .x0 0)
  else
    emitArmInstr (.ldr .x0 .x0 0)

/-- Store x1 to address in x0 based on type size -/
def emitArmStoreToAddr (sz : Nat) : ArmCodegenM Unit := do
  if sz = 1 then
    emitArmInstr (.strb .x1 .x0 0)
  else if sz ≤ 4 then
    emitArmInstr (.str_w .x1 .x0 0)
  else
    emitArmInstr (.str .x1 .x0 0)

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
      let ty := inferExprType env st.structDefs operand
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
      let arrTy := inferExprType env st.structDefs arr
      let elemTy := match arrTy with
        | .pointer elem => elem
        | .array elem _ => elem
        | _ => .long
      let elemSize := cTypeSize st.structDefs elemTy
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
              let sz := cTypeSize st.structDefs ty
              emitLoadLocal off sz
  | .binOp op lhs rhs _ =>
      match op with
      | .add =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.add_reg .x0 .x0 .x1)
      | .sub =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.sub_reg .x0 .x0 .x1)
      | .mul =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.mul_reg .x0 .x0 .x1)
      | .div =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.sdiv .x0 .x0 .x1)
      | .mod =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          -- x0 = lhs, x1 = rhs; x0 % x1 = lhs - (lhs/rhs)*rhs
          emitArmInstr (.sdiv .x9 .x0 .x1)
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
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "lt")
      | .gt =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "gt")
      | .le =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "le")
      | .ge =>
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.cmp_reg .x0 .x1)
          emitArmInstr (.cset .x0 "ge")
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
          emitArmExpr env lhs
          emitArmPush .x0
          emitArmExpr env rhs
          emitArmInstr (.mov_reg .x1 .x0)
          emitArmPop .x0
          emitArmInstr (.asr_reg .x0 .x0 .x1)
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
          let ptrTy := inferExprType env st.structDefs operand
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
          let _lhsTy ← emitArmLValueAddr env operand
          emitArmInstr (.mov_reg .x9 .x0)   -- x9 = addr
          emitArmInstr (.ldr .x0 .x9 0)     -- x0 = old value
          emitArmInstr (.add_imm .x0 .x0 1)
          emitArmInstr (.str .x0 .x9 0)     -- store new value
      | .preDec =>
          let _lhsTy ← emitArmLValueAddr env operand
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmInstr (.ldr .x0 .x9 0)
          emitArmInstr (.sub_imm .x0 .x0 1)
          emitArmInstr (.str .x0 .x9 0)
      | .postInc =>
          let _lhsTy ← emitArmLValueAddr env operand
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmInstr (.ldr .x0 .x9 0)
          emitArmInstr (.mov_reg .x10 .x0)  -- x10 = old value (return this)
          emitArmInstr (.add_imm .x0 .x0 1)
          emitArmInstr (.str .x0 .x9 0)
          emitArmInstr (.mov_reg .x0 .x10)  -- return old
      | .postDec =>
          let _lhsTy ← emitArmLValueAddr env operand
          emitArmInstr (.mov_reg .x9 .x0)
          emitArmInstr (.ldr .x0 .x9 0)
          emitArmInstr (.mov_reg .x10 .x0)
          emitArmInstr (.sub_imm .x0 .x0 1)
          emitArmInstr (.str .x0 .x9 0)
          emitArmInstr (.mov_reg .x0 .x10)
  | .index arr idx loc_ =>
      let _ ← emitArmLValueAddr env (.index arr idx loc_)
      let st ← get
      let valTy := inferExprType env st.structDefs (.index arr idx loc_)
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
  let _lhsTy ← emitArmLValueAddr env lhs
  emitArmInstr (.mov_reg .x9 .x0)   -- x9 = addr
  emitArmInstr (.ldr .x0 .x9 0)     -- x0 = old value
  emitArmPop .x1                     -- x1 = rhs
  -- Perform operation: x0 = x0 op x1
  match op with
  | .add => emitArmInstr (.add_reg .x0 .x0 .x1)
  | .sub => emitArmInstr (.sub_reg .x0 .x0 .x1)
  | .mul => emitArmInstr (.mul_reg .x0 .x0 .x1)
  | .div => emitArmInstr (.sdiv .x0 .x0 .x1)
  | .mod =>
      emitArmInstr (.sdiv .x10 .x0 .x1)
      emitArmInstr (.msub .x0 .x10 .x1 .x0)
  | .bitAnd => emitArmInstr (.and_reg .x0 .x0 .x1)
  | .bitOr => emitArmInstr (.orr_reg .x0 .x0 .x1)
  | .bitXor => emitArmInstr (.eor_reg .x0 .x0 .x1)
  | .shl => emitArmInstr (.lsl_reg .x0 .x0 .x1)
  | .shr => emitArmInstr (.asr_reg .x0 .x0 .x1)
  | _ => pure ()
  -- Store result back
  emitArmInstr (.str .x0 .x9 0)

partial def emitArmCall (env : TypeEnv) (fn : String) (args : List Expr) : ArmCodegenM Unit := do
  if args.length > armArgRegs.length then
    throw s!"too many arguments for call to '{fn}'"
  -- Evaluate each arg and push onto stack
  for arg in args do
    emitArmExpr env arg
    emitArmPush .x0
  -- Pop into argument registers in reverse order
  let regsToUse := (armArgRegs.take args.length).reverse
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

def emitArmParamMoves (params : List Param) (offsets : List (String × Int)) : ArmCodegenM Unit := do
  let pairs := List.zip params armArgRegs
  for pair in pairs do
    let (p, reg) := pair
    match lookupOffset offsets p.name with
    | none => throw s!"missing stack slot for parameter '{p.name}'"
    | some off =>
        emitArmInstr (.str reg .x29 off)

def emitArmFunction (structDefs : List StructDef) (typedefs : List TypedefDecl)
    (globalNames : List (String × CType)) (fn : FunDef)
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
    emitArmParamMoves fn.params offsets
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
def emitProgramAArch64 (prog : CCC.Syntax.Program) : Except String String := do
  let globalNames : List (String × CType) := prog.globals.map (fun g => (g.name, g.ty))
  let mut allInstrs : List String := []
  let mut allData : List String := []
  for fn in prog.functions do
    let (instrs, dataLines) ← emitArmFunction prog.structs prog.typedefs globalNames fn
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
