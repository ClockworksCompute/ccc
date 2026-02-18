import CCC.Syntax.AST
import CCC.Emit.X86
import CCC.Emit.Runtime

namespace CCC.Emit

open CCC.Syntax

/-- Loop context for break/continue targets. -/
structure LoopCtx where
  breakLabel    : LabelId
  continueLabel : Option LabelId  -- None for switch (no continue target)
  deriving Repr, Inhabited

structure CodegenState where
  localOffsets : List (String × Int)
  structDefs   : List CCC.Syntax.StructDef
  typedefs     : List CCC.Syntax.TypedefDecl
  nextOffset   : Int
  labelCounter : Nat
  currentFn    : String
  instrs       : List Instr
  dataSection  : List String
  loopStack    : List LoopCtx

abbrev CodegenM := StateT CodegenState (Except String)

abbrev TypeEnv := List (String × CType)

def argRegs : List Register :=
  [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

def builtinName (fn : String) : String :=
  mapRuntimeBuiltin fn


def lookupOffset (locals : List (String × Int)) (name : String) : Option Int :=
  match locals with
  | [] => none
  | (n, off) :: rest =>
      if n = name then some off else lookupOffset rest name


def lookupVarType (env : TypeEnv) (name : String) : Option CType :=
  match env with
  | [] => none
  | (n, ty) :: rest =>
      if n = name then some ty else lookupVarType rest name


def findStructDef (defs : List StructDef) (name : String) : Option StructDef :=
  match defs with
  | [] => none
  | d :: rest =>
      if d.name = name then some d else findStructDef rest name


partial def cTypeSize (defs : List StructDef) (ty : CType) : Nat :=
  match ty with
  | .void => 0
  | .int => 4
  | .char => 1
  | .long => 8
  | .bool => 1
  | .unsigned inner => cTypeSize defs inner
  | .pointer _ => 8
  | .array elem n => n * cTypeSize defs elem
  | .struct_ name =>
      match findStructDef defs name with
      | none => 0
      | some s =>
          s.fields.foldl (fun acc field =>
            let (_, fTy) := field
            acc + cTypeSize defs fTy) 0
  | .sizeT => 8
  -- Phase 2 types
  | .float_ => 4
  | .double_ => 8
  | .short => 2
  | .longLong => 8
  | .signed inner => cTypeSize defs inner
  | .enum_ _ => 4
  | .union_ _ => 0              -- TODO: look up union def
  | .funcPtr _ _ => 8
  | .typedef_ _ => 8            -- fallback; callers should resolveType first
  | .const_ inner => cTypeSize defs inner
  | .volatile_ inner => cTypeSize defs inner
  | .restrict_ inner => cTypeSize defs inner


def lookupFieldType (defs : List StructDef) (structName : String) (fieldName : String) : Option CType :=
  match findStructDef defs structName with
  | none => none
  | some s =>
      let rec go (fields : List (String × CType)) : Option CType :=
        match fields with
        | [] => none
        | (fname, fty) :: rest =>
            if fname = fieldName then some fty else go rest
      go s.fields


def lookupFieldOffset (defs : List StructDef) (structName : String) (fieldName : String) : Option Int :=
  match findStructDef defs structName with
  | none => none
  | some s =>
      let rec go (fields : List (String × CType)) (acc : Nat) : Option Int :=
        match fields with
        | [] => none
        | (fname, fty) :: rest =>
            if fname = fieldName then
              some (Int.ofNat acc)
            else
              go rest (acc + cTypeSize defs fty)
      go s.fields 0


def emitInstr (instr : Instr) : CodegenM Unit := do
  modify fun st => { st with instrs := st.instrs ++ [instr] }


def freshLabel (kind : String) : CodegenM LabelId := do
  let st <- get
  let lbl : LabelId := { fn := st.currentFn, kind := kind, idx := st.labelCounter }
  set { st with labelCounter := st.labelCounter + 1 }
  pure lbl


def emitLoadFromAddr (ty : CType) : CodegenM Unit := do
  let st <- get
  let sz := cTypeSize st.structDefs ty
  if sz = 1 then
    emitInstr (.movb (.mem .rax 0) (.reg .al))
    emitInstr (.movzbl (.reg .al) (.reg .eax))
  else if sz = 4 then
    emitInstr (.movl (.mem .rax 0) (.reg .eax))
  else
    emitInstr (.mov (.mem .rax 0) (.reg .rax))


/-- Resolve typedef chains: typedef_ "Node" → struct_ "Node" etc.
    Also stored as TypeEnv context for programs with typedefs. -/
partial def resolveType (typedefs : List TypedefDecl) (ty : CType) : CType :=
  match ty with
  | .typedef_ name =>
      match typedefs.find? (fun td => td.name == name) with
      | some td => resolveType typedefs td.target
      | none => ty  -- unresolved, keep as-is
  | .pointer inner => .pointer (resolveType typedefs inner)
  | .array inner n => .array (resolveType typedefs inner) n
  | _ => ty

partial def inferExprType (env : TypeEnv) (defs : List StructDef) (expr : Expr) : CType :=
  match expr with
  | .intLit _ _ => .long
  | .charLit _ _ => .char
  | .var name _ =>
      match lookupVarType env name with
      | some ty => ty
      | none => .long
  | .binOp op _ _ _ =>
      match op with
      | .eq | .ne | .lt | .gt | .le | .ge | .and_ | .or_ => .int
      | _ => .long
  | .unOp op operand _ =>
      match op with
      | .addrOf => .pointer (inferExprType env defs operand)
      | .deref =>
          match inferExprType env defs operand with
          | .pointer elem => elem
          | _ => .long
      | .not_ => .int
      | .neg | .bitNot => .long
      | .preInc | .preDec | .postInc | .postDec => inferExprType env defs operand
  | .index arr _ _ =>
      match inferExprType env defs arr with
      | .pointer elem => elem
      | .array elem _ => elem
      | _ => .long
  | .member obj field _ =>
      match inferExprType env defs obj with
      | .struct_ sname =>
          match lookupFieldType defs sname field with
          | some ty => ty
          | none => .long
      | _ => .long
  | .arrow ptr field _ =>
      match inferExprType env defs ptr with
      | .pointer (.struct_ sname) =>
          match lookupFieldType defs sname field with
          | some ty => ty
          | none => .long
      | _ => .long
  | .call _ _ _ => .long
  | .sizeOf _ _ => .sizeT
  | .assign lhs _ _ => inferExprType env defs lhs
  -- Phase 2 Expr
  | .strLit _ _ => .pointer .char
  | .nullLit _ => .pointer .void
  | .floatLit _ _ => .double_
  | .ternary _ t _ _ => inferExprType env defs t
  | .cast ty _ _ => ty
  | .comma _ r _ => inferExprType env defs r
  | .initList _ _ => .long
  | .callFnPtr _ _ _ => .long


def emitBoolFromFlags (mkSet : Operand → Instr) : CodegenM Unit := do
  emitInstr (mkSet (.reg .al))
  emitInstr (.movzbl (.reg .al) (.reg .eax))


mutual

partial def emitLValueAddr (env : TypeEnv) (expr : Expr) : CodegenM CType := do
  match expr with
  | .var name _ =>
      let st <- get
      match lookupOffset st.localOffsets name with
      | none => throw s!"unknown variable '{name}'"
      | some off =>
          emitInstr (.lea (.mem .rbp off) (.reg .rax))
          match lookupVarType env name with
          | some ty => pure ty
          | none => pure .long
  | .unOp .deref operand _ =>
      emitExpr env operand
      let st <- get
      let ty := inferExprType env st.structDefs operand
      match ty with
      | .pointer elem => pure elem
      | _ => pure .long
  | .index arr idx _ =>
      emitExpr env arr
      emitInstr (.push (.reg .rax))
      emitExpr env idx
      emitInstr (.mov (.reg .rax) (.reg .rcx))
      emitInstr (.pop (.reg .rax))
      let st <- get
      let arrTy := inferExprType env st.structDefs arr
      let elemTy := match arrTy with
        | .pointer elem => elem
        | .array elem _ => elem
        | _ => .long
      let elemSize := cTypeSize st.structDefs elemTy
      if elemSize = 1 then
        emitInstr (.lea (.memIdx .rax .rcx 1 0) (.reg .rax))
      else if elemSize = 2 then
        emitInstr (.lea (.memIdx .rax .rcx 2 0) (.reg .rax))
      else if elemSize = 4 then
        emitInstr (.lea (.memIdx .rax .rcx 4 0) (.reg .rax))
      else if elemSize = 8 then
        emitInstr (.lea (.memIdx .rax .rcx 8 0) (.reg .rax))
      else
        emitInstr (.imul (.imm (Int.ofNat elemSize)) (.reg .rcx))
        emitInstr (.add (.reg .rcx) (.reg .rax))
      pure elemTy
  | .member obj field _ =>
      let st <- get
      let objTy := resolveType st.typedefs (inferExprType env st.structDefs obj)
      let structNameOpt := match objTy with
        | .struct_ sname => some sname
        | _ => none
      match structNameOpt with
      | none => throw s!"member access on non-struct value (got {repr objTy})"
      | some structName =>
          let _ <- emitLValueAddr env obj
          let st2 <- get
          let fieldTy := match lookupFieldType st2.structDefs structName field with
            | some ty => ty
            | none => .long
          match lookupFieldOffset st2.structDefs structName field with
          | none => throw s!"unknown field '{field}' on struct '{structName}'"
          | some off =>
              if off ≠ 0 then
                emitInstr (.add (.imm off) (.reg .rax))
              pure fieldTy
  | .arrow ptr field _ =>
      emitExpr env ptr
      let st <- get
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
                emitInstr (.add (.imm off) (.reg .rax))
              pure fieldTy
      | _ => throw s!"arrow access on non-pointer-to-struct (got {repr ptrTy})"
  | _ => throw "expression is not assignable (or Phase 2 lvalue not yet implemented)"


partial def emitCmpBinOp (env : TypeEnv) (lhs rhs : Expr) (mkSet : Operand → Instr) : CodegenM Unit := do
  emitExpr env lhs
  emitInstr (.push (.reg .rax))
  emitExpr env rhs
  emitInstr (.pop (.reg .rcx))
  emitInstr (.cmp (.reg .rax) (.reg .rcx))
  emitBoolFromFlags mkSet


partial def emitCall (env : TypeEnv) (fn : String) (args : List Expr) : CodegenM Unit := do
  if args.length > argRegs.length then
    throw s!"too many arguments for call to '{fn}'"
  for arg in args do
    emitExpr env arg
    emitInstr (.push (.reg .rax))
  let regsToUse := (argRegs.take args.length).reverse
  for reg in regsToUse do
    emitInstr (.pop (.reg reg))
  emitInstr (.call (builtinName fn))


partial def emitExpr (env : TypeEnv) (expr : Expr) : CodegenM Unit := do
  match expr with
  | .intLit n _ =>
      emitInstr (.mov (.imm n) (.reg .rax))
  | .charLit c _ =>
      emitInstr (.mov (.imm (Int.ofNat c.toNat)) (.reg .rax))
  | .var name _ =>
      let st <- get
      match lookupOffset st.localOffsets name with
      | none => throw s!"unknown variable '{name}'"
      | some off =>
          let ty := match lookupVarType env name with
            | some t => t
            | none => .long
          match ty with
          | .array _ _ =>
              emitInstr (.lea (.mem .rbp off) (.reg .rax))
          | _ =>
              let sz := cTypeSize st.structDefs ty
              if sz = 1 then
                emitInstr (.movb (.mem .rbp off) (.reg .al))
                emitInstr (.movzbl (.reg .al) (.reg .eax))
              else if sz = 4 then
                emitInstr (.movl (.mem .rbp off) (.reg .eax))
              else
                emitInstr (.mov (.mem .rbp off) (.reg .rax))
  | .binOp op lhs rhs _ =>
      match op with
      | .add =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.add (.reg .rcx) (.reg .rax))
      | .sub =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.sub (.reg .rax) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .mul =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.imul (.reg .rcx) (.reg .rax))
      | .div =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.mov (.reg .rax) (.reg .rcx))
          emitInstr (.pop (.reg .rax))
          emitInstr .cqo
          emitInstr (.idiv (.reg .rcx))
      | .mod =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.mov (.reg .rax) (.reg .rcx))
          emitInstr (.pop (.reg .rax))
          emitInstr .cqo
          emitInstr (.idiv (.reg .rcx))
          emitInstr (.mov (.reg .rdx) (.reg .rax))
      | .eq => emitCmpBinOp env lhs rhs Instr.sete
      | .ne => emitCmpBinOp env lhs rhs Instr.setne
      | .lt => emitCmpBinOp env lhs rhs Instr.setl
      | .gt => emitCmpBinOp env lhs rhs Instr.setg
      | .le => emitCmpBinOp env lhs rhs Instr.setle
      | .ge => emitCmpBinOp env lhs rhs Instr.setge
      | .and_ =>
          emitExpr env lhs
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.setne (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.setne (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
          emitInstr (.pop (.reg .rcx))
          emitInstr (.imul (.reg .rcx) (.reg .rax))
      | .or_ =>
          emitExpr env lhs
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.setne (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.setne (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
          emitInstr (.pop (.reg .rcx))
          emitInstr (.add (.reg .rcx) (.reg .rax))
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.setne (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
      -- Phase 2 BinOps: bitwise
      | .bitAnd =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.and_ (.reg .rcx) (.reg .rax))
      | .bitOr =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.or_ (.reg .rcx) (.reg .rax))
      | .bitXor =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.pop (.reg .rcx))
          emitInstr (.xor_ (.reg .rcx) (.reg .rax))
      | .shl =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.mov (.reg .rax) (.reg .rcx))
          emitInstr (.pop (.reg .rax))
          emitInstr (.shl (.reg .cl) (.reg .rax))
      | .shr =>
          emitExpr env lhs
          emitInstr (.push (.reg .rax))
          emitExpr env rhs
          emitInstr (.mov (.reg .rax) (.reg .rcx))
          emitInstr (.pop (.reg .rax))
          emitInstr (.shr (.reg .cl) (.reg .rax))
      -- Phase 2 BinOps: compound assignment (desugar to load-op-store)
      -- lhs is the target, rhs is the delta; emit: addr=lhs, old=*addr, new=old OP rhs, *addr=new
      | .addAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))          -- push rhs value
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))  -- old value
          emitInstr (.push (.reg .rax))          -- push addr
          emitInstr (.pop (.reg .rax))           -- addr in rax
          emitInstr (.pop (.reg .rdx))           -- rhs in rdx
          emitInstr (.add (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .subAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .rdx))
          emitInstr (.sub (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .mulAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .rdx))
          emitInstr (.imul (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .divAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.push (.reg .rax))          -- push addr
          emitInstr (.mov (.mem .rax 0) (.reg .rax)) -- old in rax
          emitInstr .cqo
          emitInstr (.pop (.reg .rcx))           -- addr in rcx (temp)
          emitInstr (.push (.reg .rcx))          -- re-push addr
          -- rhs is on stack below addr; complex register dance
          -- Simplified: use r11 for addr
          emitInstr (.pop (.reg .r11))           -- addr
          emitInstr (.pop (.reg .rcx))           -- rhs
          emitInstr (.push (.reg .r11))          -- re-push addr
          emitInstr (.idiv (.reg .rcx))
          emitInstr (.pop (.reg .rcx))           -- addr
          emitInstr (.mov (.reg .rax) (.mem .rcx 0))
      | .modAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.push (.reg .rax))
          emitInstr (.mov (.mem .rax 0) (.reg .rax))
          emitInstr .cqo
          emitInstr (.pop (.reg .r11))
          emitInstr (.pop (.reg .rcx))
          emitInstr (.push (.reg .r11))
          emitInstr (.idiv (.reg .rcx))
          emitInstr (.pop (.reg .rcx))
          emitInstr (.mov (.reg .rdx) (.mem .rcx 0))  -- remainder in rdx
          emitInstr (.mov (.reg .rdx) (.reg .rax))
      | .andAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .rdx))
          emitInstr (.and_ (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .orAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .rdx))
          emitInstr (.or_ (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .xorAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .rdx))
          emitInstr (.xor_ (.reg .rdx) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .shlAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.push (.reg .rcx))
          emitInstr (.mov (.mem .rsp 8) (.reg .r11)) -- addr
          -- shift amount in cl
          emitInstr (.pop (.reg .rax))           -- old value
          emitInstr (.pop (.reg .r11))           -- addr
          emitInstr (.pop (.reg .rcx))           -- shift amount
          emitInstr (.shl (.reg .cl) (.reg .rax))
          emitInstr (.mov (.reg .rax) (.mem .r11 0))
      | .shrAssign =>
          emitExpr env rhs
          emitInstr (.push (.reg .rax))
          let _lhsTy ← emitLValueAddr env lhs
          emitInstr (.mov (.mem .rax 0) (.reg .rcx))
          emitInstr (.push (.reg .rax))
          emitInstr (.push (.reg .rcx))
          emitInstr (.pop (.reg .rax))
          emitInstr (.pop (.reg .r11))
          emitInstr (.pop (.reg .rcx))
          emitInstr (.shr (.reg .cl) (.reg .rax))
          emitInstr (.mov (.reg .rax) (.mem .r11 0))
  | .unOp op operand _ =>
      match op with
      | .neg =>
          emitExpr env operand
          emitInstr (.mov (.imm 0) (.reg .rcx))
          emitInstr (.sub (.reg .rax) (.reg .rcx))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .not_ =>
          emitExpr env operand
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.sete (.reg .al))
          emitInstr (.movzbl (.reg .al) (.reg .eax))
      | .deref =>
          emitExpr env operand
          let st <- get
          let ptrTy := inferExprType env st.structDefs operand
          let valTy := match ptrTy with
            | .pointer elem => elem
            | _ => .long
          emitLoadFromAddr valTy
      | .addrOf =>
          let _ <- emitLValueAddr env operand
          pure ()
      -- Phase 2 UnOps
      | .bitNot =>
          emitExpr env operand
          emitInstr (.not_ (.reg .rax))
      | .preInc =>
          let lhsTy ← emitLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          if sz ≤ 4 then do
            emitInstr (.movl (.mem .rax 0) (.reg .ecx))
            emitInstr (.add (.imm 1) (.reg .rcx))
            emitInstr (.movl (.reg .ecx) (.mem .rax 0))
          else do
            emitInstr (.mov (.mem .rax 0) (.reg .rcx))
            emitInstr (.add (.imm 1) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .preDec =>
          let lhsTy ← emitLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          if sz ≤ 4 then do
            emitInstr (.movl (.mem .rax 0) (.reg .ecx))
            emitInstr (.sub (.imm 1) (.reg .rcx))
            emitInstr (.movl (.reg .ecx) (.mem .rax 0))
          else do
            emitInstr (.mov (.mem .rax 0) (.reg .rcx))
            emitInstr (.sub (.imm 1) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          emitInstr (.mov (.reg .rcx) (.reg .rax))
      | .postInc =>
          let lhsTy ← emitLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          if sz ≤ 4 then do
            emitInstr (.movl (.mem .rax 0) (.reg .ecx))
            emitInstr (.mov (.reg .rcx) (.reg .rax))  -- return old value
            emitInstr (.add (.imm 1) (.reg .rcx))
            emitInstr (.movl (.reg .ecx) (.mem .rax 0))  -- but store new
          else do
            emitInstr (.mov (.mem .rax 0) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.reg .rax))
            emitInstr (.add (.imm 1) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.mem .rax 0))
          -- rax still holds old value
      | .postDec =>
          let lhsTy ← emitLValueAddr env operand
          let st ← get
          let sz := cTypeSize st.structDefs lhsTy
          if sz ≤ 4 then do
            emitInstr (.movl (.mem .rax 0) (.reg .ecx))
            emitInstr (.mov (.reg .rcx) (.reg .rax))
            emitInstr (.sub (.imm 1) (.reg .rcx))
            emitInstr (.movl (.reg .ecx) (.mem .rax 0))
          else do
            emitInstr (.mov (.mem .rax 0) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.reg .rax))
            emitInstr (.sub (.imm 1) (.reg .rcx))
            emitInstr (.mov (.reg .rcx) (.mem .rax 0))
  | .index arr idx loc =>
      let _ <- emitLValueAddr env (.index arr idx loc)
      let st <- get
      let valTy := inferExprType env st.structDefs (.index arr idx loc)
      emitLoadFromAddr valTy
  | .member obj field loc =>
      let _ <- emitLValueAddr env (.member obj field loc)
      let st <- get
      let valTy := resolveType st.typedefs (inferExprType env st.structDefs (.member obj field loc))
      match valTy with
      | .array _ _ => pure ()  -- array decays to pointer; address already in %rax
      | _ => emitLoadFromAddr valTy
  | .arrow ptr field loc =>
      let _ <- emitLValueAddr env (.arrow ptr field loc)
      let st <- get
      let valTy := resolveType st.typedefs (inferExprType env st.structDefs (.arrow ptr field loc))
      match valTy with
      | .array _ _ => pure ()  -- array decays to pointer; address already in %rax
      | _ => emitLoadFromAddr valTy
  | .call fn args _ =>
      emitCall env fn args
  | .sizeOf ty _ =>
      let st <- get
      let resolvedTy := resolveType st.typedefs ty
      emitInstr (.mov (.imm (Int.ofNat (cTypeSize st.structDefs resolvedTy))) (.reg .rax))
  | .assign lhs rhs _ =>
      emitExpr env rhs
      emitInstr (.push (.reg .rax))
      let lhsTy <- emitLValueAddr env lhs
      emitInstr (.pop (.reg .rcx))
      let st <- get
      let sz := cTypeSize st.structDefs lhsTy
      if sz = 1 then
        emitInstr (.movb (.reg .cl) (.mem .rax 0))
      else if sz = 4 then
        emitInstr (.movl (.reg .ecx) (.mem .rax 0))
      else
        emitInstr (.mov (.reg .rcx) (.mem .rax 0))
      emitInstr (.mov (.reg .rcx) (.reg .rax))
  -- Phase 2 Expr
  | .strLit val _ =>
      -- String literals go in .rodata; emit address load
      let st ← get
      let strLabel := s!".LC{st.labelCounter}"
      set { st with labelCounter := st.labelCounter + 1,
                     dataSection := st.dataSection ++ [s!"{strLabel}:", s!"    .string \"{val}\""] }
      emitInstr (.lea (.label strLabel) (.reg .rax))
  | .ternary cond thenExpr elseExpr _ =>
      let elseLbl ← freshLabel "tern_else"
      let endLbl ← freshLabel "tern_end"
      emitExpr env cond
      emitInstr (.cmp (.imm 0) (.reg .rax))
      emitInstr (.je elseLbl)
      emitExpr env thenExpr
      emitInstr (.jmp endLbl)
      emitInstr (.label_ elseLbl)
      emitExpr env elseExpr
      emitInstr (.label_ endLbl)
  | .cast _ operand _ =>
      -- For integer casts, just evaluate the operand (same register)
      emitExpr env operand
  | .comma left right _ =>
      emitExpr env left  -- discard result
      emitExpr env right
  | .initList elems _ =>
      -- Emit each element; result is last element
      match elems with
      | [] => emitInstr (.mov (.imm 0) (.reg .rax))
      | _ =>
        for e in elems do
          emitExpr env e
  | .callFnPtr fnExpr args _ =>
      -- Push args, evaluate fn pointer, call indirect
      for arg in args.reverse do
        emitExpr env arg
        emitInstr (.push (.reg .rax))
      let pairs := List.zip args argRegs
      for pair in pairs do
        let (_, reg) := pair
        emitInstr (.pop (.reg reg))
      emitExpr env fnExpr
      emitInstr (.push (.reg .rax))
      -- rax now has fn pointer — but we need to preserve it across arg setup
      -- Simplified: call *%rax
      emitInstr (.pop (.reg .r11))
      emitInstr (.call "*%r11")
  | .nullLit _ => emitInstr (.mov (.imm 0) (.reg .rax))
  | .floatLit _ _ =>
      -- Float not supported in x86 integer pipeline; emit 0 as placeholder
      emitInstr (.mov (.imm 0) (.reg .rax))

end


def runExprCodegen
    (structDefs : List StructDef)
    (locals : List (String × Int))
    (env : TypeEnv)
    (expr : Expr) : Except String (List Instr) := do
  let init : CodegenState := {
    localOffsets := locals
    structDefs := structDefs
    typedefs := []
    nextOffset := 0
    labelCounter := 0
    currentFn := "_expr"
    instrs := []
    dataSection := []
    loopStack := []
  }
  let (_, st) <- (emitExpr env expr).run init
  pure st.instrs


mutual

partial def collectVarDeclsStmt (stmt : Stmt) : List (String × CType) :=
  match stmt with
  | .varDecl name ty _ _ => [(name, ty)]
  | .exprStmt _ _ => []
  | .ret _ _ => []
  | .ifElse _ thenBody elseBody _ =>
      collectVarDecls thenBody ++ collectVarDecls elseBody
  | .while_ _ body _ =>
      collectVarDecls body
  | .for_ init _ _ body _ =>
      let initVars := match init with
        | none => []
        | some s => collectVarDeclsStmt s
      initVars ++ collectVarDecls body
  | .block stmts _ =>
      collectVarDecls stmts
  -- Phase 2 Stmt
  | .switch_ _ cases _ =>
      (cases.map (fun (_, body, _) => collectVarDecls body)).flatten
  | .doWhile body _ _ => collectVarDecls body
  | .break_ _ | .continue_ _ | .emptyStmt _ => []
  | .goto_ _ _ => []
  | .label_ _ body _ => collectVarDeclsStmt body


partial def collectVarDecls (stmts : List Stmt) : List (String × CType) :=
  match stmts with
  | [] => []
  | s :: rest => collectVarDeclsStmt s ++ collectVarDecls rest

end


def roundUp8 (n : Nat) : Nat :=
  if n % 8 = 0 then n else n + (8 - (n % 8))

def roundUp16 (n : Nat) : Nat :=
  if n % 16 = 0 then n else n + (16 - (n % 16))

/-- Allocate stack slots based on actual type sizes. Each slot gets
    max(8, roundUp8(cTypeSize ty)) bytes — minimum 8 for register-width stores.
    The returned offset points to the LOWEST address of the slot, so that
    `lea offset(%rbp), %rax` gives the struct base and fields extend upward
    within the allocated region (not above %rbp into the caller's frame). -/
def assignOffsets (defs : List StructDef) (bindings : List (String × CType))
    (nextFree : Int := 0) : List (String × Int) :=
  match bindings with
  | [] => []
  | (name, ty) :: rest =>
      let slotSize := max 8 (roundUp8 (cTypeSize defs ty))
      let offset := nextFree - Int.ofNat slotSize
      (name, offset) :: assignOffsets defs rest offset


mutual

partial def emitStmt (env : TypeEnv) (retLabel : LabelId) (stmt : Stmt) : CodegenM Unit := do
  match stmt with
  | .varDecl name ty init _ =>
      match init with
      | none => pure ()
      | some e =>
          emitExpr env e
          let st <- get
          match lookupOffset st.localOffsets name with
          | none => throw s!"missing stack slot for variable '{name}'"
          | some off =>
              let sz := cTypeSize st.structDefs ty
              if sz = 1 then
                emitInstr (.movb (.reg .al) (.mem .rbp off))
              else if sz = 4 then
                emitInstr (.movl (.reg .eax) (.mem .rbp off))
              else
                emitInstr (.mov (.reg .rax) (.mem .rbp off))
  | .exprStmt e _ =>
      emitExpr env e
  | .ret val _ =>
      match val with
      | none => emitInstr (.mov (.imm 0) (.reg .rax))
      | some e => emitExpr env e
      emitInstr (.jmp retLabel)
  | .ifElse cond thenBody elseBody _ =>
      let elseLbl <- freshLabel "if_else"
      let endLbl <- freshLabel "if_end"
      emitExpr env cond
      emitInstr (.cmp (.imm 0) (.reg .rax))
      emitInstr (.je elseLbl)
      emitStmts env retLabel thenBody
      emitInstr (.jmp endLbl)
      emitInstr (.label_ elseLbl)
      emitStmts env retLabel elseBody
      emitInstr (.label_ endLbl)
  | .while_ cond body _ =>
      let loopLbl <- freshLabel "while_loop"
      let endLbl <- freshLabel "while_end"
      modify fun st => { st with loopStack := ⟨endLbl, some loopLbl⟩ :: st.loopStack }
      emitInstr (.label_ loopLbl)
      emitExpr env cond
      emitInstr (.cmp (.imm 0) (.reg .rax))
      emitInstr (.je endLbl)
      emitStmts env retLabel body
      emitInstr (.jmp loopLbl)
      emitInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .for_ init cond step body _ =>
      match init with
      | none => pure ()
      | some initStmt => emitStmt env retLabel initStmt
      let loopLbl <- freshLabel "for_loop"
      let stepLbl <- freshLabel "for_step"
      let endLbl <- freshLabel "for_end"
      modify fun st => { st with loopStack := ⟨endLbl, some stepLbl⟩ :: st.loopStack }
      emitInstr (.label_ loopLbl)
      match cond with
      | none => pure ()
      | some condExpr =>
          emitExpr env condExpr
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.je endLbl)
      emitStmts env retLabel body
      emitInstr (.label_ stepLbl)
      match step with
      | none => pure ()
      | some stepExpr =>
          emitExpr env stepExpr
      emitInstr (.jmp loopLbl)
      emitInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .block stmts _ =>
      emitStmts env retLabel stmts
  -- Phase 2 Stmt
  | .switch_ scrutinee cases _ =>
      let endLbl ← freshLabel "switch_end"
      modify fun st => { st with loopStack := ⟨endLbl, none⟩ :: st.loopStack }
      -- Evaluate scrutinee once
      emitExpr env scrutinee
      emitInstr (.push (.reg .rax))
      -- Generate jump table: compare against each case value
      let mut caseLbls : List (Option Int × LabelId) := []
      let mut defaultLbl : Option LabelId := none
      for c in cases do
        let (val, _, _) := c
        let lbl ← freshLabel "case"
        caseLbls := caseLbls ++ [(val, lbl)]
        match val with
        | none => defaultLbl := some lbl
        | _ => pure ()
      -- Emit comparisons
      for (val, lbl) in caseLbls do
        match val with
        | some v =>
            emitInstr (.mov (.mem .rsp 0) (.reg .rax))
            emitInstr (.cmp (.imm v) (.reg .rax))
            emitInstr (.je lbl)
        | none => pure ()
      -- Jump to default or end
      match defaultLbl with
      | some dl => emitInstr (.jmp dl)
      | none => emitInstr (.jmp endLbl)
      -- Pop scrutinee
      emitInstr (.pop (.reg .rax))
      -- Emit case bodies
      let casePairs := List.zip cases caseLbls
      for ((_, body, _), (_, lbl)) in casePairs do
        emitInstr (.label_ lbl)
        emitStmts env retLabel body
      emitInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .doWhile body cond _ =>
      let loopLbl ← freshLabel "do_loop"
      let endLbl ← freshLabel "do_end"
      modify fun st => { st with loopStack := ⟨endLbl, some loopLbl⟩ :: st.loopStack }
      emitInstr (.label_ loopLbl)
      emitStmts env retLabel body
      emitExpr env cond
      emitInstr (.cmp (.imm 0) (.reg .rax))
      emitInstr (.jne loopLbl)
      emitInstr (.label_ endLbl)
      modify fun st => { st with loopStack := st.loopStack.drop 1 }
  | .break_ _ => do
      let st ← get
      match st.loopStack with
      | ctx :: _ => emitInstr (.jmp ctx.breakLabel)
      | [] => emitInstr (.comment "break: no enclosing loop")
  | .continue_ _ => do
      let st ← get
      match st.loopStack with
      | ctx :: _ =>
          match ctx.continueLabel with
          | some lbl => emitInstr (.jmp lbl)
          | none => emitInstr (.comment "continue: in switch, no target")
      | [] => emitInstr (.comment "continue: no enclosing loop")
  | .goto_ label _ =>
      let lbl : LabelId := { fn := "", kind := label, idx := 0 }
      emitInstr (.jmp lbl)
  | .label_ name body _ =>
      let lbl : LabelId := { fn := "", kind := name, idx := 0 }
      emitInstr (.label_ lbl)
      emitStmt env retLabel body
  | .emptyStmt _ => pure ()


partial def emitStmts (env : TypeEnv) (retLabel : LabelId) (stmts : List Stmt) : CodegenM Unit := do
  match stmts with
  | [] => pure ()
  | stmt :: rest =>
      emitStmt env retLabel stmt
      emitStmts env retLabel rest

end


def emitParamMoves (params : List Param) (offsets : List (String × Int)) : CodegenM Unit := do
  let pairs := List.zip params argRegs
  for pair in pairs do
    let (param, reg) := pair
    match lookupOffset offsets param.name with
    | none => throw s!"missing stack slot for parameter '{param.name}'"
    | some off =>
        emitInstr (.mov (.reg reg) (.mem .rbp off))


def emitFunction (structDefs : List StructDef) (typedefs : List TypedefDecl) (fn : FunDef) : Except String (AsmFunction × List String) := do
  let paramBindings : TypeEnv := fn.params.map (fun p => (p.name, p.ty))
  let localBindings : TypeEnv := collectVarDecls fn.body
  let allBindings : TypeEnv := paramBindings ++ localBindings
  let offsets := assignOffsets structDefs allBindings
  -- Frame size = distance from rbp to the lowest allocated offset
  let frameSize : Nat := match offsets.getLast? with
    | some (_, lastOff) => roundUp16 (Int.natAbs lastOff)
    | none => 0
  let initialState : CodegenState := {
    localOffsets := offsets
    structDefs := structDefs
    typedefs := typedefs
    nextOffset := -(Int.ofNat (frameSize + 8))
    labelCounter := 0
    currentFn := fn.name
    instrs := []
    dataSection := []
    loopStack := []
  }
  let env : TypeEnv := allBindings
  -- retLabel uses a distinct kind "ret", so no idx collision with freshLabel outputs
  let retLabel : LabelId := { fn := fn.name, kind := "ret", idx := 0 }
  let codegen : CodegenM Unit := do
    emitInstr (.push (.reg .rbp))
    emitInstr (.mov (.reg .rsp) (.reg .rbp))
    if frameSize > 0 then
      emitInstr (.sub (.imm (Int.ofNat frameSize)) (.reg .rsp))
    emitParamMoves fn.params offsets
    emitStmts env retLabel fn.body
    if fn.ret == .void then
      pure ()
    else
      emitInstr (.mov (.imm 0) (.reg .rax))
    emitInstr (.label_ retLabel)
    emitInstr (.mov (.reg .rbp) (.reg .rsp))
    emitInstr (.pop (.reg .rbp))
    emitInstr .ret
  let (_, finalState) <- codegen.run initialState
  pure ({ name := fn.name, instrs := finalState.instrs }, finalState.dataSection)


partial def emitFunctions (structDefs : List StructDef) (typedefs : List TypedefDecl) (fns : List FunDef)
    : Except String (List AsmFunction × List String) := do
  match fns with
  | [] => pure ([], [])
  | fn :: rest =>
      let (asmFn, dataLines) <- emitFunction structDefs typedefs fn
      let (asmRest, dataRest) <- emitFunctions structDefs typedefs rest
      pure (asmFn :: asmRest, dataLines ++ dataRest)


def emitProgramImpl (prog : CCC.Syntax.Program) : Except String String := do
  let (functions, dataLines) <- emitFunctions prog.structs prog.typedefs prog.functions
  let asm : AsmProgram := {
    functions := functions
    dataSection := dataLines
  }
  pure (emitAsm asm)

end CCC.Emit
