import CCC.Syntax.AST
import CCC.Emit.X86
import CCC.Emit.Runtime

namespace CCC.Emit

open CCC.Syntax

structure CodegenState where
  localOffsets : List (String × Int)
  structDefs   : List CCC.Syntax.StructDef
  nextOffset   : Int
  labelCounter : Nat
  currentFn    : String
  instrs       : List Instr

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
      | .neg => .long
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
      let objTy := inferExprType env st.structDefs obj
      let structNameOpt := match objTy with
        | .struct_ sname => some sname
        | _ => none
      match structNameOpt with
      | none => throw "member access on non-struct value"
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
      let ptrTy := inferExprType env st.structDefs ptr
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
      | _ => throw "arrow access on non-pointer-to-struct"
  | _ => throw "expression is not assignable"


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
  | .index arr idx loc =>
      let _ <- emitLValueAddr env (.index arr idx loc)
      let st <- get
      let valTy := inferExprType env st.structDefs (.index arr idx loc)
      emitLoadFromAddr valTy
  | .member obj field loc =>
      let _ <- emitLValueAddr env (.member obj field loc)
      let st <- get
      let valTy := inferExprType env st.structDefs (.member obj field loc)
      match valTy with
      | .array _ _ => pure ()  -- array decays to pointer; address already in %rax
      | _ => emitLoadFromAddr valTy
  | .arrow ptr field loc =>
      let _ <- emitLValueAddr env (.arrow ptr field loc)
      let st <- get
      let valTy := inferExprType env st.structDefs (.arrow ptr field loc)
      match valTy with
      | .array _ _ => pure ()  -- array decays to pointer; address already in %rax
      | _ => emitLoadFromAddr valTy
  | .call fn args _ =>
      emitCall env fn args
  | .sizeOf ty _ =>
      let st <- get
      emitInstr (.mov (.imm (Int.ofNat (cTypeSize st.structDefs ty))) (.reg .rax))
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

end


def runExprCodegen
    (structDefs : List StructDef)
    (locals : List (String × Int))
    (env : TypeEnv)
    (expr : Expr) : Except String (List Instr) := do
  let init : CodegenState := {
    localOffsets := locals
    structDefs := structDefs
    nextOffset := 0
    labelCounter := 0
    currentFn := "_expr"
    instrs := []
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
      emitInstr (.label_ loopLbl)
      emitExpr env cond
      emitInstr (.cmp (.imm 0) (.reg .rax))
      emitInstr (.je endLbl)
      emitStmts env retLabel body
      emitInstr (.jmp loopLbl)
      emitInstr (.label_ endLbl)
  | .for_ init cond step body _ =>
      match init with
      | none => pure ()
      | some initStmt => emitStmt env retLabel initStmt
      let loopLbl <- freshLabel "for_loop"
      let endLbl <- freshLabel "for_end"
      emitInstr (.label_ loopLbl)
      match cond with
      | none => pure ()
      | some condExpr =>
          emitExpr env condExpr
          emitInstr (.cmp (.imm 0) (.reg .rax))
          emitInstr (.je endLbl)
      emitStmts env retLabel body
      match step with
      | none => pure ()
      | some stepExpr =>
          emitExpr env stepExpr
      emitInstr (.jmp loopLbl)
      emitInstr (.label_ endLbl)
  | .block stmts _ =>
      emitStmts env retLabel stmts


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


def emitFunction (structDefs : List StructDef) (fn : FunDef) : Except String AsmFunction := do
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
    nextOffset := -(Int.ofNat (frameSize + 8))
    labelCounter := 0
    currentFn := fn.name
    instrs := []
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
    if fn.ret = .void then
      pure ()
    else
      emitInstr (.mov (.imm 0) (.reg .rax))
    emitInstr (.label_ retLabel)
    emitInstr (.mov (.reg .rbp) (.reg .rsp))
    emitInstr (.pop (.reg .rbp))
    emitInstr .ret
  let (_, finalState) <- codegen.run initialState
  pure { name := fn.name, instrs := finalState.instrs }


partial def emitFunctions (structDefs : List StructDef) (fns : List FunDef)
    : Except String (List AsmFunction) := do
  match fns with
  | [] => pure []
  | fn :: rest =>
      let asmFn <- emitFunction structDefs fn
      let asmRest <- emitFunctions structDefs rest
      pure (asmFn :: asmRest)


def emitProgramImpl (prog : CCC.Syntax.Program) : Except String String := do
  let functions <- emitFunctions prog.structs prog.functions
  let asm : AsmProgram := {
    functions := functions
    dataSection := []
  }
  pure (emitAsm asm)

end CCC.Emit
