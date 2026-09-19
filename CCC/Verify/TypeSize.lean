import CCC.Verify.FlowState

namespace CCC.Verify

/-- Resolve a struct definition by name. -/
def findStruct (ctx : VerifyCtx) (name : String) : Option Syntax.StructDef :=
  ctx.structs.find? (·.name == name)

/-- Resolve a struct field type. -/
def findStructFieldType (ctx : VerifyCtx) (structName : String) (field : String)
    : Option Syntax.CType :=
  match findStruct ctx structName with
  | some sd => (sd.fields.find? (·.1 == field)).map (·.2)
  | none => none

/-- Compute byte size of a type (64-bit ABI assumptions). -/
partial def sizeOfType (ctx : VerifyCtx) (ty : Syntax.CType) : Option Nat :=
  match ty with
  | .void => some 0
  | .int => some 4
  | .char => some 1
  | .long => some 8
  | .bool => some 4
  | .sizeT => some 8
  | .pointer _ => some 8
  | .unsigned inner => sizeOfType ctx inner
  | .array elem n => (sizeOfType ctx elem).map (fun s => s * n)
  | .struct_ name =>
      match findStruct ctx name with
      | some sd =>
          sd.fields.foldlM (init := 0)
            (fun acc fieldPair =>
              match sizeOfType ctx fieldPair.2 with
              | some fieldSize => some (acc + fieldSize)
              | none => none)
      | none => none
  -- Phase 2 types
  | .float_ => some 4
  | .double_ => some 8
  | .short => some 2
  | .longLong => some 8
  | .signed inner => sizeOfType ctx inner
  | .enum_ _ => some 4               -- enums are int-sized
  | .union_ _ => some 0              -- TODO: look up union def, return max field size
  | .funcPtr _ _ => some 8           -- function pointers are pointer-sized
  | .typedef_ _ => none              -- unresolved typedef — can't compute
  | .const_ inner => sizeOfType ctx inner
  | .volatile_ inner => sizeOfType ctx inner
  | .restrict_ inner => sizeOfType ctx inner

/-- Find a declared/static type for a local variable named `name` in a
    statement list: recurses into every nested-statement position (both
    branches of `if`, loop bodies, blocks, switch cases, labels). No VLAs
    are supported by this compiler, so a local array's DECLARED size is
    always its real one -- this is exact, not an approximation. -/
private partial def findVarDeclType (name : String) (stmts : List Syntax.Stmt)
    : Option Syntax.CType :=
  match stmts with
  | [] => none
  | s :: rest =>
      let hereOpt : Option Syntax.CType :=
        match s with
        | .varDecl n ty _ _ => if n == name then some ty else none
        | .ifElse _ t e _ =>
            match findVarDeclType name t with
            | some ty => some ty
            | none => findVarDeclType name e
        | .while_ _ b _ => findVarDeclType name b
        | .for_ initOpt _ _ b _ =>
            match initOpt with
            | some i =>
                match findVarDeclType name [i] with
                | some ty => some ty
                | none => findVarDeclType name b
            | none => findVarDeclType name b
        | .block b _ => findVarDeclType name b
        | .switch_ _ cases _ =>
            cases.foldl (init := none) (fun acc (_, body, _) =>
              match acc with
              | some ty => some ty
              | none => findVarDeclType name body)
        | .doWhile b _ _ => findVarDeclType name b
        | .label_ _ body _ => findVarDeclType name [body]
        | _ => none
      match hereOpt with
      | some ty => some ty
      | none => findVarDeclType name rest

/-- Declared type of a local variable (parameter or `varDecl`) in the
    CURRENT function, per `ctx.currentFun`/`ctx.program`. Used only to
    resolve `sizeof(localVar)` (see `.sizeOfExpr` below) -- deliberately
    narrow: a bare variable name is by far the common real-world shape
    (`malloc(sizeof(buf))`), and reaching for the general case (a field
    access, a dereference, ...) would need the same live `exprType?` this
    file is imported BY (`BoundsCheck.lean`), which would be a circular
    import from here. -/
private def declaredTypeOfLocal? (ctx : VerifyCtx) (name : String) : Option Syntax.CType :=
  match ctx.program.functions.find? (·.name == ctx.currentFun) with
  | none => none
  | some fn =>
      match fn.params.find? (·.name == name) with
      | some p => some p.ty
      | none => findVarDeclType name fn.body

/-- Resolve a compile-time signed-integer expression. Like `resolveExprNat`
    but keeps the sign, so `-5`, `w - h`, and unary negation resolve
    correctly instead of collapsing to `none`. Used by the range/bounds
    analysis to compute literal shift deltas and initial point ranges. -/
partial def resolveExprInt (ctx : VerifyCtx) (expr : Syntax.Expr) : Option Int :=
  match expr with
  | .intLit v _ => some v
  | .charLit c _ => some (Int.ofNat c.toNat)
  | .sizeOf ty _ => (sizeOfType ctx ty).map Int.ofNat
  -- FEL-49 item 5 correction: `sizeof(localVar)` (as opposed to
  -- `sizeof(type)`, the `.sizeOf` case above) used to be unresolvable
  -- here at all -- `malloc(sizeof(buf))` then had an UNKNOWN capacity,
  -- silently skipping bounds-checking on every access through the
  -- result, exactly the "unknown size -> silent pass" shape FEL-45 fixed
  -- for memcpy-family sinks. See `declaredTypeOfLocal?`'s docstring for
  -- why only a bare variable operand is handled.
  | .sizeOfExpr (.var name _) _ =>
      (declaredTypeOfLocal? ctx name).bind (fun ty => (sizeOfType ctx ty).map Int.ofNat)
  | .sizeOfExpr _ _ => none
  | .unOp .neg operand _ => (resolveExprInt ctx operand).map (fun v => -v)
  | .binOp op lhs rhs _ =>
      match resolveExprInt ctx lhs, resolveExprInt ctx rhs with
      | some a, some b =>
          match op with
          | .add => some (a + b)
          | .sub => some (a - b)
          | .mul => some (a * b)
          | .div => if b = 0 then none else some (a / b)
          | .mod => if b = 0 then none else some (a % b)
          | _ => none
      | _, _ => none
  | .cast _ operand _ => resolveExprInt ctx operand
  | _ => none

/-- Resolve a compile-time natural-number expression (for sizes/lengths). -/
partial def resolveExprNat (ctx : VerifyCtx) (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .intLit v _ =>
      if v < 0 then none else some v.toNat
  | .sizeOf ty _ => sizeOfType ctx ty
  | .sizeOfExpr (.var name _) _ => (declaredTypeOfLocal? ctx name).bind (sizeOfType ctx)
  | .sizeOfExpr _ _ => none
  | .binOp op lhs rhs _ =>
      match resolveExprNat ctx lhs, resolveExprNat ctx rhs with
      | some a, some b =>
          match op with
          | .add => some (a + b)
          | .sub => if a ≥ b then some (a - b) else none
          | .mul => some (a * b)
          | .div => if b = 0 then none else some (a / b)
          | .mod => if b = 0 then none else some (a % b)
          | _ => none
      | _, _ => none
  | _ => none

/-- Alias used by bounds checking for `sizeof(...)`-style expressions. -/
def resolveExprSize (ctx : VerifyCtx) (expr : Syntax.Expr) : Option Nat :=
  resolveExprNat ctx expr

/-- Alignment of a type in bytes (System V AMD64 ABI). -/
partial def alignOfType (ctx : VerifyCtx) (ty : Syntax.CType) : Nat :=
  match ty with
  | .void => 1
  | .bool | .char => 1
  | .short => 2
  | .int | .float_ | .enum_ _ => 4
  | .long | .longLong | .double_ | .pointer _ | .sizeT | .funcPtr _ _ => 8
  | .unsigned inner | .signed inner | .const_ inner | .volatile_ inner | .restrict_ inner =>
      alignOfType ctx inner
  | .array elem _ => alignOfType ctx elem
  | .struct_ name =>
      match findStruct ctx name with
      | some sd => sd.fields.foldl (fun acc (_, fty) => Nat.max acc (alignOfType ctx fty)) 1
      | none => 1
  | .union_ _ => 8  -- TODO: compute from fields
  | .typedef_ _ => 8

/-- Round up n to the next multiple of align. -/
def roundUpTo (n : Nat) (align : Nat) : Nat :=
  if align == 0 then n
  else
    let r := n % align
    if r == 0 then n else n + (align - r)

/-- Compute padded struct size (with alignment padding). -/
partial def paddedStructSize (ctx : VerifyCtx) (fields : List (String × Syntax.CType)) : Nat :=
  let (offset, maxAlign) := fields.foldl (fun (off, mxa) (_, fty) =>
    let fa := alignOfType ctx fty
    let paddedOff := roundUpTo off fa
    let fs := match sizeOfType ctx fty with | some s => s | none => 0
    (paddedOff + fs, Nat.max mxa fa)) (0, 1)
  roundUpTo offset maxAlign

/-- Compute padded field offset within a struct. -/
partial def paddedFieldOffset (ctx : VerifyCtx) (fields : List (String × Syntax.CType))
    (target : String) : Option Nat :=
  let rec go (remaining : List (String × Syntax.CType)) (offset : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | (name, fty) :: rest =>
        let fa := alignOfType ctx fty
        let paddedOff := roundUpTo offset fa
        if name == target then some paddedOff
        else
          let fs := match sizeOfType ctx fty with | some s => s | none => 0
          go rest (paddedOff + fs)
  go fields 0

end CCC.Verify
