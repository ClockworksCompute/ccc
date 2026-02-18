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

/-- Resolve a compile-time natural-number expression (for sizes/lengths). -/
partial def resolveExprNat (ctx : VerifyCtx) (expr : Syntax.Expr) : Option Nat :=
  match expr with
  | .intLit v _ =>
      if v < 0 then none else some v.toNat
  | .sizeOf ty _ => sizeOfType ctx ty
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
