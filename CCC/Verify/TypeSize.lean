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

end CCC.Verify
