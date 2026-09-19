/-
  CCC/Syntax/Layout.lean — C ABI struct layout (size, alignment, field
  offsets) shared by the emitters.

  FEL-68 (emitter completeness): `CCC/Emit/EmitX86.lean`'s `cTypeSize`
  (used by BOTH the x86-64 and AArch64 emitters — the latter imports the
  former for exactly this, plus `TypeEnv`/`LoopCtx`) summed field sizes
  with no alignment padding at all, so `struct P { char c; int x; long y; }`
  sized as 13 bytes with fields at offsets 0/1/5, instead of the real
  System V AMD64 / AAPCS64 layout: 16 bytes, offsets 0/4/8. This was
  internally consistent for a CCC-to-CCC-compiled program (nothing else
  read the layout), but breaks the moment such a struct's memory is shared
  with real C code — a linked library, the C standard library, anything
  compiled by `cc` — which is exactly the scenario FEL-65's
  whole-library-verification goal requires. This module implements the
  standard "align each field to its own alignment, round the final size up
  to the struct's own (max-field) alignment" layout algorithm, used by the
  emitters for BOTH `sizeof` and field-offset computation so the two can
  never disagree with each other (which would itself be a memory-safety
  bug: a `p->field` write landing somewhere other than where `sizeof`
  said the object ends).

  Deliberately NOT wired into the VERIFIER's separate, still-unpadded
  `CCC/Verify/TypeSize.lean:sizeOfType` in this pass — that function only
  feeds static analysis (e.g. bounding a `malloc(sizeof(struct X))`` call
  against later accesses), where computing too SMALL a size is the safe
  direction (more conservative, not unsound — it can only cause a false
  positive, never miss a real overflow). Unifying the two is tracked
  separately; see FEL-68 in the project tracker.

  Union sizing is intentionally still a TODO here (returns 0, same as
  before this module existed): computing it correctly needs `List
  UnionDef` threaded through, which none of `cTypeSize`'s current callers
  pass — a separate, larger signature change out of scope for this pass.
-/

import CCC.Syntax.AST

namespace CCC.Syntax.Layout

private def findStruct (defs : List StructDef) (name : String) : Option StructDef :=
  defs.find? (·.name == name)

/-- Alignment of a type in bytes. System V AMD64 and AAPCS64 agree on the
    "align to own size, capped at 8" rule for every scalar type CCC
    supports, so one table serves both backends. A struct's alignment is
    the max of its fields' (a struct is never LESS aligned than its most
    demanding field, or the field after it in an array of such structs
    could itself end up misaligned). -/
partial def alignOf (defs : List StructDef) : CType → Nat
  | .void => 1
  | .bool | .char => 1
  | .short => 2
  | .int | .float_ | .enum_ _ => 4
  | .long | .longLong | .double_ | .pointer _ | .sizeT | .funcPtr _ _ => 8
  | .unsigned inner | .signed inner | .const_ inner | .volatile_ inner | .restrict_ inner =>
      alignOf defs inner
  | .array elem _ => alignOf defs elem
  | .struct_ name =>
      match findStruct defs name with
      | some s => s.fields.foldl (fun acc (_, fty) => Nat.max acc (alignOf defs fty)) 1
      | none => 1
  | .union_ _ => 8       -- TODO: needs List UnionDef; see module docstring
  | .typedef_ _ => 8     -- fallback; callers should resolve typedefs first

/-- Round `n` up to the next multiple of `align` (a no-op if already
    aligned, or if `align = 0`). -/
def roundUpTo (n align : Nat) : Nat :=
  if align == 0 then n
  else
    let r := n % align
    if r == 0 then n else n + (align - r)

mutual

/-- Byte size of a type, INCLUDING struct padding. This is what callers
    should use wherever the old unpadded `cTypeSize` was used before. -/
partial def sizeOf (defs : List StructDef) : CType → Nat
  | .void => 0
  | .int => 4
  | .char => 1
  | .long => 8
  | .bool => 1
  | .unsigned inner => sizeOf defs inner
  | .pointer _ => 8
  | .array elem n => n * sizeOf defs elem
  | .struct_ name =>
      match findStruct defs name with
      | none => 0
      | some s => paddedStructSize defs s.fields
  | .sizeT => 8
  | .float_ => 4
  | .double_ => 8
  | .short => 2
  | .longLong => 8
  | .signed inner => sizeOf defs inner
  | .enum_ _ => 4
  | .union_ _ => 0        -- TODO: needs List UnionDef; see module docstring
  | .funcPtr _ _ => 8
  | .typedef_ _ => 8      -- fallback; callers should resolve typedefs first
  | .const_ inner => sizeOf defs inner
  | .volatile_ inner => sizeOf defs inner
  | .restrict_ inner => sizeOf defs inner

/-- Total padded size of a struct with the given fields, in DECLARATION
    order: each field starts at the next multiple of its own alignment
    (inserting padding before it if needed), and the whole struct's size
    is rounded up to its max field alignment (trailing padding, so an
    array of this struct keeps every element aligned too). -/
partial def paddedStructSize (defs : List StructDef) (fields : List (String × CType)) : Nat :=
  let (offset, maxAlign) := fields.foldl (fun (off, mxa) (_, fty) =>
    let fa := alignOf defs fty
    let paddedOff := roundUpTo off fa
    (paddedOff + sizeOf defs fty, Nat.max mxa fa)) (0, 1)
  roundUpTo offset maxAlign

end

/-- Byte offset of `target` within a struct with the given fields
    (declaration order), using the same per-field alignment
    `paddedStructSize` uses above — so a field's offset and the struct's
    total size are always computed by the same rule and can never
    disagree with each other. `none` if the field isn't present. -/
partial def fieldOffset (defs : List StructDef) (fields : List (String × CType))
    (target : String) : Option Nat :=
  let rec go (remaining : List (String × CType)) (offset : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | (name, fty) :: rest =>
        let fa := alignOf defs fty
        let paddedOff := roundUpTo offset fa
        if name == target then some paddedOff
        else go rest (paddedOff + sizeOf defs fty)
  go fields 0

/-- Byte offsets for a list of VALUES passed in order (e.g. the 9th+
    arguments of a call, passed on the stack), each packed at its own
    natural alignment — NOT padded to a uniform 8-byte slot each. This is
    Apple's arm64 ABI's documented deviation from the base AAPCS64 spec
    (which pads every stack argument to 8 bytes): "Writing ARM64 Code for
    Apple Platforms" specifies that stack-passed arguments are packed as
    tightly as their own alignment allows, the same rule
    `paddedStructSize`/`fieldOffset` already implement for struct fields
    — in fact it's the identical algorithm, just over a plain list of
    types with no field names needed. Confirmed empirically: two `int`
    (4-byte) stack arguments must land 4 bytes apart, not 8 — passing
    them 8 bytes apart (this module's first version) interoperated fine
    between two CCC-compiled ends (self-consistently wrong) but silently
    passed the wrong value to/from a real `cc`-compiled function on
    either side of the call.

    Returns `(perArgOffset, totalPackedSize)`; callers round
    `totalPackedSize` up to 16 separately when using it to size a stack
    reservation (sp must stay 16-aligned at a call, but that is a
    property of the RESERVATION, not of where each argument sits inside
    it). -/
def packedOffsets (defs : List StructDef) (types : List CType) : List Nat × Nat :=
  let (offsetsRev, offset, maxAlign) := types.foldl
    (fun (accOffsets, off, mxa) ty =>
      let fa := alignOf defs ty
      let paddedOff := roundUpTo off fa
      (paddedOff :: accOffsets, paddedOff + sizeOf defs ty, Nat.max mxa fa))
    ([], 0, 1)
  (offsetsRev.reverse, roundUpTo offset maxAlign)

end CCC.Syntax.Layout
