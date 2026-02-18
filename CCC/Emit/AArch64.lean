/-
  CCC/Emit/AArch64.lean — AArch64 instruction types and assembly rendering

  Targets macOS (Mach-O): underscore-prefixed globals, .p2align, Apple sections.
  Uses GNU-style assembly syntax compatible with `as` on macOS.
-/

namespace CCC.Emit

/-- AArch64 general-purpose registers (64-bit: x0-x30, sp; 32-bit: w0-w30, wsp) -/
inductive ArmReg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  | sp   -- stack pointer
  | xzr  -- zero register
  deriving Repr, BEq, Inhabited

/-- Render register as 64-bit name -/
def ArmReg.toStr64 : ArmReg → String
  | .x0 => "x0"   | .x1 => "x1"   | .x2 => "x2"   | .x3 => "x3"
  | .x4 => "x4"   | .x5 => "x5"   | .x6 => "x6"   | .x7 => "x7"
  | .x8 => "x8"   | .x9 => "x9"   | .x10 => "x10" | .x11 => "x11"
  | .x12 => "x12" | .x13 => "x13" | .x14 => "x14" | .x15 => "x15"
  | .x16 => "x16" | .x17 => "x17" | .x18 => "x18" | .x19 => "x19"
  | .x20 => "x20" | .x21 => "x21" | .x22 => "x22" | .x23 => "x23"
  | .x24 => "x24" | .x25 => "x25" | .x26 => "x26" | .x27 => "x27"
  | .x28 => "x28" | .x29 => "x29" | .x30 => "x30"
  | .sp  => "sp"   | .xzr => "xzr"

/-- Render register as 32-bit name -/
def ArmReg.toStr32 : ArmReg → String
  | .x0 => "w0"   | .x1 => "w1"   | .x2 => "w2"   | .x3 => "w3"
  | .x4 => "w4"   | .x5 => "w5"   | .x6 => "w6"   | .x7 => "w7"
  | .x8 => "w8"   | .x9 => "w9"   | .x10 => "w10" | .x11 => "w11"
  | .x12 => "w12" | .x13 => "w13" | .x14 => "w14" | .x15 => "w15"
  | .x16 => "w16" | .x17 => "w17" | .x18 => "w18" | .x19 => "w19"
  | .x20 => "w20" | .x21 => "w21" | .x22 => "w22" | .x23 => "w23"
  | .x24 => "w24" | .x25 => "w25" | .x26 => "w26" | .x27 => "w27"
  | .x28 => "w28" | .x29 => "w29" | .x30 => "w30"
  | .sp  => "wsp"  | .xzr => "wzr"

/-- AArch64 label -/
structure ArmLabel where
  fn   : String
  kind : String
  idx  : Nat
  deriving Repr, BEq, Inhabited

def ArmLabel.render (l : ArmLabel) : String :=
  s!".L_{l.fn}_{l.kind}_{l.idx}"

/-- AArch64 instruction set (subset sufficient for C codegen) -/
inductive ArmInstr where
  -- Data movement
  | mov_imm (rd : ArmReg) (imm : Int)              -- mov rd, #imm
  | mov_reg (rd : ArmReg) (rs : ArmReg)             -- mov rd, rs
  | movk (rd : ArmReg) (imm : Nat) (shift : Nat)    -- movk rd, #imm, lsl #shift
  -- Load/store
  | ldr (rt : ArmReg) (rn : ArmReg) (off : Int)     -- ldr rt, [rn, #off]
  | ldr_w (rt : ArmReg) (rn : ArmReg) (off : Int)   -- ldr wt, [rn, #off] (32-bit)
  | ldrb (rt : ArmReg) (rn : ArmReg) (off : Int)    -- ldrb wt, [rn, #off] (byte)
  | str (rt : ArmReg) (rn : ArmReg) (off : Int)     -- str rt, [rn, #off]
  | str_w (rt : ArmReg) (rn : ArmReg) (off : Int)   -- str wt, [rn, #off] (32-bit)
  | strb (rt : ArmReg) (rn : ArmReg) (off : Int)    -- strb wt, [rn, #off] (byte)
  | stp (rt1 : ArmReg) (rt2 : ArmReg) (rn : ArmReg) (off : Int)  -- stp, pre-index
  | ldp (rt1 : ArmReg) (rt2 : ArmReg) (rn : ArmReg) (off : Int)  -- ldp, post-index
  -- Address computation
  | adrp (rd : ArmReg) (sym : String)               -- adrp rd, sym@PAGE
  | add_sym (rd : ArmReg) (rn : ArmReg) (sym : String) -- add rd, rn, sym@PAGEOFF
  -- Arithmetic
  | add_imm (rd : ArmReg) (rn : ArmReg) (imm : Int)
  | add_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | sub_imm (rd : ArmReg) (rn : ArmReg) (imm : Int)
  | sub_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | mul_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | sdiv (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | msub (rd : ArmReg) (rn : ArmReg) (rm : ArmReg) (ra : ArmReg)  -- rd = ra - rn*rm
  | neg (rd : ArmReg) (rn : ArmReg)
  -- Bitwise
  | and_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | orr_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | eor_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | mvn (rd : ArmReg) (rn : ArmReg)
  | lsl_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | lsr_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  | asr_reg (rd : ArmReg) (rn : ArmReg) (rm : ArmReg)
  -- Compare + conditional
  | cmp_imm (rn : ArmReg) (imm : Int)
  | cmp_reg (rn : ArmReg) (rm : ArmReg)
  | cset (rd : ArmReg) (cond : String)               -- cset rd, eq/ne/lt/gt/le/ge
  -- Branch
  | b (label : ArmLabel)
  | b_cond (cond : String) (label : ArmLabel)        -- b.eq, b.ne, etc.
  | cbz (rt : ArmReg) (label : ArmLabel)
  | cbnz (rt : ArmReg) (label : ArmLabel)
  | bl (name : String)                                -- bl _func
  | blr (rn : ArmReg)                                -- bl via register
  | ret
  -- Labels + directives
  | label_ (l : ArmLabel)
  | raw (s : String)                                  -- raw asm line (directives)
  | comment (s : String)
  deriving Repr

/-- Render a single AArch64 instruction to assembly text -/
def ArmInstr.render : ArmInstr → String
  | .mov_imm rd imm => s!"    mov {rd.toStr64}, #{imm}"
  | .mov_reg rd rs => s!"    mov {rd.toStr64}, {rs.toStr64}"
  | .movk rd imm shift => s!"    movk {rd.toStr64}, #{imm}, lsl #{shift}"
  | .ldr rt rn off => s!"    ldr {rt.toStr64}, [{rn.toStr64}, #{off}]"
  | .ldr_w rt rn off => s!"    ldr {rt.toStr32}, [{rn.toStr64}, #{off}]"
  | .ldrb rt rn off => s!"    ldrb {rt.toStr32}, [{rn.toStr64}, #{off}]"
  | .str rt rn off => s!"    str {rt.toStr64}, [{rn.toStr64}, #{off}]"
  | .str_w rt rn off => s!"    str {rt.toStr32}, [{rn.toStr64}, #{off}]"
  | .strb rt rn off => s!"    strb {rt.toStr32}, [{rn.toStr64}, #{off}]"
  | .stp rt1 rt2 rn off => s!"    stp {rt1.toStr64}, {rt2.toStr64}, [{rn.toStr64}, #{off}]!"
  | .ldp rt1 rt2 rn off => s!"    ldp {rt1.toStr64}, {rt2.toStr64}, [{rn.toStr64}, #{off}]"
  | .adrp rd sym => s!"    adrp {rd.toStr64}, {sym}@PAGE"
  | .add_sym rd rn sym => s!"    add {rd.toStr64}, {rn.toStr64}, {sym}@PAGEOFF"
  | .add_imm rd rn imm => s!"    add {rd.toStr64}, {rn.toStr64}, #{imm}"
  | .add_reg rd rn rm => s!"    add {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .sub_imm rd rn imm => s!"    sub {rd.toStr64}, {rn.toStr64}, #{imm}"
  | .sub_reg rd rn rm => s!"    sub {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .mul_reg rd rn rm => s!"    mul {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .sdiv rd rn rm => s!"    sdiv {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .msub rd rn rm ra => s!"    msub {rd.toStr64}, {rn.toStr64}, {rm.toStr64}, {ra.toStr64}"
  | .neg rd rn => s!"    neg {rd.toStr64}, {rn.toStr64}"
  | .and_reg rd rn rm => s!"    and {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .orr_reg rd rn rm => s!"    orr {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .eor_reg rd rn rm => s!"    eor {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .mvn rd rn => s!"    mvn {rd.toStr64}, {rn.toStr64}"
  | .lsl_reg rd rn rm => s!"    lsl {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .lsr_reg rd rn rm => s!"    lsr {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .asr_reg rd rn rm => s!"    asr {rd.toStr64}, {rn.toStr64}, {rm.toStr64}"
  | .cmp_imm rn imm => s!"    cmp {rn.toStr64}, #{imm}"
  | .cmp_reg rn rm => s!"    cmp {rn.toStr64}, {rm.toStr64}"
  | .cset rd cond => s!"    cset {rd.toStr64}, {cond}"
  | .b label => s!"    b {label.render}"
  | .b_cond cond label => s!"    b.{cond} {label.render}"
  | .cbz rt label => s!"    cbz {rt.toStr64}, {label.render}"
  | .cbnz rt label => s!"    cbnz {rt.toStr64}, {label.render}"
  | .bl name => s!"    bl _{name}"
  | .blr rn => s!"    blr {rn.toStr64}"
  | .ret => "    ret"
  | .label_ l => s!"{l.render}:"
  | .raw s => s
  | .comment s => s!"    // {s}"

end CCC.Emit
