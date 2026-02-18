import CCC.Syntax.AST

namespace CCC.Emit

/-- Typed label identity — eliminates cross-function label collisions by construction.
    Labels carry their owning function name, a kind tag, and a local index.
    Rendering to string happens only at the emission boundary. -/
structure LabelId where
  fn   : String
  kind : String
  idx  : Nat
  deriving Repr, Inhabited, BEq

namespace LabelId
def render (l : LabelId) : String := s!".L_{l.fn}_{l.kind}_{l.idx}"
end LabelId

inductive Register where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  | eax | edi | esi | edx | ecx | r8d | r9d
  | al | cl
  deriving Repr, Inhabited, BEq

inductive Operand where
  | reg (r : Register)
  | imm (val : Int)
  | mem (base : Register) (offset : Int)
  | memIdx (base : Register) (index : Register) (scale : Nat) (offset : Int)
  | label (name : String)
  deriving Repr, Inhabited

inductive Instr where
  | mov (src dst : Operand)
  | movl (src dst : Operand)     -- 32-bit move
  | movb (src dst : Operand)     -- 8-bit move
  | movzbl (src dst : Operand)   -- zero-extend byte to long
  | lea (src dst : Operand)
  | add (src dst : Operand)
  | sub (src dst : Operand)
  | imul (src dst : Operand)
  | cqo                          -- sign-extend rax → rdx:rax
  | idiv (src : Operand)
  | cmp (src dst : Operand)
  | xor_ (src dst : Operand)
  | and_ (src dst : Operand)
  | or_ (src dst : Operand)
  | not_ (dst : Operand)
  | shl (src dst : Operand)      -- shift left (src=cl or imm)
  | shr (src dst : Operand)      -- shift right (src=cl or imm)
  | push (src : Operand)
  | pop (dst : Operand)
  | call (target : String)
  | ret
  | jmp (target : LabelId)
  | je (target : LabelId)
  | jne (target : LabelId)
  | jl (target : LabelId)
  | jle (target : LabelId)
  | jg (target : LabelId)
  | jge (target : LabelId)
  | sete (dst : Operand)
  | setne (dst : Operand)
  | setl (dst : Operand)
  | setg (dst : Operand)
  | setle (dst : Operand)
  | setge (dst : Operand)
  | label_ (id : LabelId)
  | comment (text : String)
  deriving Repr, Inhabited

structure AsmFunction where
  name : String
  instrs : List Instr
  deriving Repr

structure AsmProgram where
  functions : List AsmFunction
  dataSection : List String
  deriving Repr


def Register.toATT : Register → String
  | .rax => "%rax"
  | .rbx => "%rbx"
  | .rcx => "%rcx"
  | .rdx => "%rdx"
  | .rsi => "%rsi"
  | .rdi => "%rdi"
  | .rbp => "%rbp"
  | .rsp => "%rsp"
  | .r8 => "%r8"
  | .r9 => "%r9"
  | .r10 => "%r10"
  | .r11 => "%r11"
  | .r12 => "%r12"
  | .r13 => "%r13"
  | .r14 => "%r14"
  | .r15 => "%r15"
  | .eax => "%eax"
  | .edi => "%edi"
  | .esi => "%esi"
  | .edx => "%edx"
  | .ecx => "%ecx"
  | .r8d => "%r8d"
  | .r9d => "%r9d"
  | .al => "%al"
  | .cl => "%cl"


def Operand.toATT : Operand → String
  | .reg r => r.toATT
  | .imm val => s!"${val}"
  | .mem base offset =>
      if offset = 0 then
        s!"({base.toATT})"
      else
        s!"{offset}({base.toATT})"
  | .memIdx base index scale offset =>
      if offset = 0 then
        s!"({base.toATT},{index.toATT},{scale})"
      else
        s!"{offset}({base.toATT},{index.toATT},{scale})"
  | .label name => name


def Instr.toATT : Instr → String
  | .mov src dst => s!"    movq {src.toATT}, {dst.toATT}"
  | .movl src dst => s!"    movl {src.toATT}, {dst.toATT}"
  | .movb src dst => s!"    movb {src.toATT}, {dst.toATT}"
  | .movzbl src dst => s!"    movzbl {src.toATT}, {dst.toATT}"
  | .lea src dst => s!"    leaq {src.toATT}, {dst.toATT}"
  | .add src dst => s!"    addq {src.toATT}, {dst.toATT}"
  | .sub src dst => s!"    subq {src.toATT}, {dst.toATT}"
  | .imul src dst => s!"    imulq {src.toATT}, {dst.toATT}"
  | .cqo => "    cqo"
  | .idiv src => s!"    idivq {src.toATT}"
  | .cmp src dst => s!"    cmpq {src.toATT}, {dst.toATT}"
  | .xor_ src dst => s!"    xorq {src.toATT}, {dst.toATT}"
  | .and_ src dst => s!"    andq {src.toATT}, {dst.toATT}"
  | .or_ src dst => s!"    orq {src.toATT}, {dst.toATT}"
  | .not_ dst => s!"    notq {dst.toATT}"
  | .shl src dst => s!"    shlq {src.toATT}, {dst.toATT}"
  | .shr src dst => s!"    shrq {src.toATT}, {dst.toATT}"
  | .push src => s!"    pushq {src.toATT}"
  | .pop dst => s!"    popq {dst.toATT}"
  | .call target => s!"    call {target}"
  | .ret => "    ret"
  | .jmp target => s!"    jmp {target.render}"
  | .je target => s!"    je {target.render}"
  | .jne target => s!"    jne {target.render}"
  | .jl target => s!"    jl {target.render}"
  | .jle target => s!"    jle {target.render}"
  | .jg target => s!"    jg {target.render}"
  | .jge target => s!"    jge {target.render}"
  | .sete dst => s!"    sete {dst.toATT}"
  | .setne dst => s!"    setne {dst.toATT}"
  | .setl dst => s!"    setl {dst.toATT}"
  | .setg dst => s!"    setg {dst.toATT}"
  | .setle dst => s!"    setle {dst.toATT}"
  | .setge dst => s!"    setge {dst.toATT}"
  | .label_ id => s!"{id.render}:"
  | .comment text => s!"    # {text}"

private def emitFunctionLines (funDef : AsmFunction) : List String :=
  [s!".globl {funDef.name}", s!"{funDef.name}:"] ++ funDef.instrs.map Instr.toATT


def emitAsm (prog : AsmProgram) : String :=
  let dataLines : List String :=
    if prog.dataSection.isEmpty then
      []
    else
      [".data"] ++ prog.dataSection
  let textLines : List String :=
    [".text"] ++ (prog.functions.map emitFunctionLines).flatten
  let lines := dataLines ++ textLines
  String.intercalate "\n" lines ++ "\n"

end CCC.Emit
