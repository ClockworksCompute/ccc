/-
  test/regression/StructArrayRepro.lean
  CCC-BUG-003: Validates struct-with-array codegen.

  Originally an x86-64 assembly-text pattern check (looking for a specific
  `addq $N, %rax` / `movq (%rax), %rax` deref-after-field-offset bug shape).
  `CCC.compile` emits AArch64 by default now (FEL-52), so this was ported:
  rather than chase the AArch64 analog of that exact x86 instruction
  sequence — a fragile, easy-to-get-subtly-wrong text pattern that risks
  false-passing on a differently-shaped bug or false-failing on a
  perfectly correct but differently-scheduled instruction sequence —
  this actually assembles, links, and RUNS the compiled program and checks
  the real exit code. That is a strictly stronger guard: any
  deref-after-field-offset corruption would show up as a wrong exit code
  (the true field value: 3), not just an assembly-text shape.
-/
import CCC

def assembleLinkRun (asm : String) (tag : String) : IO (Except String UInt32) := do
  let asmPath := s!"/tmp/ccc_regr_{tag}.s"
  let objPath := s!"/tmp/ccc_regr_{tag}.o"
  let binPath := s!"/tmp/ccc_regr_{tag}"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
  if asOut.exitCode != 0 then
    return .error s!"assembler error:\n{asOut.stderr}"
  let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath] }
  if ccOut.exitCode != 0 then
    return .error s!"linker error:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  return .ok runOut.exitCode

def main : IO Unit := do
  let src := "
struct Msg { int len; char data[8]; };

int main() {
    struct Msg m;
    m.len = 3;
    m.data[0] = 65;
    m.data[1] = 66;
    m.data[2] = 67;
    return m.len;
}
"
  let result := CCC.compile src "struct_array_repro.c"
  match result.assembly with
  | none =>
    IO.eprintln s!"✗ FAIL  StructArrayRepro — compilation failed: {result.report}"
    IO.Process.exit 1
  | some asm =>
    let lines := asm.splitOn "\n"

    -- Check 1: entry point and return present (AArch64: `_main` is
    -- underscore-prefixed for Mach-O; `ret` is unchanged from x86).
    let hasGlobl := lines.any (fun l => (l.splitOn ".globl _main").length > 1)
    let hasRet := lines.any (fun l => l.trimAscii.toString == "ret")
    if !hasGlobl || !hasRet then
      IO.eprintln "✗ FAIL  StructArrayRepro — missing .globl _main or ret"
      IO.Process.exit 1

    -- Check 2: adequate stack allocation for a 12-byte struct
    -- (int len + char data[8] = 12, rounded up to a 16-byte-aligned frame).
    -- AArch64 prologue shape: `sub sp, sp, #N`.
    let subLine := lines.find? (fun l =>
      (l.splitOn "sub sp, sp, #").length > 1)
    match subLine with
    | none =>
      IO.eprintln "✗ FAIL  StructArrayRepro — no stack allocation found"
      IO.Process.exit 1
    | some sl =>
      let parts := sl.splitOn "#"
      match parts[1]? with
      | none =>
        IO.eprintln "✗ FAIL  StructArrayRepro — cannot parse stack size"
        IO.Process.exit 1
      | some afterHash =>
        match afterHash.trimAscii.toString.toNat? with
        | none =>
          IO.eprintln s!"✗ FAIL  StructArrayRepro — cannot parse stack size from '{afterHash}'"
          IO.Process.exit 1
        | some size =>
          if size < 16 then
            IO.eprintln s!"✗ FAIL  StructArrayRepro — stack too small: {size} (need ≥ 16)"
            IO.Process.exit 1
          else
            -- Check 3: the program actually computes the right answer —
            -- this is the real regression guard for a deref-after-field-
            -- offset bug (see module docstring above).
            match ← assembleLinkRun asm "struct_array" with
            | .error e =>
              IO.eprintln s!"✗ FAIL  StructArrayRepro — {e}"
              IO.Process.exit 1
            | .ok exitCode =>
              if exitCode == 3 then
                IO.println s!"✓ PASS  StructArrayRepro — exit={exitCode}, stack={size} bytes, assembly valid"
              else
                IO.eprintln s!"✗ FAIL  StructArrayRepro — exit={exitCode}, expected 3 (deref-after-field-offset bug?)"
                IO.Process.exit 1
