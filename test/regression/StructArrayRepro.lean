/-
  test/regression/StructArrayRepro.lean
  CCC-BUG-003: Validates struct-with-array codegen.
  Checks: compilation succeeds, no deref-after-field-offset bug pattern,
  adequate stack allocation.
-/
import CCC

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
  | some asm =>
    let lines := asm.splitOn "\n"

    -- Check 1: .globl main and ret present
    let hasGlobl := lines.any (fun l => (l.splitOn ".globl main").length > 1)
    let hasRet := lines.any (fun l => (l.splitOn "ret").length > 1)
    if !hasGlobl || !hasRet then
      IO.eprintln "✗ FAIL  StructArrayRepro — missing .globl main or ret"
      IO.Process.exit 1

    -- Check 2: No deref-after-field-offset bug pattern
    -- The bug pattern is: addq $N, %rax followed by movq (%rax), %rax
    let rec checkBugPattern (remaining : List String) : Bool :=
      match remaining with
      | [] => false
      | l1 :: l2 :: rest =>
          let isAdd := (l1.splitOn "addq $").length > 1 && (l1.splitOn "%rax").length > 1
          let isDeref := l2.trimAscii.toString == "movq (%rax), %rax"
          if isAdd && isDeref then true
          else checkBugPattern (l2 :: rest)
      | _ :: rest => checkBugPattern rest
    if checkBugPattern lines then
      IO.eprintln "✗ FAIL  StructArrayRepro — found deref-after-field-offset bug pattern"
      IO.Process.exit 1

    -- Check 3: Stack allocation ≥ 16 (struct is 12 bytes → roundUp8=16, min=16)
    let mainLines := lines.dropWhile (fun l => (l.splitOn "main:").length ≤ 1)
    let subqLine := mainLines.find? (fun l =>
      (l.splitOn "subq $").length > 1 && (l.splitOn "%rsp").length > 1)
    match subqLine with
    | none =>
      IO.eprintln "✗ FAIL  StructArrayRepro — no stack allocation found"
      IO.Process.exit 1
    | some sl =>
      -- Extract the number between "subq $" and ", %rsp"
      let parts := sl.splitOn "$"
      match parts[1]? with
      | none =>
        IO.eprintln "✗ FAIL  StructArrayRepro — cannot parse stack size"
        IO.Process.exit 1
      | some afterDollar =>
        let numStr := (afterDollar.splitOn ",").head!
        match numStr.trimAscii.toString.toNat? with
        | none =>
          IO.eprintln s!"✗ FAIL  StructArrayRepro — cannot parse stack size from '{numStr}'"
          IO.Process.exit 1
        | some size =>
          if size < 16 then
            IO.eprintln s!"✗ FAIL  StructArrayRepro — stack too small: {size} (need ≥ 16)"
            IO.Process.exit 1
          else
            IO.println s!"✓ PASS  StructArrayRepro — no deref bug, stack={size} bytes, assembly valid"

  | none =>
    IO.eprintln s!"✗ FAIL  StructArrayRepro — compilation failed: {result.report}"
    IO.Process.exit 1
