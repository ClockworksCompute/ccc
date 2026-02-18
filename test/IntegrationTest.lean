/-
  test/IntegrationTest.lean — EPIC-CCC43: Integration tests

  15+ progressively harder E2E tests.
  C source → preprocess → parse → verify → emit AArch64 → as → cc → run → check exit code.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

-- ═══════════════════════════════════════════════════════════════
-- Test infrastructure
-- ═══════════════════════════════════════════════════════════════

/-- Preprocess + parse + force-emit via AArch64 backend -/
def compileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

/-- Compile via full pipeline (parse → verify → force-emit) -/
def compileViaPipeline (src : String) : IO (Option String) := do
  let pp ← preprocess src "."
  let result := CCC.compile pp "integration_test.c"
  pure result.assembly

/-- Assemble + link + run, returning exit code -/
def assembleAndRun (asm : String) (testName : String)
    (withRuntime : Bool := false) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_integ_{testName}.s"
  let objPath := s!"/tmp/ccc_integ_{testName}.o"
  let binPath := s!"/tmp/ccc_integ_{testName}"
  IO.FS.writeFile asmPath asm
  -- Assemble
  let asOut ← IO.Process.output {
    cmd := "as"
    args := #["-o", objPath, asmPath]
  }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  -- Build link args
  let mut linkArgs : Array String := #["-o", binPath, objPath]
  if withRuntime then
    let rtOut ← IO.Process.output {
      cmd := "cc"
      args := #["-c", "-o", "/tmp/ccc_integ_runtime.o", "runtime/ccc_runtime.c"]
    }
    if rtOut.exitCode != 0 then
      throw <| IO.userError s!"runtime compile failed:\n{rtOut.stderr}"
    linkArgs := linkArgs.push "/tmp/ccc_integ_runtime.o"
  -- Link
  let ccOut ← IO.Process.output {
    cmd := "cc"
    args := linkArgs
  }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"link failed for {testName}:\n{ccOut.stderr}"
  -- Run
  let runOut ← IO.Process.output {
    cmd := binPath
    args := #[]
  }
  pure runOut.exitCode

/-- Run a single test: compile C → asm → assemble → link → run → check exit code -/
def runTest (name : String) (src : String) (expectedExit : UInt32)
    (withRuntime : Bool := false) (usePipeline : Bool := false) : IO Bool := do
  let asmResult ← do
    if usePipeline then
      let r ← compileViaPipeline src
      pure (match r with | some a => Except.ok a | none => Except.error "pipeline produced no assembly")
    else
      compileToArm src
  match asmResult with
  | .error e =>
      IO.eprintln s!"✗ {name}: compilation error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← assembleAndRun asm name (withRuntime := withRuntime)
        if exitCode == expectedExit then
          IO.println s!"✓ {name}: exit {exitCode} (expected {expectedExit})"
          pure true
        else
          IO.eprintln s!"✗ {name}: exit {exitCode}, expected {expectedExit}"
          pure false
      catch e =>
        IO.eprintln s!"✗ {name}: {e}"
        pure false

/-- Run a test that is expected to fail; log reason but don't count as failure. -/
def runSkippedTest (name : String) (src : String) (expectedExit : UInt32)
    (reason : String) (usePipeline : Bool := false)
    (withRuntime : Bool := false) : IO Unit := do
  IO.println s!"⊘ {name}: SKIP — {reason}"
  -- Attempt it anyway so we can see if it starts passing
  let asmResult ← do
    if usePipeline then
      let r ← compileViaPipeline src
      pure (match r with | some a => Except.ok a | none => Except.error "no asm")
    else
      compileToArm src
  match asmResult with
  | .error _ => pure ()
  | .ok asm =>
      try
        let exitCode ← assembleAndRun asm (name ++ "_probe") (withRuntime := withRuntime)
        if exitCode == expectedExit then
          IO.println s!"  ↑ (actually PASSES now — exit {exitCode})"
      catch _ => pure ()

-- ═══════════════════════════════════════════════════════════════
-- Main test driver
-- ═══════════════════════════════════════════════════════════════

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  IO.println "═══════════════════════════════════════════════════"
  IO.println "  EPIC-CCC43: Integration — Real Programs Compile"
  IO.println "═══════════════════════════════════════════════════"
  IO.println ""
  IO.println "── Tier 1: Basics ──"

  -- ═══════════════════════════════════════════
  -- T1: Arithmetic expression
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T01_arithmetic" "int main() { return (3 + 4) * 2 - 1; }" 13 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T2: Multiple locals with reassignment
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T02_locals_reassign"
    "int main() { int a = 10; int b = 20; a = a + b; b = a - 5; return b; }" 25 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T3: Nested function calls: f(g(x))
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T03_nested_calls"
    "int double_(int x) { return x * 2; } int add3(int x) { return x + 3; } int main() { return double_(add3(5)); }" 16 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T4: Pointer dereference chain
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T04_ptr_deref_chain"
    "int main() { int x = 5; int *p = &x; int **pp = &p; return **pp; }" 5 then
    pass := pass + 1

  IO.println ""
  IO.println "── Tier 2: Control Flow ──"

  -- ═══════════════════════════════════════════
  -- T5: Nested loops compute sum 1..10 → 55
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T05_nested_loops"
    ("int main() {\n" ++
     "  int total = 0;\n" ++
     "  for (int i = 1; i <= 10; i = i + 1) {\n" ++
     "    for (int j = 0; j < i; j = j + 1) {\n" ++
     "      total = total + 1;\n" ++
     "    }\n" ++
     "  }\n" ++
     "  return total;\n" ++
     "}\n") 55 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T6: Switch with fallthrough
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T06_switch_fallthrough"
    ("int main() {\n" ++
     "  int x = 1;\n" ++
     "  int r = 0;\n" ++
     "  switch (x) {\n" ++
     "    case 1: r = r + 10;\n" ++
     "    case 2: r = r + 20;\n" ++
     "      break;\n" ++
     "    case 3: r = r + 30;\n" ++
     "      break;\n" ++
     "  }\n" ++
     "  return r;\n" ++
     "}\n") 30 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T7: Recursive factorial: fact(5) = 120
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T07_recursive_fact"
    ("int fact(int n) {\n" ++
     "  if (n <= 1) { return 1; }\n" ++
     "  return n * fact(n - 1);\n" ++
     "}\n" ++
     "int main() { return fact(5); }\n") 120 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T8: Early return from nested if
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T08_early_return"
    ("int check(int x) {\n" ++
     "  if (x > 100) { return 3; }\n" ++
     "  if (x > 10) { return 2; }\n" ++
     "  if (x > 0) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n" ++
     "int main() {\n" ++
     "  int a = check(200);\n" ++
     "  int b = check(50);\n" ++
     "  return a * 10 + b;\n" ++
     "}\n") 32 then  -- 3*10 + 2 = 32
    pass := pass + 1

  IO.println ""
  IO.println "── Tier 3: Structs + Pointers ──"

  -- ═══════════════════════════════════════════
  -- T9: Struct with member access (dot)
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T09_struct_dot"
    ("struct Point { int x; int y; };\n" ++
     "int main() {\n" ++
     "  struct Point p;\n" ++
     "  p.x = 17;\n" ++
     "  p.y = 25;\n" ++
     "  return p.x + p.y;\n" ++
     "}\n") 42 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T10: Struct with pointer field via malloc+arrow
  -- (uses force-emit pipeline since malloc triggers verify warnings)
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T10_struct_ptr_field"
    ("struct Pair { int a; int b; };\n" ++
     "int main() {\n" ++
     "  struct Pair *p = malloc(16);\n" ++
     "  p->a = 17;\n" ++
     "  p->b = 25;\n" ++
     "  int r = p->a + p->b;\n" ++
     "  free(p);\n" ++
     "  return r;\n" ++
     "}\n") 42 (usePipeline := true) (withRuntime := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T11: Array of structs via pointer arithmetic
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T11_struct_array_manual"
    ("struct Item { int val; int pad; };\n" ++
     "int main() {\n" ++
     "  struct Item *arr = malloc(48);\n" ++
     "  arr->val = 10;\n" ++
     "  struct Item *second = arr + 1;\n" ++
     "  second->val = 20;\n" ++
     "  struct Item *third = arr + 2;\n" ++
     "  third->val = 12;\n" ++
     "  int r = arr->val + second->val + third->val;\n" ++
     "  free(arr);\n" ++
     "  return r;\n" ++
     "}\n") 42 (usePipeline := true) (withRuntime := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T12: Nested struct access
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T12_nested_struct"
    ("struct Inner { int val; int pad; };\n" ++
     "struct Outer { struct Inner a; struct Inner b; };\n" ++
     "int main() {\n" ++
     "  struct Outer s;\n" ++
     "  s.a.val = 17;\n" ++
     "  s.b.val = 25;\n" ++
     "  return s.a.val + s.b.val;\n" ++
     "}\n") 42 then
    pass := pass + 1

  IO.println ""
  IO.println "── Tier 4: Standard Library ──"

  -- ═══════════════════════════════════════════
  -- T13: strlen on string literal
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T13_strlen"
    ("int strlen(const char *s);\n" ++
     "int main() {\n" ++
     "  return strlen(\"hello\");\n" ++
     "}\n") 5 (usePipeline := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T14: strcmp of two equal strings → 0
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T14_strcmp"
    ("int strcmp(const char *a, const char *b);\n" ++
     "int main() {\n" ++
     "  int r = strcmp(\"abc\", \"abc\");\n" ++
     "  if (r == 0) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n") 1 (usePipeline := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T15: puts + return code
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T15_puts"
    ("int puts(const char *s);\n" ++
     "int main() {\n" ++
     "  puts(\"integration test output\");\n" ++
     "  return 7;\n" ++
     "}\n") 7 (usePipeline := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T16: memset a buffer, check first byte
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T16_memset"
    ("void *memset(void *s, int c, long n);\n" ++
     "int main() {\n" ++
     "  char buf[16];\n" ++
     "  memset(buf, 42, 16);\n" ++
     "  return buf[0];\n" ++
     "}\n") 42 (usePipeline := true) then
    pass := pass + 1

  IO.println ""
  IO.println "── Tier 5: Complex Programs ──"

  -- ═══════════════════════════════════════════
  -- T17: Fibonacci iterative
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T17_fib_iterative"
    ("int main() {\n" ++
     "  int a = 0;\n" ++
     "  int b = 1;\n" ++
     "  for (int i = 0; i < 10; i = i + 1) {\n" ++
     "    int t = a + b;\n" ++
     "    a = b;\n" ++
     "    b = t;\n" ++
     "  }\n" ++
     "  return a;\n" ++
     "}\n") 55 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T18: Bitwise operations combined
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T18_bitwise_combined"
    ("int main() {\n" ++
     "  int x = 0xAB;\n" ++
     "  int lo = x & 0x0F;\n" ++
     "  int hi = (x >> 4) & 0x0F;\n" ++
     "  int combined = (hi << 4) | lo;\n" ++
     "  if (combined == x) { return 1; }\n" ++
     "  return 0;\n" ++
     "}\n") 1 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T19: GCD by Euclidean algorithm
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T19_gcd"
    ("int gcd(int a, int b) {\n" ++
     "  while (b != 0) {\n" ++
     "    int t = b;\n" ++
     "    b = a % b;\n" ++
     "    a = t;\n" ++
     "  }\n" ++
     "  return a;\n" ++
     "}\n" ++
     "int main() { return gcd(252, 105); }\n") 21 then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T20: Bubble sort (manual array via pointer arithmetic)
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T20_bubble_sort"
    ("int main() {\n" ++
     "  int arr[5];\n" ++
     "  arr[0] = 5; arr[1] = 3; arr[2] = 4; arr[3] = 1; arr[4] = 2;\n" ++
     "  for (int i = 0; i < 5; i = i + 1) {\n" ++
     "    for (int j = 0; j < 4 - i; j = j + 1) {\n" ++
     "      if (arr[j] > arr[j + 1]) {\n" ++
     "        int tmp = arr[j];\n" ++
     "        arr[j] = arr[j + 1];\n" ++
     "        arr[j + 1] = tmp;\n" ++
     "      }\n" ++
     "    }\n" ++
     "  }\n" ++
     "  return arr[0] * 16 + arr[1] * 8 + arr[2] * 4 + arr[3] * 2 + arr[4];\n" ++
     "}\n") (1*16 + 2*8 + 3*4 + 4*2 + 5) then  -- 16+16+12+8+5 = 57
    pass := pass + 1

  IO.println ""
  IO.println "── Tier 6: Bonus (formerly skipped) ──"

  -- ═══════════════════════════════════════════
  -- T21: Linked list: create 2 nodes, sum values
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T21_linked_list"
    ("struct Node { int val; int pad; struct Node *next; };\n" ++
     "int main() {\n" ++
     "  struct Node *head = malloc(24);\n" ++
     "  head->val = 10;\n" ++
     "  struct Node *n2 = malloc(24);\n" ++
     "  n2->val = 20;\n" ++
     "  head->next = n2;\n" ++
     "  int sum = head->val + n2->val;\n" ++
     "  free(n2);\n" ++
     "  free(head);\n" ++
     "  return sum;\n" ++
     "}\n") 30 (usePipeline := true) (withRuntime := true) then
    pass := pass + 1

  -- ═══════════════════════════════════════════
  -- T22: snprintf to format, check return value
  -- ═══════════════════════════════════════════
  total := total + 1
  if ← runTest "T22_snprintf"
    ("int snprintf(char *buf, long n, const char *fmt);\n" ++
     "int main() {\n" ++
     "  char buf[32];\n" ++
     "  int r = snprintf(buf, 32, \"hello\");\n" ++
     "  return r;\n" ++
     "}\n") 5 (usePipeline := true) then
    pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════════════"
  IO.println s!"  Integration: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
