import CCC

open CCC.Preprocess CCC.Parse

def testTypedef (name : String) (src : String) (expectOk : Bool) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .ok prog =>
      if expectOk then
        IO.println s!"✓ {name}: parsed ({prog.functions.length} fns)"
        pure true
      else
        IO.eprintln s!"✗ {name}: expected failure"
        pure false
  | .error e =>
      if !expectOk then
        IO.println s!"✓ {name}: correctly rejected"
        pure true
      else
        IO.eprintln s!"✗ {name}: {e.take 80}"
        pure false

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  let cases : List (String × String × Bool) := [
    ("basic_typedef",
     "typedef int myint;\nint main() { myint x = 42; return x; }",
     true),
    ("typedef_ptr",
     "typedef int *intptr;\nint main() { int y = 5; intptr p = &y; return *p; }",
     true),
    ("typedef_struct",
     "struct Point { int x; int y; };\ntypedef struct Point Point;\nint main() { Point p; p.x = 1; return p.x; }",
     true),
    ("typedef_chain",
     "typedef int myint;\ntypedef myint myint2;\nint main() { myint2 x = 10; return x; }",
     true),
    ("stdint_types",
     "#include <stdint.h>\nint main() { int32_t x = 42; uint8_t y = 255; return x; }",
     true),
    ("size_t_use",
     "#include <stddef.h>\nint main() { size_t n = 100; return 0; }",
     true),
    ("stdio_file",
     "#include <stdio.h>\nint main() { FILE *f = 0; return 0; }",
     true),
    ("stdlib_use",
     "#include <stdlib.h>\nint main() { void *p = malloc(10); free(p); return 0; }",
     true),
    ("typedef_func_param",
     "typedef int Number;\nint add(Number a, Number b) { return a + b; }\nint main() { return add(1, 2); }",
     true),
    ("typedef_in_for",
     "typedef int idx;\nint main() { int sum = 0; for (idx i = 0; i < 10; i = i + 1) { sum = sum + i; } return sum; }",
     true)
  ]

  for (name, src, expect) in cases do
    total := total + 1
    let ok ← testTypedef name src expect
    if ok then pass := pass + 1

  IO.println s!"\n═══════════════════════════════════════"
  IO.println s!"  Typedef resolution: {pass}/{total}"
  IO.println s!"═══════════════════════════════════════"
  if pass == total then pure 0 else pure 1
