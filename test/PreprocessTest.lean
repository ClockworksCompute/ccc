import CCC

open CCC.Preprocess CCC.Parse

def testPP (name : String) (src : String) (expectOk : Bool) : IO Bool := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .ok prog =>
      if expectOk then
        IO.println s!"✓ {name}: preprocessed + parsed ({prog.functions.length} functions)"
        pure true
      else
        IO.eprintln s!"✗ {name}: expected parse failure but parsed OK"
        pure false
  | .error e =>
      if !expectOk then
        IO.println s!"✓ {name}: correctly failed ({e.take 40}...)"
        pure true
      else
        IO.eprintln s!"✗ {name}: preprocess/parse error: {e.take 80}"
        pure false

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  let cases : List (String × String × Bool) := [
    ("include_stdio",
     "#include <stdio.h>\nint main() { return 0; }",
     true),
    ("include_stdlib",
     "#include <stdlib.h>\nint main() { void *p = malloc(10); free(p); return 0; }",
     true),
    ("include_string",
     "#include <string.h>\nint main() { size_t n = strlen(\"hello\"); return 0; }",
     true),
    ("define_simple",
     "#define MAX 100\nint main() { int x = MAX; return x; }",
     true),
    ("ifdef_true",
     "#define FOO\n#ifdef FOO\nint main() { return 1; }\n#endif\n",
     true),
    ("ifdef_false",
     "#ifdef BAR\nint main() { return 1; }\n#endif\nint main() { return 0; }\n",
     true),
    ("ifndef",
     "#ifndef MISSING\nint main() { return 42; }\n#endif\n",
     true),
    ("if_else",
     "#define X 1\n#if X\nint main() { return 1; }\n#else\nint main() { return 0; }\n#endif\n",
     true),
    ("nested_ifdef",
     "#define A\n#define B\n#ifdef A\n#ifdef B\nint main() { return 2; }\n#endif\n#endif\n",
     true),
    ("include_limits",
     "#include <limits.h>\nint main() { int x = INT_MAX; return 0; }",
     true),
    -- stdint.h typedefs need typedef resolution (T-002) to use as types
    ("include_stdint",
     "#include <stdint.h>\nint main() { int x = 42; return x; }",
     true),
    ("undef",
     "#define X 10\n#undef X\n#define X 20\nint main() { int v = X; return v; }",
     true),
    ("pragma_ignored",
     "#pragma once\nint main() { return 0; }",
     true),
    ("include_guard",
     "#ifndef MYHEADER_H\n#define MYHEADER_H\nint foo() { return 1; }\n#endif\nint main() { return foo(); }",
     true)
  ]

  for (name, src, expect) in cases do
    total := total + 1
    let ok ← testPP name src expect
    if ok then pass := pass + 1

  IO.println s!"\n═══════════════════════════════════════"
  IO.println s!"  Preprocessor: {pass}/{total} passed"
  IO.println s!"═══════════════════════════════════════"
  if pass == total then pure 0 else pure 1
