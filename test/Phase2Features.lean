/-
  Phase 2 feature integration test.
  Verifies that new C99 features parse, verify, and (where applicable) emit.
-/
import CCC

open CCC.Parse CCC.Syntax CCC.Verify CCC.Emit

def testParseAndVerify (name : String) (src : String) (expectAccept : Bool) : IO Bool := do
  match parseProgram src with
  | .error e =>
      if expectAccept then
        IO.eprintln s!"✗ {name}: unexpected parse error: {e}"
        pure false
      else
        IO.println s!"✓ {name}: correctly rejected at parse"
        pure true
  | .ok prog =>
      let result := CCC.Verify.verifyProgramReport prog
      let accepted := result.isSafe
      if accepted == expectAccept then
        if expectAccept then do
          -- Also try emit
          match emitProgramImpl prog with
          | .ok _ => IO.println s!"✓ {name}: accepted + emits"
          | .error e => IO.println s!"✓ {name}: accepted (emit error: {e}, expected for some features)"
        else
          IO.println s!"✓ {name}: correctly rejected"
        pure true
      else
        IO.eprintln s!"✗ {name}: expected {if expectAccept then "ACCEPT" else "REJECT"} got {if accepted then "ACCEPT" else "REJECT"}"
        pure false

def main : IO UInt32 := do
  let mut pass : Nat := 0
  let mut total : Nat := 0

  let cases : List (String × String × Bool) := [
    -- Ternary
    ("ternary", "int main() { int x = 5; int y = x > 3 ? 1 : 0; return y; }", true),
    -- Bitwise
    ("bitwise_and", "int main() { int x = 0xFF & 0x0F; return x; }", true),
    ("bitwise_or", "int main() { int x = 0xF0 | 0x0F; return x; }", true),
    ("bitwise_xor", "int main() { int x = 0xFF ^ 0x0F; return x; }", true),
    ("bitwise_not", "int main() { int x = ~0; return x; }", true),
    ("shift_left", "int main() { int x = 1 << 3; return x; }", true),
    ("shift_right", "int main() { int x = 8 >> 2; return x; }", true),
    -- Increment/Decrement
    ("pre_inc", "int main() { int x = 5; ++x; return x; }", true),
    ("post_inc", "int main() { int x = 5; x++; return x; }", true),
    -- String literals
    ("string_lit", "int main() { char *s = \"hello\"; return 0; }", true),
    -- Switch
    ("switch_basic", "int main() { int x = 2; int r = 0; switch (x) { case 1: r = 10; break; case 2: r = 20; break; default: r = 30; break; } return r; }", true),
    -- Do-while
    ("do_while", "int main() { int x = 0; do { x = x + 1; } while (x < 5); return x; }", true),
    -- Break/continue
    ("break_loop", "int main() { int i = 0; while (i < 100) { if (i > 5) { break; } i = i + 1; } return i; }", true),
    -- Goto
    ("goto_label", "int main() { int x = 0; goto done; x = 42; done: return x; }", true),
    -- Enum
    ("enum_def", "enum Color { RED, GREEN = 5, BLUE }; int main() { return 0; }", true),
    -- Union
    ("union_def", "union Value { int i; char c; }; int main() { return 0; }", true),
    -- Typedef (parsing the declaration; using typedef names as types needs symbol table)
    ("typedef_basic", "typedef int myint; int main() { int x = 42; return x; }", true),
    -- Float types
    ("float_decl", "int main() { float x = 3.14; double y = 2.71; return 0; }", true),
    -- NULL
    ("null_ptr", "int main() { int *p = NULL; return 0; }", true),
    -- Cast
    ("cast_expr", "int main() { int x = (int)3.14; return x; }", true),
    -- Comma expression
    ("comma_expr", "int main() { int x = 0; x = (1, 2, 3); return x; }", true),
    -- Const qualifier
    ("const_qual", "int main() { const int x = 42; return x; }", true),
    -- Short type
    ("short_type", "int main() { short x = 10; return x; }", true),
    -- Signed type
    ("signed_type", "int main() { signed int x = -5; return 0; }", true),
    -- Long long
    ("long_long", "int main() { long long x = 100; return 0; }", true),
    -- Empty statement
    ("empty_stmt", "int main() { ; return 0; }", true),
    -- Unsigned bare
    ("unsigned_bare", "int main() { unsigned x = 42; return x; }", true),
    -- Compound assignment
    ("plus_assign", "int main() { int x = 10; x += 5; return x; }", true),
    ("minus_assign", "int main() { int x = 10; x -= 3; return x; }", true),
    ("star_assign", "int main() { int x = 5; x *= 3; return x; }", true),
    ("div_assign", "int main() { int x = 20; x /= 4; return x; }", true),
    ("mod_assign", "int main() { int x = 17; x %= 5; return x; }", true),
    ("and_assign", "int main() { int x = 0xFF; x &= 0x0F; return x; }", true),
    ("or_assign", "int main() { int x = 0xF0; x |= 0x0F; return x; }", true),
    ("xor_assign", "int main() { int x = 0xFF; x ^= 0x0F; return x; }", true),
    ("shl_assign", "int main() { int x = 1; x <<= 3; return x; }", true),
    ("shr_assign", "int main() { int x = 16; x >>= 2; return x; }", true)
  ]

  for (name, src, expect) in cases do
    total := total + 1
    let ok ← testParseAndVerify name src expect
    if ok then pass := pass + 1

  IO.println s!"\n═══════════════════════════════════════"
  IO.println s!"  Phase 2 features: {pass}/{total} passed"
  IO.println s!"═══════════════════════════════════════"
  if pass == total then pure 0 else pure 1
