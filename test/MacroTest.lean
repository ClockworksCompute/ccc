import CCC
open CCC.Preprocess CCC.Parse

def main : IO UInt32 := do
  let raw := "#if defined(__GNUC__)\n#define likely(x) __builtin_expect(x, 1)\n#else\n#define likely(x) (x)\n#endif\nint main() { return likely(1); }\n"
  let pp ← preprocess raw "."
  IO.println s!"PP: {pp.take 200}"
  match parseProgram pp with
  | .ok p => IO.println s!"✓ {p.functions.length} fns"; pure 0
  | .error e => IO.println s!"✗ {e}"; pure 1
