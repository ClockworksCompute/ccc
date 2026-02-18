import CCC
open CCC.Preprocess CCC.Parse

def main : IO UInt32 := do
  let raw := [
    "#define luai_likely(x) (x)",
    "#define luaL_argcheck(L,cond,arg,extramsg) ((void)((cond) || luaL_argerror(L, (arg), (extramsg))))",
    "int luaL_argerror(int L, int arg, const char *msg);",
    "void test(int L, int idx) {",
    "  luaL_argcheck(L, !(idx <= -1000), 1, \"invalid index\");",
    "}"
  ].foldl (fun a b => a ++ "\n" ++ b) ""
  let pp ← preprocess raw "."
  IO.println s!"PP output:"
  for line in pp.splitOn "\n" do
    if !line.isEmpty then IO.println s!"  {line}"
  match parseProgram pp with
  | .ok p => IO.println s!"✓ {p.functions.length} fns"; pure 0
  | .error e => IO.println s!"✗ {e}"; pure 1
