import CCC
open CCC.Preprocess

def main : IO UInt32 := do
  let raw := [
    "#define api_check(l,e,msg) luai_apicheck(l,(e) && msg)",
    "#define luai_apicheck(l,e) assert(e)",
    "#define assert(expr) ((void)0)",
    "void test() {",
    "  api_check(L, o < L->top, \"invalid index\");",
    "}"
  ].foldl (fun a b => a ++ "\n" ++ b) ""
  let pp ← preprocess raw "."
  for line in pp.splitOn "\n" do
    if !line.isEmpty then IO.println s!"  {line}"
  pure 0
