/-
  PreprocessElifTest.lean — Tests for #if/#elif/#else chain semantics
  and comparison operators (==, !=, <, >, <=, >=) in preprocessor.
-/
import CCC

def pp (src : String) : IO String := CCC.Preprocess.preprocess src "/tmp"
def lines (s : String) : List String := (s.splitOn "\n").filter (fun l => l.length > 0 && !l.startsWith "/*")

def check (label : String) (src : String) (expected : List String) : IO Bool := do
  let result ← pp src
  let got := lines result
  if got == expected then
    IO.println s!"  ✅ {label}"
    pure true
  else
    IO.println s!"  ❌ {label}"
    IO.println s!"     expected: {expected}"
    IO.println s!"     got:      {got}"
    pure false

def main : IO UInt32 := do
  IO.println "═══ Preprocessor #elif + Comparison Tests ═══"
  let mut passed := 0
  let mut total := 0

  -- T1: #if true, #elif skipped
  total := total + 1
  if ← check "T1: #if true → first branch only"
    "#if 1\nA\n#elif 1\nB\n#endif\n" ["A"] then passed := passed + 1

  -- T2: #if false, #elif true → second branch
  total := total + 1
  if ← check "T2: #if false, #elif true → second branch"
    "#if 0\nA\n#elif 1\nB\n#endif\n" ["B"] then passed := passed + 1

  -- T3: both false → #else
  total := total + 1
  if ← check "T3: #if false, #elif false → #else"
    "#if 0\nA\n#elif 0\nB\n#else\nC\n#endif\n" ["C"] then passed := passed + 1

  -- T4: 4-branch #elif chain, third matches
  total := total + 1
  if ← check "T4: 4-branch chain, third matches"
    "#define X 3\n#if X == 1\nA\n#elif X == 2\nB\n#elif X == 3\nC\n#elif X == 4\nD\n#endif\n"
    ["C"] then passed := passed + 1

  -- T5: once a branch is taken, later branches skipped
  total := total + 1
  if ← check "T5: first match wins, later branches skipped"
    "#define X 2\n#if X == 2\nFIRST\n#elif X == 2\nSECOND\n#endif\n"
    ["FIRST"] then passed := passed + 1

  -- T6: nested #if inside #elif
  total := total + 1
  if ← check "T6: nested #if inside #elif"
    "#if 0\nOUTER_IF\n#elif 1\n#if 1\nNESTED_YES\n#else\nNESTED_NO\n#endif\n#endif\n"
    ["NESTED_YES"] then passed := passed + 1

  -- T7: macro-expanded == comparison
  total := total + 1
  if ← check "T7: macro-expanded =="
    "#define A 5\n#define B 5\n#if A == B\nEQ\n#else\nNE\n#endif\n"
    ["EQ"] then passed := passed + 1

  -- T8: != operator
  total := total + 1
  if ← check "T8: != operator"
    "#if 3 != 4\nDIFF\n#else\nSAME\n#endif\n"
    ["DIFF"] then passed := passed + 1

  -- T9: < and > operators
  total := total + 1
  if ← check "T9: < operator"
    "#if 2 < 5\nLT\n#else\nGE\n#endif\n"
    ["LT"] then passed := passed + 1

  -- T10: >= operator
  total := total + 1
  if ← check "T10: >= operator"
    "#if 5 >= 5\nGEQ\n#else\nLT\n#endif\n"
    ["GEQ"] then passed := passed + 1

  -- T11: Lua pattern — #if TYPE == INT, #elif TYPE == LONGLONG, #else #error
  total := total + 1
  if ← check "T11: Lua-style int type selection"
    ("#define LUA_INT_INT 1\n#define LUA_INT_LONGLONG 3\n" ++
     "#define LUA_INT_DEFAULT LUA_INT_LONGLONG\n" ++
     "#define LUA_INT_TYPE LUA_INT_DEFAULT\n" ++
     "#if LUA_INT_TYPE == LUA_INT_INT\nINT\n" ++
     "#elif LUA_INT_TYPE == LUA_INT_LONGLONG\nLONGLONG\n" ++
     "#else\nFALLBACK\n#endif\n")
    ["LONGLONG"] then passed := passed + 1

  -- T12: #if with defined() inside comparison should not misparse
  total := total + 1
  if ← check "T12: defined() still works"
    "#define FOO 1\n#if defined(FOO)\nYES\n#else\nNO\n#endif\n"
    ["YES"] then passed := passed + 1

  IO.println s!"═══════════════════════════════════════"
  IO.println s!"  #elif tests: {passed}/{total} passed"
  IO.println s!"═══════════════════════════════════════"
  return if passed == total then 0 else 1
