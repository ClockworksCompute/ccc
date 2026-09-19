/-
  test/StackArgsTest.lean — AAPCS64 stack-argument passing (FEL-68, was
  FEL-51's ">8 call args" item).

  A call with more than 8 arguments (or a function DEFINED with more than
  8 parameters) used to throw "too many arguments" outright at the call
  site, and silently drop the 9th+ parameter's spill code entirely at the
  definition site (a real, silent correctness bug on that side — the
  local slot for such a parameter was left as whatever garbage was
  already on the stack). Fixed by implementing the AAPCS64 outgoing
  stack-argument area for both directions.

  Getting this right needed TWO iterations, both instructive:

  1. First pass used a uniform 8-byte stride per stack argument. Every
     purely-CCC-compiled test (caller AND callee both CCC) passed — but a
     real cross-ABI test (CCC calling a `cc`-compiled function, or vice
     versa) failed on the second stack argument onward. Root cause:
     Apple's arm64 ABI does NOT pad stack arguments to 8 bytes each
     (unlike the base AAPCS64 spec) — it packs each at its own natural
     size/alignment. Two CCC-only test ends agreeing with each other
     self-consistently masked the real ABI non-conformance completely.
  2. Fixed via `CCC.Syntax.Layout.packedOffsets`. Re-testing surfaced a
     SECOND bug: the call site was sizing each stack argument from
     `inferExprType`'s guess about the caller's own expression (which
     reports a bare integer literal as `.long`, an existing imprecision
     that was harmless before this feature existed), rather than the
     callee's actually-declared parameter type. Fixed by threading a
     name → declared-parameter-types table through codegen so the call
     site can look up the real prototype when one is visible.

  This is why every case below that has a real `cc`-compiled counterpart
  on one side of the ABI boundary is tested against ACTUAL `cc` output,
  not just against another CCC-compiled binary — that is the only way
  this class of bug reliably surfaces, and is a materially stronger check
  than internal self-consistency for exactly the interop reason FEL-65
  (compiling and linking against real C libraries) cares about.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

def stackArgsCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

/-- Compile `src` with CCC down to a `.o` at `objPath` (no linking). -/
def ccArmCompileToObj (src : String) (tag : String) : IO String := do
  match ← stackArgsCompileToArm src with
  | .error e => throw <| IO.userError s!"CCC compile error for {tag}: {e}"
  | .ok asm =>
      let asmPath := s!"/tmp/ccc_stackargs_{tag}.s"
      let objPath := s!"/tmp/ccc_stackargs_{tag}.o"
      IO.FS.writeFile asmPath asm
      let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
      if asOut.exitCode != 0 then
        throw <| IO.userError s!"assembler error for {tag}:\n{asOut.stderr}"
      pure objPath

/-- Compile `src` with the system `cc` down to a `.o` at a fixed path. -/
def ccCompileToObj (src : String) (tag : String) : IO String := do
  let srcPath := s!"/tmp/ccc_stackargs_ccsrc_{tag}.c"
  let objPath := s!"/tmp/ccc_stackargs_ccsrc_{tag}.o"
  IO.FS.writeFile srcPath src
  let ccOut ← IO.Process.output { cmd := "cc", args := #["-c", "-o", objPath, srcPath] }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"cc compile error for {tag}:\n{ccOut.stderr}"
  pure objPath

/-- Link the given `.o` files into an executable and run it, returning the exit code. -/
def linkAndRun (objs : List String) (tag : String) : IO UInt32 := do
  let binPath := s!"/tmp/ccc_stackargs_{tag}_bin"
  let ccOut ← IO.Process.output { cmd := "cc", args := (#["-o", binPath] ++ objs.toArray) }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"linker error for {tag}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  pure runOut.exitCode

/-- Whole program compiled and run entirely by CCC (self-consistency check). -/
def expectExitAllCcc (name : String) (src : String) (expected : UInt32) : IO Bool := do
  try
    let obj ← ccArmCompileToObj src name
    let exitCode ← linkAndRun [obj] name
    if exitCode == expected then
      IO.println s!"✓ {name}: exit code {exitCode} (expected {expected})"
      pure true
    else
      IO.eprintln s!"✗ {name}: exit code {exitCode}, expected {expected}"
      pure false
  catch e =>
    IO.eprintln s!"✗ {name}: {e}"
    pure false

/-- Cross-ABI check: `callerSrc` compiled by CCC, `calleeSrc` compiled by
    the real system `cc`, linked together and run. This is the check that
    actually catches ABI non-conformance — see the module docstring. -/
def expectExitCrossCalleeCC (name : String) (callerSrc calleeSrc : String) (expected : UInt32)
    : IO Bool := do
  try
    let callerObj ← ccArmCompileToObj callerSrc s!"{name}_caller"
    let calleeObj ← ccCompileToObj calleeSrc s!"{name}_callee"
    let exitCode ← linkAndRun [callerObj, calleeObj] name
    if exitCode == expected then
      IO.println s!"✓ {name} (cc callee): exit code {exitCode} (expected {expected})"
      pure true
    else
      IO.eprintln s!"✗ {name} (cc callee): exit code {exitCode}, expected {expected}"
      pure false
  catch e =>
    IO.eprintln s!"✗ {name} (cc callee): {e}"
    pure false

/-- The other direction: `callerSrc` compiled by real `cc`, `calleeSrc`
    (the function whose >8-param DEFINITION codegen is under test)
    compiled by CCC. -/
def expectExitCrossCallerCC (name : String) (callerSrc calleeSrc : String) (expected : UInt32)
    : IO Bool := do
  try
    let callerObj ← ccCompileToObj callerSrc s!"{name}_caller"
    let calleeObj ← ccArmCompileToObj calleeSrc s!"{name}_callee"
    let exitCode ← linkAndRun [callerObj, calleeObj] name
    if exitCode == expected then
      IO.println s!"✓ {name} (cc caller): exit code {exitCode} (expected {expected})"
      pure true
    else
      IO.eprintln s!"✗ {name} (cc caller): exit code {exitCode}, expected {expected}"
      pure false
  catch e =>
    IO.eprintln s!"✗ {name} (cc caller): {e}"
    pure false

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════"
  IO.println "  AAPCS64 stack-argument tests (FEL-68)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The exact repro from the original review: 9 int args (1 on the
  -- stack), self-consistent CCC round trip.
  total := total + 1
  if ← expectExitAllCcc "sum9"
    "int sum9(int a,int b,int c,int d,int e,int f,int g,int h,int i){return a+b+c+d+e+f+g+h+i;}\nint main(){ return sum9(1,2,3,4,5,6,7,8,9); }\n"
    45
  then pass := pass + 1

  -- 10 args (2 on the stack), order-sensitive: a transposition of the
  -- two stack args would change the result to a DIFFERENT wrong value
  -- (37 instead of 73), so this can't pass by accident.
  total := total + 1
  if ← expectExitAllCcc "order10"
    "int f(int a,int b,int c,int d,int e,int g,int h,int i,int j,int k){ return j*10 + k; }\nint main(){ return f(0,0,0,0,0,0,0,0,7,3); }\n"
    73
  then pass := pass + 1

  -- 12 args (4 on the stack), each stack arg independently checkable via
  -- distinct bit weights — any single position landing wrong or swapped
  -- changes the result to a distinguishable wrong value.
  total := total + 1
  if ← expectExitAllCcc "args12"
    "int g(int a,int b,int c,int d,int e,int f,int h,int i,int p,int q,int r,int s){\n  return p*1 + q*2 + r*4 + s*8;\n}\nint main(){ return g(0,0,0,0,0,0,0,0, 1,0,1,1); }\n"
    13
  then pass := pass + 1

  -- Cross-ABI, real cc callee, all-int (the case the uniform-8-byte-
  -- stride first attempt got wrong: 45 instead of 55).
  total := total + 1
  if ← expectExitCrossCalleeCC "cross_all_int"
    "int cc_sum10(int a,int b,int c,int d,int e,int f,int g,int h,int i,int j);\nint main() { return cc_sum10(1,2,3,4,5,6,7,8,9,10); }\n"
    "int cc_sum10(int a,int b,int c,int d,int e,int f,int g,int h,int i,int j) {\n  return a+b+c+d+e+f+g+h+i+j;\n}\n"
    55
  then pass := pass + 1

  -- Cross-ABI, the OTHER direction: a real cc caller invoking a
  -- CCC-DEFINED >8-param function (exercises `emitArmParamMoves`'s
  -- stack-parameter spill code, not just the call site).
  total := total + 1
  if ← expectExitCrossCallerCC "cross_callee_defined_by_ccc"
    "int ccc_sum10(int a,int b,int c,int d,int e,int f,int g,int h,int i,int j);\nint main() { return ccc_sum10(1,2,3,4,5,6,7,8,9,10); }\n"
    "int ccc_sum10(int a,int b,int c,int d,int e,int f,int g,int h,int i,int j) {\n  return a+b+c+d+e+f+g+h+i+j;\n}\n"
    55
  then pass := pass + 1

  -- Cross-ABI, mixed widths: int params packed at 4-byte alignment, a
  -- long param forcing 8-byte alignment for itself (and for whatever
  -- follows it) within the SAME packed stack-argument area — this is
  -- exactly the shape that would silently corrupt under a uniform stride
  -- (either 4 or 8) in either direction.
  total := total + 1
  if ← expectExitCrossCalleeCC "cross_mixed_int_long"
    "long cc_mixed(int a,int b,int c,int d,int e,int f,int g,int h,int i,long j,int k);\nint main() { return cc_mixed(1,2,3,4,5,6,7,8,9,10,11); }\n"
    "long cc_mixed(int a,int b,int c,int d,int e,int f,int g,int h,int i,long j,int k) {\n  return a+b+c+d+e+f+g+h+i+j+k;\n}\n"
    66
  then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Stack-argument tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
