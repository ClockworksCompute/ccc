/-
  test/FuncPtrTest.lean — Function pointer / indirect call regression
  tests (FEL-68).

  Three related bugs fixed together, all discovered by trying to compile
  the plain callback-parameter idiom real C libraries use constantly
  (zlib's `alloc_func`/`free_func`, qsort comparators, dispatch tables):

  1. A bare function name used as a value (`op_t p = add;`) failed
     emission OUTRIGHT with "unknown variable 'add'" — functions were
     never registered anywhere `emitArmExpr`/`emitArmLValueAddr` looked
     up variable names. Fixed by falling back to `funcParamTypes`
     (already built program-wide for the AAPCS64 stack-args work) and
     treating a match as function-to-pointer decay (the same rule C
     already applies for arrays-to-pointer): emit the function's address.

  2. `f(x, y)` where `f` is a LOCAL variable (a parameter or local)
     holding a function pointer is syntactically indistinguishable at
     parse time from a direct call to a top-level function named `f`
     (`parsePostfix`'s `.lparen` case only special-cases an explicit
     `(*fp)(...)` deref as an indirect call) — so it always compiled to
     a direct `bl _f`, which either linked to an unrelated same-named
     global function or failed to link at all ("symbol not found").
     Fixed in `emitArmCall` by checking whether `fn` is a local variable
     first, and treating it as an indirect call if so.

  3. Once (1) and (2) let indirect calls with real arguments actually
     execute, they computed the WRONG VALUE: both the pre-existing
     `.callFnPtr` codegen (`(*fp)(...)`) and the new indirect-call path
     from (2) evaluated the function-pointer expression into `x0` AFTER
     already popping argument values into `x0..xN` — silently
     overwriting the first argument with the function's address right
     before the branch. Fixed by pushing the function-pointer value
     first (before any argument), and popping it into a scratch register
     (`x9`, not `x0`) only after all argument registers are populated.

  Three further follow-up bugs, found immediately after by trying the
  next-most-common function-pointer idioms:

  4. The verifier's pointer-safety check never resolved typedefs before
     classifying a variable's type, so `(*p)(...)` on a `typedef`'d
     function-pointer type was rejected OUTRIGHT as "Dereference of
     non-pointer variable" — a false positive on ordinary, valid code.
     Fixed in `PointerSafety.checkDereferenceable` by resolving typedefs
     first and treating `.funcPtr` as always dereferenceable.

  5. Once (4) stopped rejecting it, `(*p)(...)` still crashed (confirmed
     SIGBUS) at RUNTIME: the generic `.deref` codegen unconditionally
     read memory AT the address held by `p` — correct for an ordinary
     pointer, but dereferencing a FUNCTION pointer is a no-op in C (`*p`
     and `p` denote the same function), so this read the target
     function's own CODE BYTES as data and branched into that garbage.
     Fixed by making `.deref` a no-op when the operand's type resolves
     to `.funcPtr`.

  6. A GLOBAL variable holding a function pointer, called directly by
     name (`global_op(1, 2, 3)`), used to compile AND link successfully
     — Mach-O doesn't distinguish symbol kinds for a plain `bl`, so
     branching to a global variable's data symbol just works, in the
     sense of not erroring — but crash at runtime for two independent,
     stacked reasons: `emitArmCall` only recognized LOCAL variables as
     indirect-call targets (fixed by also checking `globalNames`), and
     the global's own initializer (`= add3`, a bare function name) was
     silently stored as a null pointer by the global-initializer
     emitter, which only understood integer/char literal initializers
     (fixed by recognizing a known function name and emitting a real
     `.quad _name` symbol reference).

  (4) is a verifier-level fix, so it is covered separately, directly
  against `Verify.verifyProgramReport`, in `test/VerifierFixesTest.lean`
  (`FEL68_funcptr_deref_of_typedef_not_flagged`) rather than here.

  Compile C → AArch64 assembly (via `emitProgramAArch64`, bypassing the
  verifier — matches the established FEL-68 test pattern) → assemble →
  link → run → check exit code. Cross-checked directly against `cc`
  compiling the identical source.
-/
import CCC

open CCC CCC.Syntax CCC.Emit CCC.Parse CCC.Preprocess

def fnptrCompileToArm (src : String) : IO (Except String String) := do
  let pp ← preprocess src "."
  match parseProgram pp with
  | .error e => pure (.error s!"parse error: {e}")
  | .ok prog => pure (emitProgramAArch64 prog)

def fnptrAssembleAndRun (asm : String) (testName : String) : IO UInt32 := do
  let asmPath := s!"/tmp/ccc_fnptr_{testName}.s"
  let objPath := s!"/tmp/ccc_fnptr_{testName}.o"
  let binPath := s!"/tmp/ccc_fnptr_{testName}"
  IO.FS.writeFile asmPath asm
  let asOut ← IO.Process.output { cmd := "as", args := #["-o", objPath, asmPath] }
  if asOut.exitCode != 0 then
    throw <| IO.userError s!"assembly failed for {testName}:\n{asOut.stderr}"
  let ccOut ← IO.Process.output { cmd := "cc", args := #["-o", binPath, objPath] }
  if ccOut.exitCode != 0 then
    throw <| IO.userError s!"linker error for {testName}:\n{ccOut.stderr}"
  let runOut ← IO.Process.output { cmd := binPath, args := #[] }
  pure runOut.exitCode

def expectExit (name : String) (src : String) (expected : UInt32) : IO Bool := do
  match ← fnptrCompileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compile error: {e}"
      pure false
  | .ok asm =>
      try
        let exitCode ← fnptrAssembleAndRun asm name
        if exitCode == expected then
          IO.println s!"✓ {name}: exit code {exitCode} (expected {expected})"
          pure true
        else
          IO.eprintln s!"✗ {name}: exit code {exitCode}, expected {expected}"
          pure false
      catch e =>
        IO.eprintln s!"✗ {name}: {e}"
        pure false

def expectExitMatchesCc (name : String) (src : String) : IO Bool := do
  match ← fnptrCompileToArm src with
  | .error e =>
      IO.eprintln s!"✗ {name}: compile error: {e}"
      pure false
  | .ok asm =>
      try
        let cccExit ← fnptrAssembleAndRun asm name
        let srcPath := s!"/tmp/ccc_fnptr_{name}_cc_ref.c"
        let ccBin := s!"/tmp/ccc_fnptr_{name}_cc_ref_bin"
        IO.FS.writeFile srcPath src
        let ccCompile ← IO.Process.output { cmd := "cc", args := #["-o", ccBin, srcPath] }
        if ccCompile.exitCode != 0 then
          IO.eprintln s!"✗ {name}: cc failed to compile the reference:\n{ccCompile.stderr}"
          pure false
        else
          let ccRun ← IO.Process.output { cmd := ccBin, args := #[] }
          if cccExit == ccRun.exitCode then
            IO.println s!"✓ {name}: CCC={cccExit}, cc={ccRun.exitCode} (agree)"
            pure true
          else
            IO.eprintln s!"✗ {name}: CCC={cccExit}, cc={ccRun.exitCode} (disagree!)"
            pure false
      catch e =>
        IO.eprintln s!"✗ {name}: {e}"
        pure false

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════"
  IO.println "  Function pointer / indirect call tests (FEL-68)"
  IO.println "═══════════════════════════════════════════"
  let mut pass : Nat := 0
  let mut total : Nat := 0

  -- The core severity check: a bare function name assigned to a
  -- function-pointer-typed local and then CALLED THROUGH THAT LOCAL
  -- used to fail emission outright with "unknown variable".
  total := total + 1
  if ← expectExit "fnptr_basic_callback_param"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int sub(int a, int b) { return a - b; }\n" ++
     "typedef int (*op_t)(int, int);\n" ++
     "int apply(op_t f, int x, int y) { return f(x, y); }\n" ++
     "int main() {\n" ++
     "  op_t p = add;\n" ++
     "  int r1 = apply(p, 3, 4);\n" ++
     "  op_t q = sub;\n" ++
     "  int r2 = q(10, 3);\n" ++
     "  return r1 + r2;\n" ++
     "}\n")
    14
  then pass := pass + 1

  total := total + 1
  if ← expectExitMatchesCc "fnptr_basic_callback_param_matches_cc"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int sub(int a, int b) { return a - b; }\n" ++
     "typedef int (*op_t)(int, int);\n" ++
     "int apply(op_t f, int x, int y) { return f(x, y); }\n" ++
     "int main() {\n" ++
     "  op_t p = add;\n" ++
     "  int r1 = apply(p, 3, 4);\n" ++
     "  op_t q = sub;\n" ++
     "  int r2 = q(10, 3);\n" ++
     "  return r1 + r2;\n" ++
     "}\n")
  then pass := pass + 1

  -- The register-clobber check: BEFORE the fix, evaluating the
  -- function-pointer expression into x0 right before `blr` silently
  -- overwrote the already-evaluated first argument, so this would have
  -- run without crashing but returned a WRONG value.
  total := total + 1
  if ← expectExit "fnptr_args_not_clobbered"
    ("int add3(int a, int b, int c) { return a + b + c; }\n" ++
     "typedef int (*op3_t)(int, int, int);\n" ++
     "int apply3(op3_t f, int a, int b, int c) { return f(a, b, c); }\n" ++
     "int main() { return apply3(add3, 100, 20, 3); }\n")
    123
  then pass := pass + 1

  -- Dispatch-table pattern: an array of function pointers indexed at
  -- runtime and called -- this is real C's most common use of function
  -- pointers (zlib-class callback tables), and exercises the SAME
  -- register-clobber bug through the pre-existing `.callFnPtr` codegen
  -- path (`ops[idx](x, y)` parses with an `.index` base, not `.var`, so
  -- it never goes through `emitArmCall`'s new local-variable check).
  total := total + 1
  if ← expectExit "fnptr_dispatch_table"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int sub(int a, int b) { return a - b; }\n" ++
     "int mul(int a, int b) { return a * b; }\n" ++
     "typedef int (*op_t)(int, int);\n" ++
     "int dispatch(op_t ops[], int idx, int x, int y) { return ops[idx](x, y); }\n" ++
     "int main() {\n" ++
     "  op_t table[3];\n" ++
     "  table[0] = add;\n" ++
     "  table[1] = sub;\n" ++
     "  table[2] = mul;\n" ++
     "  return dispatch(table, 0, 3, 4) + dispatch(table, 1, 10, 3) + dispatch(table, 2, 2, 5);\n" ++
     "}\n")
    24
  then pass := pass + 1

  total := total + 1
  if ← expectExitMatchesCc "fnptr_dispatch_table_matches_cc"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int sub(int a, int b) { return a - b; }\n" ++
     "int mul(int a, int b) { return a * b; }\n" ++
     "typedef int (*op_t)(int, int);\n" ++
     "int dispatch(op_t ops[], int idx, int x, int y) { return ops[idx](x, y); }\n" ++
     "int main() {\n" ++
     "  op_t table[3];\n" ++
     "  table[0] = add;\n" ++
     "  table[1] = sub;\n" ++
     "  table[2] = mul;\n" ++
     "  return dispatch(table, 0, 3, 4) + dispatch(table, 1, 10, 3) + dispatch(table, 2, 2, 5);\n" ++
     "}\n")
  then pass := pass + 1

  -- A plain program with no function pointers at all must be completely
  -- unaffected by the new `emitArmCall` local-variable check.
  total := total + 1
  if ← expectExit "fnptr_ordinary_calls_unaffected"
    ("int add(int a, int b) { return a + b; }\n" ++
     "int main() { return add(2, 3) + add(10, 20); }\n")
    35
  then pass := pass + 1

  -- FEL-68 follow-up #1: the verifier's pointer-safety check didn't
  -- resolve typedefs before deciding whether a name was pointer-typed,
  -- so `(*p)(...)` where `p`'s declared type was a TYPEDEF'D function
  -- pointer (`typedef int (*op3_t)(int,int,int);`) was rejected
  -- OUTRIGHT as a "Dereference of non-pointer variable" violation --
  -- for perfectly valid, common code. This must now verify clean.
  total := total + 1
  if ← expectExit "fnptr_explicit_deref_call"
    ("int add3(int a, int b, int c) { return a + b + c; }\n" ++
     "typedef int (*op3_t)(int, int, int);\n" ++
     "int main() {\n  op3_t p = add3;\n  return (*p)(1, 2, 3);\n}\n")
    6
  then pass := pass + 1

  total := total + 1
  if ← expectExitMatchesCc "fnptr_explicit_deref_call_matches_cc"
    ("int add3(int a, int b, int c) { return a + b + c; }\n" ++
     "typedef int (*op3_t)(int, int, int);\n" ++
     "int main() {\n  op3_t p = add3;\n  return (*p)(1, 2, 3);\n}\n")
  then pass := pass + 1

  -- FEL-68 follow-up #2: once the verifier stopped rejecting it, `(*p)`
  -- still crashed at RUNTIME (confirmed SIGBUS): the generic `.deref`
  -- codegen unconditionally read memory AT the address held by `p`,
  -- but dereferencing a function pointer is a no-op in C -- `*p` and
  -- `p` denote the same function. The generic path instead read the
  -- target FUNCTION'S CODE BYTES as data and branched into that
  -- garbage. Covered by the two cases directly above (which would
  -- still fail at this step if the codegen fix regressed).

  -- FEL-68 follow-up #3: a GLOBAL variable holding a function pointer,
  -- called directly by name, used to compile and LINK successfully
  -- (Mach-O doesn't distinguish symbol kinds for a plain `bl`) but
  -- crash at runtime for two independent reasons, both fixed here: (a)
  -- `emitArmCall` only recognized LOCAL variables as indirect-call
  -- targets, so a global's `bl _global_op` branched straight at the
  -- DATA symbol's address instead of loading the pointer value first;
  -- (b) even after (a), the global's OWN initializer (`= add3`) was a
  -- bare function name, which the global-initializer emitter didn't
  -- recognize and silently stored as a null pointer -- so the call
  -- would dereference a null function pointer instead.
  total := total + 1
  if ← expectExit "fnptr_global_variable_call"
    ("int add3(int a, int b, int c) { return a + b + c; }\n" ++
     "typedef int (*op3_t)(int, int, int);\n" ++
     "op3_t global_op = add3;\n" ++
     "int main() { return global_op(1, 2, 3); }\n")
    6
  then pass := pass + 1

  total := total + 1
  if ← expectExitMatchesCc "fnptr_global_variable_call_matches_cc"
    ("int add3(int a, int b, int c) { return a + b + c; }\n" ++
     "typedef int (*op3_t)(int, int, int);\n" ++
     "op3_t global_op = add3;\n" ++
     "int main() { return global_op(1, 2, 3); }\n")
  then pass := pass + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Function pointer tests: {pass}/{total} passed"
  IO.println "═══════════════════════════════════════════"
  if pass == total then pure 0 else pure 1
