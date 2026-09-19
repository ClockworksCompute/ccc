/-
  test/regression/PreprocessErrorRepro.lean
  FEL-52: `#error` used to silently become a harmless comment
  (`/* CCC #error: ... */`), so a file that hit an unsupported-
  configuration guard (extremely common in real headers) "preprocessed"
  successfully and the verifier happily reported on whatever nonsense
  followed it. A real C preprocessor treats `#error` as fatal; this must
  too. `#error` inside an untaken `#if 0` branch must still be a no-op,
  matching real preprocessor semantics.

  Exercises the actual `.lake/build/bin/ccc` CLI binary (the exception is
  raised inside `Preprocess.preprocess`'s `IO` monad and propagates as an
  uncaught exception all the way out of `main`, so the CLI's own exit
  code/output is the right thing to check, not a library-level call).
  Must FAIL before the FEL-52 fix (exits 0, no mention of the error text),
  PASS after.
-/
import CCC

def runCcc (args : List String) : IO (UInt32 × String) := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/ccc", args := args.toArray }
  pure (result.exitCode, result.stdout ++ result.stderr)

def main : IO Unit := do
  let mut ok := true

  -- 1. An active `#error` must fail compilation and mention the message.
  let activePath := "/tmp/ccc_preprocess_error_repro_active.c"
  IO.FS.writeFile activePath
    ("#if 1\n" ++
     "#error \"this platform is unsupported\"\n" ++
     "#endif\n" ++
     "int main() { return 0; }\n")
  let (code1, out1) ← runCcc [activePath]
  if code1 == 0 then
    IO.eprintln s!"✗ FAIL  PreprocessErrorRepro — active #error did not fail compilation (exit 0)"
    ok := false
  else if !((out1.splitOn "this platform is unsupported").length > 1) then
    IO.eprintln s!"✗ FAIL  PreprocessErrorRepro — exit was non-zero ({code1}) but output doesn't mention the #error text:\n{out1}"
    ok := false
  else
    IO.println s!"✓ PASS  PreprocessErrorRepro — active #error correctly fails compilation (exit {code1}), message surfaced"
  IO.FS.removeFile activePath

  -- 2. An `#error` inside an untaken `#if 0` branch must be a no-op, same
  --    as a real C preprocessor -- this must NOT regress into "any #error
  --    token anywhere in the file fails", only an ACTIVE one.
  let inactivePath := "/tmp/ccc_preprocess_error_repro_inactive.c"
  IO.FS.writeFile inactivePath
    ("#if 0\n" ++
     "#error \"should never fire\"\n" ++
     "#endif\n" ++
     "int main() { return 5; }\n")
  let (code2, out2) ← runCcc [inactivePath]
  if code2 != 0 then
    IO.eprintln s!"✗ FAIL  PreprocessErrorRepro — #error inside an untaken #if 0 branch incorrectly fired (exit {code2}):\n{out2}"
    ok := false
  else
    IO.println s!"✓ PASS  PreprocessErrorRepro — #error inside an untaken #if 0 branch correctly does not fire"
  IO.FS.removeFile inactivePath

  if ok then
    IO.println "✓ PASS  PreprocessErrorRepro — all checks passed"
  else
    IO.eprintln "✗ FAIL  PreprocessErrorRepro — see failures above"
    IO.Process.exit 1
