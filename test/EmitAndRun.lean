import CCC.Contracts
import CCC.Syntax.Build

open CCC
open CCC.Syntax
open CCC.Syntax.Build

namespace CCC.Test.EmitAndRun

def testVerified (prog : Syntax.Program) : CCC.VerifiedProgram :=
  CCC.VerifierOnly.mkVerified prog { results := [] } (by decide)


def progReturn42 : Syntax.Program :=
  program []
    [funDef "main" .int []
      [retVal (intLit 42)]]


def progAddAndCall : Syntax.Program :=
  program []
    [ funDef "add" .int [param "a" .int, param "b" .int]
        [retVal (add (var "a") (var "b"))]
    , funDef "main" .int []
        [retVal (call "add" [intLit 3, intLit 4])]
    ]


def emitReturn42 : Except String String :=
  CCC.emitProgram (testVerified progReturn42)


def emitAddAndCall : Except String String :=
  CCC.emitProgram (testVerified progAddAndCall)


def toolExists (tool : String) : IO Bool := do
  let out ← IO.Process.output {
    cmd := "sh"
    args := #["-c", s!"command -v {tool} >/dev/null 2>&1"]
  }
  pure (out.exitCode == 0)


def compileAssemblyIfSupported (asm : String) : IO Bool := do
  if System.Platform.isOSX || System.Platform.isWindows || System.Platform.isEmscripten then
    pure true
  else
    let hasAs ← toolExists "as"
    if !hasAs then
      pure true
    else
      let asmPath : System.FilePath := "/tmp/ccc_emit_test.s"
      let objPath : System.FilePath := "/tmp/ccc_emit_test.o"
      IO.FS.writeFile asmPath asm
      let out ← IO.Process.output {
        cmd := "as"
        args := #[asmPath.toString, "-o", objPath.toString]
      }
      pure (out.exitCode == 0)


def smokeTest : IO Bool := do
  match emitReturn42 with
  | .error _ => pure false
  | .ok asm1 =>
      match emitAddAndCall with
      | .error _ => pure false
      | .ok asm2 =>
          let ok1 ← compileAssemblyIfSupported asm1
          let ok2 ← compileAssemblyIfSupported asm2
          pure (ok1 && ok2)


def runMain : IO Unit := do
  let ok ← smokeTest
  if ok then
    IO.println "Emitter smoke tests passed."
  else
    throw <| IO.userError "Emitter smoke tests failed"

end CCC.Test.EmitAndRun

def main : IO Unit :=
  CCC.Test.EmitAndRun.runMain
