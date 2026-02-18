/-
  LuaScoreTest.lean — Scoring harness for Lua 5.4 parse parity.
  Gate test: all 34 files must parse. Regression guard.
-/
import CCC

open CCC.Preprocess CCC.Parse

def tryParseLuaFile (path : String) : IO (Bool × String) := do
  let filename := (path.splitOn "/").getLast!
  let raw ← IO.FS.readFile path
  let parts := path.splitOn "/"
  let basePath := String.intercalate "/" (parts.dropLast)
  let pp ← preprocess raw basePath
  match parseProgram pp with
  | .ok prog =>
      let nFns := prog.functions.length
      pure (true, s!"✓ {filename}: {nFns} fns")
  | .error e =>
      let shortErr := e.take 120
      pure (false, s!"✗ {filename}: {shortErr}")

def main : IO UInt32 := do
  let luaSrc := "/tmp/lua-5.4.7/src"
  let srcExists ← System.FilePath.pathExists luaSrc
  if !srcExists then
    IO.eprintln "ERROR: lua source not found at /tmp/lua-5.4.7/src"
    return 1

  let files := #[
    "lapi.c", "lauxlib.c", "lbaselib.c", "lcode.c", "lcorolib.c",
    "lctype.c", "ldblib.c", "ldebug.c", "ldo.c", "ldump.c",
    "lfunc.c", "lgc.c", "linit.c", "liolib.c", "llex.c",
    "lmathlib.c", "lmem.c", "loadlib.c", "lobject.c", "lopcodes.c",
    "loslib.c", "lparser.c", "lstate.c", "lstring.c", "lstrlib.c",
    "ltable.c", "ltablib.c", "ltm.c", "lua.c", "luac.c",
    "lundump.c", "lutf8lib.c", "lvm.c", "lzio.c"
  ]

  let mut pass : Nat := 0
  let mut fail : Nat := 0

  for file in files do
    let (ok, msg) ← tryParseLuaFile (luaSrc ++ "/" ++ file)
    IO.println msg
    if ok then pass := pass + 1
    else fail := fail + 1

  IO.println ""
  IO.println "═══════════════════════════════════════════"
  IO.println s!"  Lua 5.4 parse: {pass}/{pass + fail} files"
  IO.println "═══════════════════════════════════════════"

  if pass < 34 then
    IO.eprintln s!"GATE FAILED: expected 34/34, got {pass}/{pass + fail}"
    return 1
  else
    IO.println "GATE PASSED: 34/34 ✓"
    return 0
