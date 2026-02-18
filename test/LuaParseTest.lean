/-
  Attempt to preprocess + parse each lua 5.4 source file.
  Reports pass/fail per file with error details.
-/
import CCC

open CCC.Preprocess CCC.Parse

def tryParseLuaFile (path : String) : IO (Bool × String) := do
  let filename := (path.splitOn "/").getLast!
  let raw ← IO.FS.readFile path
  -- Determine base path for includes
  let parts := path.splitOn "/"
  let basePath := String.intercalate "/" (parts.dropLast)
  -- Preprocess
  let pp ← preprocess raw basePath
  -- Parse
  match parseProgram pp with
  | .ok prog =>
      let nFns := prog.functions.length
      let nStructs := prog.structs.length
      pure (true, s!"✓ {filename}: {nFns} fns, {nStructs} structs")
  | .error e =>
      let shortErr := e.take 100
      pure (false, s!"✗ {filename}: {shortErr}")

def main : IO UInt32 := do
  let luaSrc := "/tmp/lua-5.4.7/src"
  let srcExists ← System.FilePath.pathExists luaSrc
  if !srcExists then
    IO.eprintln "lua source not found at /tmp/lua-5.4.7/src"
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
  let mut total : Nat := 0

  for file in files do
    total := total + 1
    let (ok, msg) ← tryParseLuaFile (luaSrc ++ "/" ++ file)
    IO.println msg
    if ok then pass := pass + 1

  IO.println s!"\n═══════════════════════════════════════════"
  IO.println s!"  Lua 5.4 parse: {pass}/{total} files"
  IO.println s!"═══════════════════════════════════════════"
  pure 0  -- always exit 0 (informational)
