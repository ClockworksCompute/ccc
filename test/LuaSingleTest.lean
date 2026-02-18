import CCC
open CCC.Preprocess CCC.Parse

def main (args : List String) : IO UInt32 := do
  let file := args.headD "/tmp/lua-5.4.7/src/lzio.c"
  let raw ← IO.FS.readFile file
  let parts := file.splitOn "/"
  let basePath := String.intercalate "/" (parts.dropLast)
  IO.println s!"Preprocessing {file}..."
  let pp ← preprocess raw basePath
  IO.println s!"Preprocessed: {pp.length} chars, {(pp.splitOn "\n").length} lines"
  IO.println s!"Parsing..."
  match parseProgram pp with
  | .ok prog =>
      IO.println s!"✓ Parsed: {prog.functions.length} fns, {prog.structs.length} structs"
      pure 0
  | .error e =>
      IO.println s!"✗ Parse error: {e}"
      pure 1
