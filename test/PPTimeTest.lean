import CCC
open CCC.Preprocess
def main : IO UInt32 := do
  IO.println "Starting preprocess..."
  let raw ← IO.FS.readFile "/tmp/lua-5.4.7/src/lapi.c"
  IO.println s!"Read {raw.length} chars"
  let pp ← preprocess raw "/tmp/lua-5.4.7/src"
  IO.println s!"Done: {pp.length} chars"
  pure 0
