namespace CCC.Emit

/-- Map source-level builtin names to C runtime shims. -/
def mapRuntimeBuiltin (fn : String) : String :=
  if fn = "malloc" then "ccc_malloc"
  else if fn = "free" then "ccc_free"
  else if fn = "memcpy" then "ccc_memcpy"
  else fn

end CCC.Emit
