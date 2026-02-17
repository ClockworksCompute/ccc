import Lake
open Lake DSL

package ccc where
  moreLeanArgs := #["-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]

@[default_target]
lean_lib CCC where
  roots := #[`CCC]

lean_exe ccc where
  root := `Main
