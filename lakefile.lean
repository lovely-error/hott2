import Lake
open Lake DSL

package «simptt» where
  -- add package configuration options here

lean_lib «Simptt» where
  -- add library configuration options here

@[default_target]
lean_exe «simptt» where
  root := `Main
