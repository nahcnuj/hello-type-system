import Lake
open Lake DSL

package «HelloTypeSystem» where
  -- add package configuration options here

lean_lib «HelloTypeSystem» where
  -- add library configuration options here

@[default_target]
lean_exe «hellotypesystem» where
  root := `Main

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "1daa0de7eea6bf8d3e1b0814156ede21a8a9e9e9" -- "main"
