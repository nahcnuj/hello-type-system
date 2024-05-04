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
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "a34d3c1f7b72654c08abe5741d94794db40dbb2e" -- "main"
