import Lake
open Lake DSL

package «eileen» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "v4.14.0"
require "leanprover-community" / "aesop" @ git "master"

@[default_target]
lean_lib «Eileen» where
  -- add library configuration options here
