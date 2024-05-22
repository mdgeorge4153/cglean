import Lake
open Lake DSL

package cglean

@[default_target]
lean_lib CGLean

require mathlib from git
    "https://github.com/leanprover-community/mathlib4" @ "v4.8.0-rc1"

require leancolls from git
  "https://github.com/mdgeorge4153/LeanColls.git" @ "lean-4.8"

require ray from git
  "https://github.com/girving/ray.git" @ "lean-4.8"

