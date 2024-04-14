import Lake
open Lake DSL

package greeting

@[default_target]
lean_lib Greeting

require leancolls from git
  "https://github.com/JamesGallicchio/LeanColls.git" @ "main"

require ray from git
  "https://github.com/girving/ray.git" @ "main"


