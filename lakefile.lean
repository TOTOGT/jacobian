import Lake
open Lake DSL

package «jacobian» {
  -- Add any package configuration options here
}

@[default_target]
lean_lib «Jacobian» {
  -- Add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
