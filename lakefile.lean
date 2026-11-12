import Lake
open Lake DSL

package «RH» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "0f18102487"

@[default_target]
lean_lib «RH»
