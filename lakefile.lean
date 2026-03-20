import Lake
open Lake DSL

package «TPC» where
  name := "TPC"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «TPC» where
  roots := #[`TPC]
