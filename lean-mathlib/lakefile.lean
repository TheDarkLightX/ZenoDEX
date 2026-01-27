import Lake
open Lake DSL

package «tauswapLean» {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib Proofs {
  roots := #[`Proofs]
}
