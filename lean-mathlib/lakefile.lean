import Lake
open Lake DSL

package «tauswapLean» {}

require mathlib from "../external/mathlib4"

@[default_target]
lean_lib Proofs {
  roots := #[`Proofs]
}
