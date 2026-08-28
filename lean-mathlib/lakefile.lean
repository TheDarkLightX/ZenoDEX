import Lake
open Lake DSL

package «tauswapLean» {}

-- Keep mathlib out of git history; prefer a local clone/symlink at `external/mathlib4`.
require mathlib from "../external/mathlib4"

@[default_target]
lean_lib Proofs {
  roots := #[`Proofs, `MathFrontier]
}
