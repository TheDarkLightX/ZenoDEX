import Lake
open Lake DSL

package «tauswapLean» {}

-- Use a global, shared Mathlib checkout to avoid re-downloading in each project.
require mathlib from "/home/trevormoc/deps/mathlib4"

@[default_target]
lean_lib Proofs {
  roots := #[`Proofs]
}
