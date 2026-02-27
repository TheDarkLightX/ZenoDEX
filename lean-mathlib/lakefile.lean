import Lake
open Lake DSL

package «tauswapLean» {}

require mathlib from "/home/trevormoc/deps/mathlib4"

@[default_target]
lean_lib Proofs {
  roots := #[`Proofs]
}
