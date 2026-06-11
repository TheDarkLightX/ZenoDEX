import Proofs
open Proofs.PokayokeImpactGate

example : impactOnlyAction 500 = ImpactAction.typedConfirm := by
  exact impactOnlyAction_of_ge_500 500 (by native_decide)

example : severity (impactOnlyAction 99) ≤ severity (impactOnlyAction 500) := by
  exact severity_impactOnlyAction_monotone 99 500 (by native_decide)
