import Proofs.AMMGlobalCounterexamples

/-!
# AMM global boundary countermodels

This file records the boundary around the global AMM tradeoff theorem.

The checked obstruction theorems in `AMMGlobalCounterexamples` require a
same-benchmark analytic extraction object. If that extraction requirement is
dropped and one quantifies over arbitrary coefficient surfaces, simultaneous
dominance is trivial. This is negative knowledge: it does not exhibit a valid
AMM, but it proves why the raw-AMM realizability bridge is load-bearing.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- A coefficient surface that is deliberately not claimed to come from any
valid AMM semantics. It exists only to mark the assumption boundary. -/
def arbitraryDominatingCoefficientSurface : AMMCoefficientSurface where
  baselineSlippage := fun _ => 1
  candidateSlippage := fun _ => 0
  baselineCurvature := fun _ => 1
  candidateCurvature := fun _ => 0

/-- Without same-benchmark analytic extraction assumptions, arbitrary
coefficient surfaces can be globally better in both coordinates. -/
theorem arbitrary_coefficient_surfaces_admit_simultaneous_strict_dominance :
    ∃ F : AMMCoefficientSurface,
      GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
        StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
        GloballyNoWorse F.candidateCurvature F.baselineCurvature ∧
        StrictlyBetterSomewhere F.candidateCurvature F.baselineCurvature := by
  refine ⟨arbitraryDominatingCoefficientSurface, ?_, ?_, ?_, ?_⟩
  · intro d
    norm_num [arbitraryDominatingCoefficientSurface]
  · exact ⟨0, by norm_num [arbitraryDominatingCoefficientSurface]⟩
  · intro d
    norm_num [arbitraryDominatingCoefficientSurface]
  · exact ⟨0, by norm_num [arbitraryDominatingCoefficientSurface]⟩

/-- The universal obstruction theorem is false for unconstrained coefficient
surfaces. A valid global AMM theorem must therefore prove that admissible raw
AMMs realize only surfaces satisfying the extraction assumptions, or else find
a valid AMM outside that class. -/
theorem not_universal_over_unconstrained_coefficient_surfaces :
    ¬ ∀ F : AMMCoefficientSurface,
      ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
          StrictlyBetterSomewhere F.candidateSlippage F.baselineSlippage ∧
          GloballyNoWorse F.candidateCurvature F.baselineCurvature) := by
  intro h
  rcases arbitrary_coefficient_surfaces_admit_simultaneous_strict_dominance with
    ⟨F, hslip, hstrict, hcurv, _hcurvStrict⟩
  exact h F ⟨hslip, hstrict, hcurv⟩

end
end LocalJetFrontier
end Impossibility
end TauSwap
