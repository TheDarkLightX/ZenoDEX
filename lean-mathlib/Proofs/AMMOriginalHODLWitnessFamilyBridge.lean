import Proofs.AMMOriginalHODLGlobalBridge

open Filter
open scoped Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier
namespace OriginalHODLWitnessFamilyBridge

open LocalJetFrontier.OriginalHODLBridge

noncomputable section

/-!
# Original-HODL witness-family bridge

This file packages a stronger, pair-local witness-family interface into the
checked global obstruction interface from `AMMOriginalHODLGlobalBridge`.

The point is structural rather than mathematical: if a concrete AMM family can
provide the witness data and limit laws for each admissible pair, then the
pairwise and existential impossibility theorems follow immediately.
-/

/-- A structured witness family for original-HODL concrete extraction.

This is intentionally stronger than an arbitrary raw AMM semantics model: it
stores exactly the pair-local fields that a future concrete AMM family should
prove for each admissible baseline/candidate pair.
-/
structure OriginalHODLWitnessFamily (RawAMM : Type) where
  AdmissiblePair : RawAMM → RawAMM → Prop
  coeffs : RawAMMCoefficientExtractors RawAMM
  order : RawAMM → RawAMM → ℕ
  n : RawAMM → RawAMM → ℝ
  b : RawAMM → RawAMM → ℝ
  deltaR2 : RawAMM → RawAMM → ℝ → ℝ
  deltaQ1 : RawAMM → RawAMM → ℝ → ℝ
  deltaQ2 : RawAMM → RawAMM → ℝ → ℝ
  order_pos :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        0 < order baseline candidate
  n_pos :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        0 < n baseline candidate
  b_pos :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        0 < b baseline candidate
  deltaR2_tendsto :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        Tendsto
          (fun d =>
            deltaR2 baseline candidate d /
              d ^ (firstEvenHODLExponent (order baseline candidate) - 1))
          (𝓝[≠] (0 : ℝ))
          (𝓝
            ((b baseline candidate / n baseline candidate) *
              ((firstEvenHODLExponent (order baseline candidate) : ℝ) ^ 2)))
  deltaQ1_tendsto :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        Tendsto
          (fun d =>
            deltaQ1 baseline candidate d /
              d ^ (firstEvenHODLExponent (order baseline candidate) - 1))
          (𝓝[≠] (0 : ℝ))
          (𝓝
            (-2 * (b baseline candidate / n baseline candidate) *
              (firstEvenHODLExponent (order baseline candidate) : ℝ)))
  deltaQ2_tendsto :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        Tendsto
          (fun d =>
            deltaQ2 baseline candidate d /
              d ^ (firstEvenHODLExponent (order baseline candidate) - 2))
          (𝓝[≠] (0 : ℝ))
          (𝓝
            (-2 * (b baseline candidate / n baseline candidate) *
              (firstEvenHODLExponent (order baseline candidate) : ℝ) *
              ((firstEvenHODLExponent (order baseline candidate) : ℝ) - 1)))
  slippage_delta_eq :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        FunctionDelta (coeffs.slippage candidate) (coeffs.slippage baseline) =
          TauSwap.Impossibility.OriginalHODL.hodlSlipDeltaExact
            (n baseline candidate)
            (b baseline candidate)
            (firstEvenHODLExponent (order baseline candidate))
  curvature_delta_eq :
    ∀ {baseline candidate : RawAMM},
      AdmissiblePair baseline candidate →
        FunctionDelta (coeffs.curvature candidate) (coeffs.curvature baseline) =
          originalHODLCurvatureChainDelta
            (deltaR2 baseline candidate)
            (deltaQ1 baseline candidate)
            (deltaQ2 baseline candidate)

/-- One admissible witness-family pair packages into the local original-HODL
pair certificate. -/
def OriginalHODLWitnessFamily.pairObligations
    {RawAMM : Type} (W : OriginalHODLWitnessFamily RawAMM)
    {baseline candidate : RawAMM}
    (hpair : W.AdmissiblePair baseline candidate) :
    OriginalHODLPairExpansionObligations W.coeffs baseline candidate where
  order := W.order baseline candidate
  order_pos := W.order_pos hpair
  n := W.n baseline candidate
  b := W.b baseline candidate
  n_pos := W.n_pos hpair
  b_pos := W.b_pos hpair
  deltaR2 := W.deltaR2 baseline candidate
  deltaQ1 := W.deltaQ1 baseline candidate
  deltaQ2 := W.deltaQ2 baseline candidate
  deltaR2_tendsto := W.deltaR2_tendsto hpair
  deltaQ1_tendsto := W.deltaQ1_tendsto hpair
  deltaQ2_tendsto := W.deltaQ2_tendsto hpair
  slippage_delta_eq := W.slippage_delta_eq hpair
  curvature_delta_eq := W.curvature_delta_eq hpair

/-- A structured original-HODL witness family induces the concrete extraction
semantics interface used by the checked global obstruction theorems. -/
def OriginalHODLWitnessFamily.toConcreteExtractionSemantics
    {RawAMM : Type} (W : OriginalHODLWitnessFamily RawAMM) :
    OriginalHODLConcreteExtractionSemantics RawAMM where
  AdmissiblePair := W.AdmissiblePair
  coeffs := W.coeffs
  pair_obligations := fun hpair => W.pairObligations hpair

/-- Pairwise strict-surface obstruction for the witness family. -/
theorem OriginalHODLWitnessFamily.surface_not_simultaneous_global_no_worse_with_strict
    {RawAMM : Type} (W : OriginalHODLWitnessFamily RawAMM)
    {baseline candidate : RawAMM}
    (hpair : W.AdmissiblePair baseline candidate) :
    ¬ (GloballyNoWorse
          (W.toConcreteExtractionSemantics.surface baseline candidate).candidateSlippage
          (W.toConcreteExtractionSemantics.surface baseline candidate).baselineSlippage ∧
        StrictlyBetterSomewhere
          (W.toConcreteExtractionSemantics.surface baseline candidate).candidateSlippage
          (W.toConcreteExtractionSemantics.surface baseline candidate).baselineSlippage ∧
        GloballyNoWorse
          (W.toConcreteExtractionSemantics.surface baseline candidate).candidateCurvature
          (W.toConcreteExtractionSemantics.surface baseline candidate).baselineCurvature) :=
  W.toConcreteExtractionSemantics.surface_not_simultaneous_global_no_worse_with_strict hpair

/-- Global existential obstruction for the witness family. -/
theorem OriginalHODLWitnessFamily.no_admissible_simultaneous_global_no_worse
    {RawAMM : Type} (W : OriginalHODLWitnessFamily RawAMM) :
    ¬ ∃ (baseline candidate : RawAMM),
        W.AdmissiblePair baseline candidate ∧
          GloballyNoWorse (W.coeffs.slippage candidate) (W.coeffs.slippage baseline) ∧
          GloballyNoWorse (W.coeffs.curvature candidate) (W.coeffs.curvature baseline) :=
  W.toConcreteExtractionSemantics.no_admissible_simultaneous_global_no_worse

end
end OriginalHODLWitnessFamilyBridge
end LocalJetFrontier
end Impossibility
end TauSwap
