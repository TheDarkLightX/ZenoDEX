import Proofs.AMMGlobalCounterexamples
import Proofs.AMMOriginalHODLNormalizedFunctionBridge

/-!
# Original-HODL normalized surface bridge

This file packages the concrete normalized power-family comparison into the
common `AMMCoefficientSurface` type used by the repo's global obstruction APIs.

The purpose is narrow: we already know the local normalized function packet and
its obstruction theorems. This file makes that concrete comparison available on
the shared surface type so later semantic transport theorems can target one
surface representation.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Forget the extra normalized-pair data and retain only the shared coefficient
surface. -/
def NormalizedFunctionPair.toSurface (P : NormalizedFunctionPair) : AMMCoefficientSurface where
  baselineSlippage := P.baselineSlippage
  candidateSlippage := P.candidateSlippage
  baselineCurvature := P.baselineCurvature
  candidateCurvature := P.candidateCurvature

/-- On the shared surface, the slippage delta is exactly the packaged local
slippage delta. -/
theorem NormalizedFunctionPair.slippage_delta_eq_toSurface
    (P : NormalizedFunctionPair) :
    P.pair.slippage.delta = (P.toSurface).slipDelta := by
  funext d
  change P.pair.slippage.delta d = P.candidateSlippage d - P.baselineSlippage d
  simpa [NormalizedFunctionPair.toSurface, AMMCoefficientSurface.slipDelta, FunctionDelta]
    using congrFun P.slippage_delta_eq d

/-- On the shared surface, the curvature delta is exactly the packaged local
curvature delta. -/
theorem NormalizedFunctionPair.curvature_delta_eq_toSurface
    (P : NormalizedFunctionPair) :
    P.pair.curvature.delta = (P.toSurface).curvDelta := by
  funext d
  change P.pair.curvature.delta d = P.candidateCurvature d - P.baselineCurvature d
  simpa [NormalizedFunctionPair.toSurface, AMMCoefficientSurface.curvDelta, FunctionDelta]
    using congrFun P.curvature_delta_eq d

/-- Shared-surface assumption for a local regime where both deltas are
strictly positive at some point. -/
structure LocalJointPositiveSurfaceAssumptions
    (F : AMMCoefficientSurface) : Prop where
  witness : LocalJointPositiveWitness F.slipDelta F.curvDelta

/-- Shared-surface assumption for a local slippage/curvature tradeoff
regime. -/
structure LocalTradeoffSurfaceAssumptions
    (F : AMMCoefficientSurface) : Prop where
  witness : LocalTradeoffWitness F.slipDelta F.curvDelta

/-- A local joint-positive surface witness refutes global no-worse in both
coordinates on the shared surface. -/
theorem LocalJointPositiveSurfaceAssumptions.componentwise_obstruction
    {F : AMMCoefficientSurface}
    (A : LocalJointPositiveSurfaceAssumptions F) :
    (¬ GloballyNoWorse F.candidateSlippage F.baselineSlippage) ∧
      (¬ GloballyNoWorse F.candidateCurvature F.baselineCurvature) :=
  LocalJointPositiveWitness.function_level_obstruction
    (candidateSlippage := F.candidateSlippage)
    (baselineSlippage := F.baselineSlippage)
    (candidateCurvature := F.candidateCurvature)
    (baselineCurvature := F.baselineCurvature)
    (hslip_eq := by
      funext d
      rfl)
    (hcurv_eq := by
      funext d
      rfl)
    A.witness

/-- Conjunction form of the same shared-surface obstruction. -/
theorem LocalJointPositiveSurfaceAssumptions.not_simultaneous_global_no_worse
    {F : AMMCoefficientSurface}
    (A : LocalJointPositiveSurfaceAssumptions F) :
    ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
        GloballyNoWorse F.candidateCurvature F.baselineCurvature) := by
  intro h
  exact (A.componentwise_obstruction).1 h.1

/-- A local tradeoff surface witness refutes global no-worse in slippage and
the reversed curvature dominance claim on the shared surface. -/
theorem LocalTradeoffSurfaceAssumptions.componentwise_tradeoff
    {F : AMMCoefficientSurface}
    (A : LocalTradeoffSurfaceAssumptions F) :
    (¬ GloballyNoWorse F.candidateSlippage F.baselineSlippage) ∧
      (¬ GloballyNoWorse F.baselineCurvature F.candidateCurvature) :=
  LocalTradeoffWitness.function_level_tradeoff
    (candidateSlippage := F.candidateSlippage)
    (baselineSlippage := F.baselineSlippage)
    (candidateCurvature := F.candidateCurvature)
    (baselineCurvature := F.baselineCurvature)
    (hslip_eq := by
      funext d
      rfl)
    (hcurv_eq := by
      funext d
      rfl)
    A.witness

/-- Conjunction form of the shared-surface tradeoff obstruction. -/
theorem LocalTradeoffSurfaceAssumptions.not_slippage_no_worse_and_baseline_curvature_no_worse
    {F : AMMCoefficientSurface}
    (A : LocalTradeoffSurfaceAssumptions F) :
    ¬ (GloballyNoWorse F.candidateSlippage F.baselineSlippage ∧
        GloballyNoWorse F.baselineCurvature F.candidateCurvature) := by
  intro h
  exact (A.componentwise_tradeoff).1 h.1

/-- Same-sign normalized function packets induce shared-surface joint-positive
assumptions. -/
def SameSignNormalizedFunctionPair.toLocalJointPositiveSurfaceAssumptions
    (P : SameSignNormalizedFunctionPair) :
    LocalJointPositiveSurfaceAssumptions P.surface.toSurface where
  witness := by
    let Q : SameSignNormalizedQuadraticPair := {
      pair := P.surface.pair
      curvature_coeff_pos := P.curvature_coeff_pos
    }
    rcases Q.toLocalJointPositiveWitness with ⟨d, hdslip, hdcurv⟩
    refine ⟨d, by
      rw [← congrFun (NormalizedFunctionPair.slippage_delta_eq_toSurface P.surface) d]
      exact hdslip, by
      rw [← congrFun (NormalizedFunctionPair.curvature_delta_eq_toSurface P.surface) d]
      exact hdcurv⟩

/-- Mixed-sign normalized function packets induce shared-surface tradeoff
assumptions. -/
def MixedSignNormalizedFunctionPair.toLocalTradeoffSurfaceAssumptions
    (P : MixedSignNormalizedFunctionPair) :
    LocalTradeoffSurfaceAssumptions P.surface.toSurface where
  witness := by
    let Q : MixedSignNormalizedQuadraticPair := {
      pair := P.surface.pair
      curvature_coeff_neg := P.curvature_coeff_neg
    }
    rcases Q.toLocalTradeoffWitness with ⟨d, hdslip, hdcurv⟩
    refine ⟨d, by
      rw [← congrFun (NormalizedFunctionPair.slippage_delta_eq_toSurface P.surface) d]
      exact hdslip, by
      rw [← congrFun (NormalizedFunctionPair.curvature_delta_eq_toSurface P.surface) d]
      exact hdcurv⟩

/-- The concrete normalized power-family comparison surface. -/
def powerFamilyNormalizedSurface (alpha : ℝ) : AMMCoefficientSurface where
  baselineSlippage := powerFamilyNormalizedSlippageBaseline alpha
  candidateSlippage := powerFamilyNormalizedSlippageCandidate alpha
  baselineCurvature := powerFamilyNormalizedCurvatureBaseline alpha
  candidateCurvature := powerFamilyNormalizedCurvatureCandidate alpha

/-- The power-family normalized surface satisfies the shared-surface
joint-positive assumptions below the phase threshold. -/
def powerFamilyNormalizedSurface_same_sign_assumptions
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    LocalJointPositiveSurfaceAssumptions (powerFamilyNormalizedSurface alpha) := by
  simpa [powerFamilyNormalizedSurface, powerFamilySameSignNormalizedFunctionPair,
    powerFamilyNormalizedFunctionPair, NormalizedFunctionPair.toSurface]
    using
      SameSignNormalizedFunctionPair.toLocalJointPositiveSurfaceAssumptions
        (powerFamilySameSignNormalizedFunctionPair alpha halpha halpha_lt)

/-- The power-family normalized surface satisfies the shared-surface tradeoff
assumptions above the phase threshold. -/
def powerFamilyNormalizedSurface_mixed_sign_assumptions
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    LocalTradeoffSurfaceAssumptions (powerFamilyNormalizedSurface alpha) := by
  simpa [powerFamilyNormalizedSurface, powerFamilyMixedSignNormalizedFunctionPair,
    powerFamilyNormalizedFunctionPair, NormalizedFunctionPair.toSurface]
    using
      MixedSignNormalizedFunctionPair.toLocalTradeoffSurfaceAssumptions
        (powerFamilyMixedSignNormalizedFunctionPair alpha halpha halpha_gt)

/-- Below the phase threshold `alpha = 2/3`, the normalized power-family
surface cannot have the candidate globally no worse in both coordinates. -/
theorem powerFamilyNormalizedSurface_same_sign_obstruction
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    ¬ (GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateSlippage
          (powerFamilyNormalizedSurface alpha).baselineSlippage ∧
        GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateCurvature
          (powerFamilyNormalizedSurface alpha).baselineCurvature) := by
  exact
    LocalJointPositiveSurfaceAssumptions.not_simultaneous_global_no_worse
      (powerFamilyNormalizedSurface_same_sign_assumptions alpha halpha halpha_lt)

/-- Above the phase threshold `alpha = 2/3`, the normalized power-family
surface cannot have the candidate globally no worse in slippage while the
baseline is globally no worse in curvature. -/
theorem powerFamilyNormalizedSurface_mixed_sign_tradeoff
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    ¬ (GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateSlippage
          (powerFamilyNormalizedSurface alpha).baselineSlippage ∧
        GloballyNoWorse (powerFamilyNormalizedSurface alpha).baselineCurvature
          (powerFamilyNormalizedSurface alpha).candidateCurvature) := by
  exact
    LocalTradeoffSurfaceAssumptions.not_slippage_no_worse_and_baseline_curvature_no_worse
      (powerFamilyNormalizedSurface_mixed_sign_assumptions alpha halpha halpha_gt)

/-- Same-sign regime, unpacked into componentwise refuters on the shared
surface. -/
theorem powerFamilyNormalizedSurface_same_sign_componentwise
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    (¬ GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateSlippage
        (powerFamilyNormalizedSurface alpha).baselineSlippage) ∧
      (¬ GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateCurvature
        (powerFamilyNormalizedSurface alpha).baselineCurvature) :=
  LocalJointPositiveSurfaceAssumptions.componentwise_obstruction
    (powerFamilyNormalizedSurface_same_sign_assumptions alpha halpha halpha_lt)

/-- Mixed-sign regime, unpacked into componentwise refuters on the shared
surface. -/
theorem powerFamilyNormalizedSurface_mixed_sign_componentwise
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    (¬ GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateSlippage
        (powerFamilyNormalizedSurface alpha).baselineSlippage) ∧
      (¬ GloballyNoWorse (powerFamilyNormalizedSurface alpha).baselineCurvature
        (powerFamilyNormalizedSurface alpha).candidateCurvature) :=
  LocalTradeoffSurfaceAssumptions.componentwise_tradeoff
    (powerFamilyNormalizedSurface_mixed_sign_assumptions alpha halpha halpha_gt)

/-- Uniform slippage conclusion on the shared surface: for every positive
`alpha`, the normalized power-family candidate is not globally no worse than
the normalized slippage baseline. -/
theorem powerFamilyNormalizedSurface_slippage_not_global_no_worse
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateSlippage
        (powerFamilyNormalizedSurface alpha).baselineSlippage := by
  simpa [powerFamilyNormalizedSurface, powerFamilyNormalizedFunctionPair,
    NormalizedFunctionPair.toSurface]
    using powerFamilyNormalizedFunctionPair_slippage_not_global_no_worse halpha

/-- Barrier result: the candidate curvature cannot be globally no worse than
the normalized baseline curvature for every positive `alpha`. -/
theorem powerFamilyNormalizedSurface_not_universal_candidate_curvature_no_worse :
    ¬ ∀ alpha : ℝ,
        0 < alpha ->
          GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateCurvature
            (powerFamilyNormalizedSurface alpha).baselineCurvature := by
  intro h
  have hthird : GloballyNoWorse
      (powerFamilyNormalizedSurface (1 / 3 : ℝ)).candidateCurvature
      (powerFamilyNormalizedSurface (1 / 3 : ℝ)).baselineCurvature :=
    h (1 / 3) (by norm_num)
  exact
    (powerFamilyNormalizedSurface_same_sign_componentwise (alpha := 1 / 3)
      (by norm_num) (by norm_num)).2 hthird

/-- Barrier result: the normalized baseline curvature cannot be globally no
worse than the candidate curvature for every positive `alpha`. -/
theorem powerFamilyNormalizedSurface_not_universal_baseline_curvature_no_worse :
    ¬ ∀ alpha : ℝ,
        0 < alpha ->
          GloballyNoWorse (powerFamilyNormalizedSurface alpha).baselineCurvature
            (powerFamilyNormalizedSurface alpha).candidateCurvature := by
  intro h
  have hone : GloballyNoWorse
      (powerFamilyNormalizedSurface (1 : ℝ)).baselineCurvature
      (powerFamilyNormalizedSurface (1 : ℝ)).candidateCurvature :=
    h 1 (by norm_num)
  exact
    (powerFamilyNormalizedSurface_mixed_sign_componentwise (alpha := 1)
      (by norm_num) (by norm_num)).2 hone

/-- There is no single global curvature orientation that is valid for every
positive `alpha` on the normalized power-family surface. -/
theorem powerFamilyNormalizedSurface_no_uniform_curvature_orientation :
    ¬ ((∀ alpha : ℝ,
            0 < alpha ->
              GloballyNoWorse (powerFamilyNormalizedSurface alpha).candidateCurvature
                (powerFamilyNormalizedSurface alpha).baselineCurvature) ∨
        (∀ alpha : ℝ,
            0 < alpha ->
              GloballyNoWorse (powerFamilyNormalizedSurface alpha).baselineCurvature
                (powerFamilyNormalizedSurface alpha).candidateCurvature)) := by
  intro h
  rcases h with hleft | hright
  · exact powerFamilyNormalizedSurface_not_universal_candidate_curvature_no_worse hleft
  · exact powerFamilyNormalizedSurface_not_universal_baseline_curvature_no_worse hright

end
end LocalJetFrontier
end Impossibility
end TauSwap
