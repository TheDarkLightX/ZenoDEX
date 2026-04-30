import Proofs.AMMOriginalHODLNormalizedSurfaceBridge

/-!
# Original-HODL normalized surface semantics

This file lifts the normalized shared-surface witness layer into small semantic
model objects.

The purpose is to make the next transport target explicit: a semantics class
must construct a coefficient surface together with one of the normalized local
witness assumption objects. Once that is done, the corresponding global
obstruction theorem follows immediately.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Semantic model for AMM families whose extracted surface carries a local
joint-positive witness. -/
structure LocalJointPositiveSurfaceSemanticsModel (RawAMM : Type) where
  surface : RawAMM → AMMCoefficientSurface
  assumptions : ∀ raw, LocalJointPositiveSurfaceAssumptions (surface raw)

/-- Semantic model for AMM families whose extracted surface carries a local
slippage/curvature tradeoff witness. -/
structure LocalTradeoffSurfaceSemanticsModel (RawAMM : Type) where
  surface : RawAMM → AMMCoefficientSurface
  assumptions : ∀ raw, LocalTradeoffSurfaceAssumptions (surface raw)

/-- A joint-positive surface model immediately yields the componentwise global
refuters on its extracted surface. -/
theorem LocalJointPositiveSurfaceSemanticsModel.componentwise_obstruction
    {RawAMM : Type} (M : LocalJointPositiveSurfaceSemanticsModel RawAMM)
    (raw : RawAMM) :
    (¬ GloballyNoWorse (M.surface raw).candidateSlippage
        (M.surface raw).baselineSlippage) ∧
      (¬ GloballyNoWorse (M.surface raw).candidateCurvature
        (M.surface raw).baselineCurvature) :=
  LocalJointPositiveSurfaceAssumptions.componentwise_obstruction
    (M.assumptions raw)

/-- A joint-positive surface model refutes simultaneous global no-worse on its
extracted surface. -/
theorem LocalJointPositiveSurfaceSemanticsModel.not_simultaneous_global_no_worse
    {RawAMM : Type} (M : LocalJointPositiveSurfaceSemanticsModel RawAMM)
    (raw : RawAMM) :
    ¬ (GloballyNoWorse (M.surface raw).candidateSlippage
          (M.surface raw).baselineSlippage ∧
        GloballyNoWorse (M.surface raw).candidateCurvature
          (M.surface raw).baselineCurvature) :=
  LocalJointPositiveSurfaceAssumptions.not_simultaneous_global_no_worse
    (M.assumptions raw)

/-- A tradeoff surface model immediately yields the componentwise global
refuters on its extracted surface. -/
theorem LocalTradeoffSurfaceSemanticsModel.componentwise_tradeoff
    {RawAMM : Type} (M : LocalTradeoffSurfaceSemanticsModel RawAMM)
    (raw : RawAMM) :
    (¬ GloballyNoWorse (M.surface raw).candidateSlippage
        (M.surface raw).baselineSlippage) ∧
      (¬ GloballyNoWorse (M.surface raw).baselineCurvature
        (M.surface raw).candidateCurvature) :=
  LocalTradeoffSurfaceAssumptions.componentwise_tradeoff
    (M.assumptions raw)

/-- A tradeoff surface model refutes simultaneous slippage no-worse and the
reversed curvature dominance claim on its extracted surface. -/
theorem LocalTradeoffSurfaceSemanticsModel.not_slippage_no_worse_and_baseline_curvature_no_worse
    {RawAMM : Type} (M : LocalTradeoffSurfaceSemanticsModel RawAMM)
    (raw : RawAMM) :
    ¬ (GloballyNoWorse (M.surface raw).candidateSlippage
          (M.surface raw).baselineSlippage ∧
        GloballyNoWorse (M.surface raw).baselineCurvature
          (M.surface raw).candidateCurvature) :=
  LocalTradeoffSurfaceAssumptions.not_slippage_no_worse_and_baseline_curvature_no_worse
    (M.assumptions raw)

/-- Parameter space for the power-family same-sign regime. -/
abbrev PowerFamilySameSignParam : Type :=
  { alpha : ℝ // 0 < alpha ∧ alpha < 2 / 3 }

/-- Parameter space for the power-family mixed-sign regime. -/
abbrev PowerFamilyMixedSignParam : Type :=
  { alpha : ℝ // 2 / 3 < alpha }

/-- The power-family same-sign regime is a joint-positive normalized surface
model. -/
def powerFamilySameSignSurfaceModel :
    LocalJointPositiveSurfaceSemanticsModel PowerFamilySameSignParam where
  surface := fun raw => powerFamilyNormalizedSurface raw.1
  assumptions := by
    intro raw
    exact powerFamilyNormalizedSurface_same_sign_assumptions
      raw.1 raw.2.1 raw.2.2

/-- The power-family mixed-sign regime is a normalized surface tradeoff
model. -/
def powerFamilyMixedSignSurfaceModel :
    LocalTradeoffSurfaceSemanticsModel PowerFamilyMixedSignParam where
  surface := fun raw => powerFamilyNormalizedSurface raw.1
  assumptions := by
    intro raw
    have halpha : 0 < raw.1 := by linarith [raw.2]
    exact powerFamilyNormalizedSurface_mixed_sign_assumptions
      raw.1 halpha raw.2

/-- Semantic-model restatement of the same-sign obstruction for the power
family. -/
theorem powerFamilySameSignSurfaceModel_not_simultaneous_global_no_worse
    (raw : PowerFamilySameSignParam) :
    ¬ (GloballyNoWorse
          (powerFamilySameSignSurfaceModel.surface raw).candidateSlippage
          (powerFamilySameSignSurfaceModel.surface raw).baselineSlippage ∧
        GloballyNoWorse
          (powerFamilySameSignSurfaceModel.surface raw).candidateCurvature
          (powerFamilySameSignSurfaceModel.surface raw).baselineCurvature) :=
  powerFamilySameSignSurfaceModel.not_simultaneous_global_no_worse raw

/-- Semantic-model restatement of the mixed-sign tradeoff theorem for the power
family. -/
theorem powerFamilyMixedSignSurfaceModel_tradeoff
    (raw : PowerFamilyMixedSignParam) :
    ¬ (GloballyNoWorse
          (powerFamilyMixedSignSurfaceModel.surface raw).candidateSlippage
          (powerFamilyMixedSignSurfaceModel.surface raw).baselineSlippage ∧
        GloballyNoWorse
          (powerFamilyMixedSignSurfaceModel.surface raw).baselineCurvature
          (powerFamilyMixedSignSurfaceModel.surface raw).candidateCurvature) :=
  powerFamilyMixedSignSurfaceModel.not_slippage_no_worse_and_baseline_curvature_no_worse raw

end
end LocalJetFrontier
end Impossibility
end TauSwap
