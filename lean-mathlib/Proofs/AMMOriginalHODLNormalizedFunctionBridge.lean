import Proofs.AMMOriginalHODLNormalizedPairBridge

/-!
# Original-HODL normalized function bridge

This file transports the local normalized witness packets back to ordinary
candidate/baseline function-level obstruction statements.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Function-level packaging for a normalized local pair: the bundled
quadratic-pair delta surface is identified with candidate-minus-baseline
function deltas. -/
structure NormalizedFunctionPair where
  baselineSlippage : ℝ → ℝ
  candidateSlippage : ℝ → ℝ
  baselineCurvature : ℝ → ℝ
  candidateCurvature : ℝ → ℝ
  pair : OriginalHODLNormalizedQuadraticPair
  slippage_delta_eq :
    pair.slippage.delta = fun d => candidateSlippage d - baselineSlippage d
  curvature_delta_eq :
    pair.curvature.delta = fun d => candidateCurvature d - baselineCurvature d

/-- Function-level same-sign packet: the normalized curvature coefficient is
positive. -/
structure SameSignNormalizedFunctionPair where
  surface : NormalizedFunctionPair
  curvature_coeff_pos : 0 < surface.pair.curvature.coeff

/-- Function-level mixed-sign packet: the normalized curvature coefficient is
negative. -/
structure MixedSignNormalizedFunctionPair where
  surface : NormalizedFunctionPair
  curvature_coeff_neg : surface.pair.curvature.coeff < 0

/-- A local joint-positive witness transports through delta equalities into a
function-level obstruction: candidate cannot be globally no worse in either
coordinate. -/
theorem LocalJointPositiveWitness.function_level_obstruction
    {slipDelta curvDelta : ℝ → ℝ}
    {candidateSlippage baselineSlippage candidateCurvature baselineCurvature : ℝ → ℝ}
    (hslip_eq : slipDelta = fun d => candidateSlippage d - baselineSlippage d)
    (hcurv_eq : curvDelta = fun d => candidateCurvature d - baselineCurvature d)
    (hlocal : LocalJointPositiveWitness slipDelta curvDelta) :
    (¬ GloballyNoWorse candidateSlippage baselineSlippage) ∧
      (¬ GloballyNoWorse candidateCurvature baselineCurvature) := by
  rcases hlocal with ⟨d, hdslip, hdcurv⟩
  constructor
  · intro hglobal
    have hdslip' : 0 < candidateSlippage d - baselineSlippage d := by
      simpa [hslip_eq] using hdslip
    have hle : candidateSlippage d ≤ baselineSlippage d := hglobal d
    linarith
  · intro hglobal
    have hdcurv' : 0 < candidateCurvature d - baselineCurvature d := by
      simpa [hcurv_eq] using hdcurv
    have hle : candidateCurvature d ≤ baselineCurvature d := hglobal d
    linarith

/-- A local tradeoff witness transports through delta equalities into the
function-level tradeoff obstruction: candidate cannot be globally no worse in
slippage, and baseline cannot be globally no worse in curvature. -/
theorem LocalTradeoffWitness.function_level_tradeoff
    {slipDelta curvDelta : ℝ → ℝ}
    {candidateSlippage baselineSlippage candidateCurvature baselineCurvature : ℝ → ℝ}
    (hslip_eq : slipDelta = fun d => candidateSlippage d - baselineSlippage d)
    (hcurv_eq : curvDelta = fun d => candidateCurvature d - baselineCurvature d)
    (hlocal : LocalTradeoffWitness slipDelta curvDelta) :
    (¬ GloballyNoWorse candidateSlippage baselineSlippage) ∧
      (¬ GloballyNoWorse baselineCurvature candidateCurvature) := by
  rcases hlocal with ⟨d, hdslip, hdcurv⟩
  constructor
  · intro hglobal
    have hdslip' : 0 < candidateSlippage d - baselineSlippage d := by
      simpa [hslip_eq] using hdslip
    have hle : candidateSlippage d ≤ baselineSlippage d := hglobal d
    linarith
  · intro hglobal
    have hdcurv' : candidateCurvature d - baselineCurvature d < 0 := by
      simpa [hcurv_eq] using hdcurv
    have hle : baselineCurvature d ≤ candidateCurvature d := hglobal d
    linarith

/-- A same-sign normalized function packet transports the local witness into a
function-level obstruction: candidate is not globally no worse in either
coordinate. -/
theorem SameSignNormalizedFunctionPair.function_level_obstruction
    (F : SameSignNormalizedFunctionPair) :
    (¬ GloballyNoWorse F.surface.candidateSlippage F.surface.baselineSlippage) ∧
      (¬ GloballyNoWorse F.surface.candidateCurvature F.surface.baselineCurvature) := by
  let P : SameSignNormalizedQuadraticPair := {
    pair := F.surface.pair
    curvature_coeff_pos := F.curvature_coeff_pos
  }
  exact LocalJointPositiveWitness.function_level_obstruction
    F.surface.slippage_delta_eq
    F.surface.curvature_delta_eq
    P.toLocalJointPositiveWitness

/-- A mixed-sign normalized function packet transports the local tradeoff
witness into the function-level obstruction. -/
theorem MixedSignNormalizedFunctionPair.function_level_tradeoff
    (F : MixedSignNormalizedFunctionPair) :
    (¬ GloballyNoWorse F.surface.candidateSlippage F.surface.baselineSlippage) ∧
      (¬ GloballyNoWorse F.surface.baselineCurvature F.surface.candidateCurvature) := by
  let P : MixedSignNormalizedQuadraticPair := {
    pair := F.surface.pair
    curvature_coeff_neg := F.curvature_coeff_neg
  }
  exact LocalTradeoffWitness.function_level_tradeoff
    F.surface.slippage_delta_eq
    F.surface.curvature_delta_eq
    P.toLocalTradeoffWitness

/-- Every normalized function pair already refutes global slippage no-worse,
because the slippage side has a strictly positive quadratic leading
coefficient. -/
theorem NormalizedFunctionPair.slippage_not_global_no_worse
    (P : NormalizedFunctionPair) :
    ¬ GloballyNoWorse P.candidateSlippage P.baselineSlippage := by
  intro hglobal
  have hdelta_nonpos : ∀ d, P.pair.slippage.delta d ≤ 0 := by
    intro d
    rw [P.slippage_delta_eq]
    exact sub_nonpos.mpr (hglobal d)
  exact P.pair.slippage.not_global_nonpos hdelta_nonpos

/-- Concrete slippage baseline for the power-family normalized bridge: the
center value removed from the raw slippage surface. -/
def powerFamilyNormalizedSlippageBaseline (alpha : ℝ) : ℝ → ℝ :=
  fun _ => 2 / (alpha + 2)

/-- Concrete slippage candidate for the power-family normalized bridge. -/
def powerFamilyNormalizedSlippageCandidate (alpha : ℝ) : ℝ → ℝ :=
  fun d => powerFamilyGlobalSlippageFromSechSq alpha (sechSq d)

/-- Concrete curvature baseline for the power-family normalized bridge: CPMM
plus the center offset that must be normalized away. -/
def powerFamilyNormalizedCurvatureBaseline (alpha : ℝ) : ℝ → ℝ :=
  fun d => cpmmGlobalCurvatureFromSechSq (sechSq d) + alpha / 16

/-- Concrete curvature candidate for the power-family normalized bridge. -/
def powerFamilyNormalizedCurvatureCandidate (alpha : ℝ) : ℝ → ℝ :=
  fun d => powerFamilyGlobalCurvatureFromSechSq alpha (sechSq d)

/-- Concrete function-level packaging of the normalized power-family pair. -/
def powerFamilyNormalizedFunctionPair
    (alpha : ℝ) (halpha : 0 < alpha) : NormalizedFunctionPair where
  baselineSlippage := powerFamilyNormalizedSlippageBaseline alpha
  candidateSlippage := powerFamilyNormalizedSlippageCandidate alpha
  baselineCurvature := powerFamilyNormalizedCurvatureBaseline alpha
  candidateCurvature := powerFamilyNormalizedCurvatureCandidate alpha
  pair := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  slippage_delta_eq := by
    funext d
    rfl
  curvature_delta_eq := by
    funext d
    change powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d =
      powerFamilyNormalizedCurvatureCandidate alpha d -
        powerFamilyNormalizedCurvatureBaseline alpha d
    rw [powerFamilyOriginalHODLNormalizedCurvatureDelta_eq_fromW]
    unfold powerFamilyOriginalHODLNormalizedCurvatureFromW
    unfold powerFamilyNormalizedCurvatureCandidate powerFamilyNormalizedCurvatureBaseline
    ring

/-- Below the phase threshold `alpha = 2/3`, the concrete normalized
power-family function packet lands in the same-sign regime. -/
def powerFamilySameSignNormalizedFunctionPair
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    SameSignNormalizedFunctionPair where
  surface := powerFamilyNormalizedFunctionPair alpha halpha
  curvature_coeff_pos :=
    (powerFamilySameSignNormalizedQuadraticPair alpha halpha halpha_lt).curvature_coeff_pos

/-- Above the phase threshold `alpha = 2/3`, the concrete normalized
power-family function packet lands in the mixed-sign regime. -/
def powerFamilyMixedSignNormalizedFunctionPair
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    MixedSignNormalizedFunctionPair where
  surface := powerFamilyNormalizedFunctionPair alpha halpha
  curvature_coeff_neg :=
    (powerFamilyMixedSignNormalizedQuadraticPair alpha halpha halpha_gt).curvature_coeff_neg

/-- Concrete function-level consequence below `alpha = 2/3`: on the normalized
slippage and curvature surfaces, the power-family candidate is not globally no
worse than its normalized baselines in either coordinate. -/
theorem powerFamilySameSignNormalizedFunctionPair_obstruction
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    (¬ GloballyNoWorse
        (powerFamilyNormalizedSlippageCandidate alpha)
        (powerFamilyNormalizedSlippageBaseline alpha)) ∧
      (¬ GloballyNoWorse
        (powerFamilyNormalizedCurvatureCandidate alpha)
        (powerFamilyNormalizedCurvatureBaseline alpha)) := by
  exact
    (powerFamilySameSignNormalizedFunctionPair alpha halpha halpha_lt).function_level_obstruction

/-- Concrete function-level consequence above `alpha = 2/3`: on the normalized
surfaces, the power-family candidate cannot be globally no worse in slippage,
and the normalized curvature baseline cannot be globally no worse than the
candidate. -/
theorem powerFamilyMixedSignNormalizedFunctionPair_tradeoff
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    (¬ GloballyNoWorse
        (powerFamilyNormalizedSlippageCandidate alpha)
        (powerFamilyNormalizedSlippageBaseline alpha)) ∧
      (¬ GloballyNoWorse
        (powerFamilyNormalizedCurvatureBaseline alpha)
        (powerFamilyNormalizedCurvatureCandidate alpha)) := by
  exact
    (powerFamilyMixedSignNormalizedFunctionPair alpha halpha halpha_gt).function_level_tradeoff

/-- Uniform slippage conclusion for the normalized power-family comparison:
for every positive `alpha`, the candidate cannot be globally no worse than the
normalized slippage baseline. -/
theorem powerFamilyNormalizedFunctionPair_slippage_not_global_no_worse
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ GloballyNoWorse
        (powerFamilyNormalizedSlippageCandidate alpha)
        (powerFamilyNormalizedSlippageBaseline alpha) := by
  exact (powerFamilyNormalizedFunctionPair alpha halpha).slippage_not_global_no_worse

end
end LocalJetFrontier
end Impossibility
end TauSwap
