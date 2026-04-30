import Proofs.AMMOriginalHODLNormalizedSlippageBridge
import Proofs.AMMPowerFamilyOriginalHODLCurvatureNormalization

/-!
# Original-HODL normalized pair bridge

This file packages the center-normalized power-family original-HODL slippage
and curvature surfaces into one quadratic pair object.

The old first-even bridge surface is already ruled out on the slippage side.
The next honest interface is therefore the normalized pair itself:

* slippage contributes a checked quadratic coefficient;
* curvature contributes a checked quadratic coefficient;
* the coefficient signs split at `alpha = 2/3`;
* the mismatch with the old `1/8` coupling law factors exactly.
-/

open Filter Topology

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

/-- Generic quadratic surface: the center-normalized delta has a finite
quadratic leading coefficient. -/
structure QuadraticSurface where
  delta : ℝ → ℝ
  coeff : ℝ
  coeff_tendsto :
    Tendsto (fun d => delta d / d ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 coeff)

/-- The normalized original-HODL pair interface: positive quadratic slippage
data together with a quadratic curvature surface. -/
structure OriginalHODLNormalizedQuadraticPair where
  slippage : PositiveQuadraticSlippageSurface
  curvature : QuadraticSurface

/-- A quadratic surface with positive leading coefficient is eventually
positive on the punctured neighborhood of the center. -/
theorem QuadraticSurface.eventually_pos_of_coeff_pos
    (S : QuadraticSurface) (hcoeff : 0 < S.coeff) :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < S.delta d := by
  have hratio : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < S.delta d / d ^ 2 :=
    S.coeff_tendsto.eventually (eventually_gt_nhds hcoeff)
  filter_upwards [hratio, self_mem_nhdsWithin] with d hratio hd
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  exact (div_pos_iff_of_pos_right hd2).1 hratio

/-- A quadratic surface with negative leading coefficient is eventually
negative on the punctured neighborhood of the center. -/
theorem QuadraticSurface.eventually_neg_of_coeff_neg
    (S : QuadraticSurface) (hcoeff : S.coeff < 0) :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ), S.delta d < 0 := by
  have hratio : ∀ᶠ d in 𝓝[≠] (0 : ℝ), S.delta d / d ^ 2 < 0 :=
    S.coeff_tendsto.eventually (eventually_lt_nhds hcoeff)
  filter_upwards [hratio, self_mem_nhdsWithin] with d hratio hd
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  by_contra hnonneg
  have hnonneg' : 0 ≤ S.delta d := by linarith
  have hdiv_nonneg : 0 ≤ S.delta d / d ^ 2 := div_nonneg hnonneg' hd2.le
  linarith

/-- A positive quadratic leading coefficient rules out global nonpositivity. -/
theorem QuadraticSurface.not_global_nonpos_of_coeff_pos
    (S : QuadraticSurface) (hcoeff : 0 < S.coeff) :
    ¬ ∀ d, S.delta d ≤ 0 := by
  intro hglobal
  obtain ⟨d, hdpos⟩ := (S.eventually_pos_of_coeff_pos hcoeff).exists
  exact not_lt_of_ge (hglobal d) hdpos

/-- A negative quadratic leading coefficient rules out global nonnegativity. -/
theorem QuadraticSurface.not_global_nonneg_of_coeff_neg
    (S : QuadraticSurface) (hcoeff : S.coeff < 0) :
    ¬ ∀ d, 0 ≤ S.delta d := by
  intro hglobal
  obtain ⟨d, hdneg⟩ := (S.eventually_neg_of_coeff_neg hcoeff).exists
  exact not_lt_of_ge (hglobal d) hdneg

/-- Positive quadratic slippage surfaces are eventually positive near the
center. -/
theorem PositiveQuadraticSlippageSurface.eventually_pos
    (S : PositiveQuadraticSlippageSurface) :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < S.delta d := by
  let T : QuadraticSurface := {
    delta := S.delta
    coeff := S.coeff
    coeff_tendsto := S.coeff_tendsto
  }
  exact T.eventually_pos_of_coeff_pos S.coeff_pos

/-- Positive quadratic slippage surfaces cannot stay globally nonpositive. -/
theorem PositiveQuadraticSlippageSurface.not_global_nonpos
    (S : PositiveQuadraticSlippageSurface) :
    ¬ ∀ d, S.delta d ≤ 0 := by
  let T : QuadraticSurface := {
    delta := S.delta
    coeff := S.coeff
    coeff_tendsto := S.coeff_tendsto
  }
  exact T.not_global_nonpos_of_coeff_pos S.coeff_pos

/-- Any normalized quadratic pair already rules out simultaneous global
nonpositivity, because the slippage side is forced positive near the center. -/
theorem OriginalHODLNormalizedQuadraticPair.not_simultaneous_global_nonpos
    (P : OriginalHODLNormalizedQuadraticPair) :
    ¬ ((∀ d, P.slippage.delta d ≤ 0) ∧ (∀ d, P.curvature.delta d ≤ 0)) := by
  intro hglobal
  exact P.slippage.not_global_nonpos hglobal.1

/-- Replacement bridge object for the regime where both normalized quadratic
coefficients are positive. -/
structure SameSignNormalizedQuadraticPair where
  pair : OriginalHODLNormalizedQuadraticPair
  curvature_coeff_pos : 0 < pair.curvature.coeff

/-- Replacement bridge object for the regime where normalized slippage stays
positive but normalized curvature flips negative. -/
structure MixedSignNormalizedQuadraticPair where
  pair : OriginalHODLNormalizedQuadraticPair
  curvature_coeff_neg : pair.curvature.coeff < 0

/-- Transport-ready witness predicate for a local regime where both normalized
deltas are strictly positive at some punctured-neighborhood point. -/
def LocalJointPositiveWitness (slipDelta curvDelta : ℝ → ℝ) : Prop :=
  ∃ d, 0 < slipDelta d ∧ 0 < curvDelta d

/-- Transport-ready witness predicate for a local slippage/curvature tradeoff:
slippage is strictly positive while curvature is strictly negative somewhere. -/
def LocalTradeoffWitness (slipDelta curvDelta : ℝ → ℝ) : Prop :=
  ∃ d, 0 < slipDelta d ∧ curvDelta d < 0

/-- A local joint-positive witness already refutes simultaneous global
nonpositivity. -/
theorem LocalJointPositiveWitness.not_simultaneous_global_nonpos
    {slipDelta curvDelta : ℝ → ℝ}
    (hlocal : LocalJointPositiveWitness slipDelta curvDelta) :
    ¬ ((∀ d, slipDelta d ≤ 0) ∧ (∀ d, curvDelta d ≤ 0)) := by
  rintro ⟨hslip, hcurv⟩
  rcases hlocal with ⟨d, hdslip, hdcurv⟩
  exact not_lt_of_ge (hslip d) hdslip

/-- A local tradeoff witness already refutes global nonpositive slippage and
global nonnegative curvature. -/
theorem LocalTradeoffWitness.obstruction
    {slipDelta curvDelta : ℝ → ℝ}
    (hlocal : LocalTradeoffWitness slipDelta curvDelta) :
    (¬ ∀ d, slipDelta d ≤ 0) ∧ (¬ ∀ d, 0 ≤ curvDelta d) := by
  rcases hlocal with ⟨d, hdslip, hdcurv⟩
  constructor
  · intro hslip
    exact not_lt_of_ge (hslip d) hdslip
  · intro hcurv
    exact not_lt_of_ge (hcurv d) hdcurv

/-- The checked quadratic coefficient of the normalized power-family slippage
surface. -/
def powerFamilyOriginalHODLNormalizedSlippageCoeff (alpha : ℝ) : ℝ :=
  4 * alpha * (alpha + 1) / (alpha + 2) ^ 3

/-- The checked quadratic coefficient of the normalized power-family curvature
surface. -/
def powerFamilyOriginalHODLNormalizedCurvatureCoeff (alpha : ℝ) : ℝ :=
  -alpha * (3 * alpha - 2) / (16 * (alpha + 2))

/-- The normalized power-family curvature surface packages into the generic
quadratic surface interface. -/
def powerFamilyOriginalHODLNormalizedCurvatureSurface
    (alpha : ℝ) (_halpha : 0 < alpha) : QuadraticSurface where
  delta := powerFamilyOriginalHODLNormalizedCurvatureDelta alpha
  coeff := powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha
  coeff_tendsto := by
    simpa [powerFamilyOriginalHODLNormalizedCurvatureCoeff] using
      powerFamilyOriginalHODLNormalizedCurvatureDelta_div_sq_tendsto _halpha

/-- The full normalized power-family pair: slippage and curvature together. -/
def powerFamilyOriginalHODLNormalizedQuadraticPair
    (alpha : ℝ) (halpha : 0 < alpha) : OriginalHODLNormalizedQuadraticPair where
  slippage := {
    powerFamilyOriginalHODLNormalizedSlippageSurface alpha halpha with
    coeff := powerFamilyOriginalHODLNormalizedSlippageCoeff alpha
  }
  curvature := powerFamilyOriginalHODLNormalizedCurvatureSurface alpha halpha

/-- The normalized power-family curvature coefficient is positive below the
phase threshold `alpha = 2/3`. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureCoeff_pos_of_lt_two_thirds
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    0 < powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha := by
  unfold powerFamilyOriginalHODLNormalizedCurvatureCoeff
  have hmain : 0 < 2 - 3 * alpha := by linarith
  have hrewrite :
      -alpha * (3 * alpha - 2) = alpha * (2 - 3 * alpha) := by ring
  rw [hrewrite]
  positivity

/-- At the threshold `alpha = 2/3`, the normalized power-family curvature
coefficient vanishes, so any stronger bridge must look one order higher. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureCoeff_two_thirds :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff (2 / 3 : ℝ) = 0 := by
  norm_num [powerFamilyOriginalHODLNormalizedCurvatureCoeff]

/-- Canonical packet at the phase boundary `alpha = 2/3`.  This keeps the
critical point explicit instead of silently classifying it into either open
regime. -/
def powerFamilyCriticalOriginalHODLNormalizedQuadraticPair :
    OriginalHODLNormalizedQuadraticPair :=
  powerFamilyOriginalHODLNormalizedQuadraticPair (2 / 3 : ℝ) (by norm_num)

/-- At the phase boundary, slippage is still genuinely quadratic-positive but
the curvature quadratic coefficient is exactly zero.  Any sign theorem at this
point therefore needs a higher-order expansion rather than the open-regime
quadratic classifier. -/
theorem powerFamilyCriticalOriginalHODLNormalizedQuadraticPair_boundary :
    0 < powerFamilyCriticalOriginalHODLNormalizedQuadraticPair.slippage.coeff ∧
      powerFamilyCriticalOriginalHODLNormalizedQuadraticPair.curvature.coeff = 0 := by
  constructor
  · norm_num [powerFamilyCriticalOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedSlippageCoeff]
  · norm_num [powerFamilyCriticalOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedCurvatureSurface,
      powerFamilyOriginalHODLNormalizedCurvatureCoeff]

/-- The critical packet has no quadratic curvature orientation.  It is neither
same-sign nor mixed-sign at quadratic order. -/
theorem powerFamilyCriticalOriginalHODLNormalizedQuadraticPair_no_quadratic_curvature_sign :
    ¬ 0 < powerFamilyCriticalOriginalHODLNormalizedQuadraticPair.curvature.coeff ∧
      ¬ powerFamilyCriticalOriginalHODLNormalizedQuadraticPair.curvature.coeff < 0 := by
  rcases powerFamilyCriticalOriginalHODLNormalizedQuadraticPair_boundary with
    ⟨_, hcurv⟩
  constructor
  · intro hpos
    rw [hcurv] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro hneg
    rw [hcurv] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg

/-- The normalized power-family curvature coefficient is negative above the
phase threshold `alpha = 2/3`. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureCoeff_neg_of_two_thirds_lt
    {alpha : ℝ} (halpha_gt : 2 / 3 < alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha < 0 := by
  unfold powerFamilyOriginalHODLNormalizedCurvatureCoeff
  have hpos : 0 < alpha * (3 * alpha - 2) := by
    have halpha : 0 < alpha := by linarith
    have hmain : 0 < 3 * alpha - 2 := by linarith
    positivity
  have hrewrite :
      -alpha * (3 * alpha - 2) / (16 * (alpha + 2)) =
        -(alpha * (3 * alpha - 2) / (16 * (alpha + 2))) := by
    ring
  rw [hrewrite]
  have hfrac : 0 < alpha * (3 * alpha - 2) / (16 * (alpha + 2)) := by
    positivity
  linarith

/-- Concrete power-family packet below the phase threshold `alpha = 2/3`. -/
def powerFamilySameSignNormalizedQuadraticPair
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    SameSignNormalizedQuadraticPair where
  pair := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  curvature_coeff_pos := by
    simpa [powerFamilyOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedCurvatureSurface] using
      powerFamilyOriginalHODLNormalizedCurvatureCoeff_pos_of_lt_two_thirds
        halpha halpha_lt

/-- Concrete power-family packet above the phase threshold `alpha = 2/3`. -/
def powerFamilyMixedSignNormalizedQuadraticPair
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    MixedSignNormalizedQuadraticPair where
  pair := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  curvature_coeff_neg := by
    simpa [powerFamilyOriginalHODLNormalizedQuadraticPair,
      powerFamilyOriginalHODLNormalizedCurvatureSurface] using
      powerFamilyOriginalHODLNormalizedCurvatureCoeff_neg_of_two_thirds_lt
        halpha_gt

/-- A same-sign normalized pair has a concrete punctured-neighborhood witness at
which both normalized deltas are positive. -/
theorem SameSignNormalizedQuadraticPair.exists_joint_positive_witness
    (P : SameSignNormalizedQuadraticPair) :
    ∃ d, 0 < P.pair.slippage.delta d ∧ 0 < P.pair.curvature.delta d := by
  have hslip : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.pair.slippage.delta d :=
    P.pair.slippage.eventually_pos
  have hcurv : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.pair.curvature.delta d :=
    P.pair.curvature.eventually_pos_of_coeff_pos P.curvature_coeff_pos
  rcases (hslip.and hcurv).exists with ⟨d, hd⟩
  exact ⟨d, hd⟩

/-- A same-sign normalized pair realizes the generic local joint-positive
witness predicate. -/
theorem SameSignNormalizedQuadraticPair.toLocalJointPositiveWitness
    (P : SameSignNormalizedQuadraticPair) :
    LocalJointPositiveWitness P.pair.slippage.delta P.pair.curvature.delta :=
  P.exists_joint_positive_witness

/-- A same-sign normalized pair refutes simultaneous global nonpositivity in
both coordinates. -/
theorem SameSignNormalizedQuadraticPair.not_simultaneous_global_nonpos
    (P : SameSignNormalizedQuadraticPair) :
    ¬ ((∀ d, P.pair.slippage.delta d ≤ 0) ∧ (∀ d, P.pair.curvature.delta d ≤ 0)) :=
  P.toLocalJointPositiveWitness.not_simultaneous_global_nonpos

/-- A mixed-sign normalized pair has a concrete punctured-neighborhood witness
for the local slippage/curvature tradeoff. -/
theorem MixedSignNormalizedQuadraticPair.exists_tradeoff_witness
    (P : MixedSignNormalizedQuadraticPair) :
    ∃ d, 0 < P.pair.slippage.delta d ∧ P.pair.curvature.delta d < 0 := by
  have hslip : ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.pair.slippage.delta d :=
    P.pair.slippage.eventually_pos
  have hcurv : ∀ᶠ d in 𝓝[≠] (0 : ℝ), P.pair.curvature.delta d < 0 :=
    P.pair.curvature.eventually_neg_of_coeff_neg P.curvature_coeff_neg
  rcases (hslip.and hcurv).exists with ⟨d, hd⟩
  exact ⟨d, hd⟩

/-- A mixed-sign normalized pair realizes the generic local tradeoff witness
predicate. -/
theorem MixedSignNormalizedQuadraticPair.toLocalTradeoffWitness
    (P : MixedSignNormalizedQuadraticPair) :
    LocalTradeoffWitness P.pair.slippage.delta P.pair.curvature.delta :=
  P.exists_tradeoff_witness

/-- A mixed-sign normalized pair forces the local tradeoff obstruction:
slippage cannot stay globally nonpositive, and curvature cannot stay globally
nonnegative. -/
theorem MixedSignNormalizedQuadraticPair.tradeoff_obstruction
    (P : MixedSignNormalizedQuadraticPair) :
    (¬ ∀ d, P.pair.slippage.delta d ≤ 0) ∧
      (¬ ∀ d, 0 ≤ P.pair.curvature.delta d) :=
  P.toLocalTradeoffWitness.obstruction

/-- Regime theorem below `alpha = 2/3`: both normalized power-family quadratic
coefficients are positive. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.coeff ∧
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.coeff := by
  constructor
  · simpa [powerFamilyOriginalHODLNormalizedSlippageCoeff] using
      powerFamilyOriginalHODLNormalizedSlippageCoeff_pos halpha
  · simpa [powerFamilyOriginalHODLNormalizedCurvatureSurface,
      powerFamilyOriginalHODLNormalizedQuadraticPair] using
      powerFamilyOriginalHODLNormalizedCurvatureCoeff_pos_of_lt_two_thirds
        halpha halpha_lt

/-- Regime theorem above `alpha = 2/3`: normalized slippage stays positive
while normalized curvature flips sign. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.coeff ∧
      (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.coeff < 0 := by
  constructor
  · simpa [powerFamilyOriginalHODLNormalizedSlippageCoeff] using
      powerFamilyOriginalHODLNormalizedSlippageCoeff_pos halpha
  · simpa [powerFamilyOriginalHODLNormalizedCurvatureSurface,
      powerFamilyOriginalHODLNormalizedQuadraticPair] using
      powerFamilyOriginalHODLNormalizedCurvatureCoeff_neg_of_two_thirds_lt
        halpha_gt

/-- Below the phase threshold `alpha = 2/3`, both normalized power-family
deltas are strictly positive on a punctured neighborhood of the center. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime_local_signs
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    (∀ᶠ d in 𝓝[≠] (0 : ℝ),
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d) ∧
      (∀ᶠ d in 𝓝[≠] (0 : ℝ),
        0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d) := by
  let P := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  constructor
  · exact
      (show ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.slippage.delta d from
        P.slippage.eventually_pos)
  · have hcoeff : 0 < P.curvature.coeff := by
      simpa [P, powerFamilyOriginalHODLNormalizedCurvatureSurface,
        powerFamilyOriginalHODLNormalizedQuadraticPair] using
        powerFamilyOriginalHODLNormalizedCurvatureCoeff_pos_of_lt_two_thirds
          halpha halpha_lt
    exact
      (show ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.curvature.delta d from
        P.curvature.eventually_pos_of_coeff_pos hcoeff)

/-- Above the phase threshold `alpha = 2/3`, the normalized power-family
slippage delta stays positive near the center while the normalized curvature
delta is strictly negative near the center. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime_local_signs
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    (∀ᶠ d in 𝓝[≠] (0 : ℝ),
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d) ∧
      (∀ᶠ d in 𝓝[≠] (0 : ℝ),
        (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d < 0) := by
  let P := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  constructor
  · exact
      (show ∀ᶠ d in 𝓝[≠] (0 : ℝ), 0 < P.slippage.delta d from
        P.slippage.eventually_pos)
  · have hcoeff : P.curvature.coeff < 0 := by
      simpa [P, powerFamilyOriginalHODLNormalizedCurvatureSurface,
        powerFamilyOriginalHODLNormalizedQuadraticPair] using
        powerFamilyOriginalHODLNormalizedCurvatureCoeff_neg_of_two_thirds_lt
          halpha_gt
    exact
      (show ∀ᶠ d in 𝓝[≠] (0 : ℝ), P.curvature.delta d < 0 from
        P.curvature.eventually_neg_of_coeff_neg hcoeff)

/-- Below the phase threshold `alpha = 2/3`, there is a concrete local witness
at which both normalized deltas are positive. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime_exists_witness
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    ∃ d,
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d ∧
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d := by
  let P := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  rcases powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime_local_signs
      halpha halpha_lt with ⟨hslip, hcurv⟩
  rcases (hslip.and hcurv).exists with ⟨d, hd⟩
  exact ⟨d, hd⟩

/-- Above the phase threshold `alpha = 2/3`, there is a concrete local witness
at which normalized slippage is positive while normalized curvature is
negative. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime_exists_witness
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    ∃ d,
      0 < (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d ∧
      (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d < 0 := by
  let P := powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha
  rcases powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime_local_signs
      halpha halpha_gt with ⟨hslip, hcurv⟩
  rcases (hslip.and hcurv).exists with ⟨d, hd⟩
  exact ⟨d, hd⟩

/-- Below the phase threshold `alpha = 2/3`, neither normalized coordinate can
stay globally nonpositive. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime_not_global_nonpos
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_lt : alpha < 2 / 3) :
    (¬ ∀ d,
        (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d ≤ 0) ∧
      (¬ ∀ d,
        (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d ≤ 0) := by
  rcases powerFamilyOriginalHODLNormalizedQuadraticPair_same_sign_regime_exists_witness
      halpha halpha_lt with ⟨d, hdslip, hdcurv⟩
  constructor
  · intro hglobal
    exact not_lt_of_ge (hglobal d) hdslip
  · intro hglobal
    exact not_lt_of_ge (hglobal d) hdcurv

/-- Above the phase threshold `alpha = 2/3`, normalized slippage cannot stay
globally nonpositive, and normalized curvature cannot stay globally
nonnegative. -/
theorem powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime_tradeoff
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_gt : 2 / 3 < alpha) :
    (¬ ∀ d,
        (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).slippage.delta d ≤ 0) ∧
      (¬ ∀ d,
        0 ≤ (powerFamilyOriginalHODLNormalizedQuadraticPair alpha halpha).curvature.delta d) := by
  rcases powerFamilyOriginalHODLNormalizedQuadraticPair_mixed_sign_regime_exists_witness
      halpha halpha_gt with ⟨d, hdslip, hdcurv⟩
  constructor
  · intro hglobal
    exact not_lt_of_ge (hglobal d) hdslip
  · intro hglobal
    exact not_lt_of_ge (hglobal d) hdcurv

/-- Exact coefficient gap between the normalized power-family pair and the old
`1/8` coupling law. -/
theorem powerFamilyOriginalHODLNormalizedCoeffGap_eq_factorized
    {alpha : ℝ} (halpha : 0 < alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha +
        powerFamilyOriginalHODLNormalizedSlippageCoeff alpha / 8 =
      -alpha * (3 * alpha + 4) * (alpha ^ 2 + 2 * alpha - 4) /
        (16 * (alpha + 2) ^ 3) := by
  have hden : alpha + 2 ≠ 0 := by linarith
  unfold powerFamilyOriginalHODLNormalizedCurvatureCoeff
    powerFamilyOriginalHODLNormalizedSlippageCoeff
  field_simp [hden]
  ring

/-- Exact factorization for the same-sign `1/8` coupling test.  This is the
relevant one if slippage is reoriented into a "benefit" delta with negative
leading coefficient. -/
theorem powerFamilyOriginalHODLNormalizedCoeffGap_sameSign_eq_factorized
    {alpha : ℝ} (halpha : 0 < alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha -
        powerFamilyOriginalHODLNormalizedSlippageCoeff alpha / 8 =
      -(alpha ^ 2) * (3 * alpha ^ 2 + 10 * alpha + 12) /
        (16 * (alpha + 2) ^ 3) := by
  have hden : alpha + 2 ≠ 0 := by linarith
  unfold powerFamilyOriginalHODLNormalizedCurvatureCoeff
    powerFamilyOriginalHODLNormalizedSlippageCoeff
  field_simp [hden]
  ring

/-- The same-sign `1/8` coupling law is impossible for every positive
power-family parameter. -/
theorem powerFamilyOriginalHODLNormalizedCoeffGap_sameSign_neg
    {alpha : ℝ} (halpha : 0 < alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha -
        powerFamilyOriginalHODLNormalizedSlippageCoeff alpha / 8 < 0 := by
  rw [powerFamilyOriginalHODLNormalizedCoeffGap_sameSign_eq_factorized halpha]
  have hpos :
      0 <
        alpha ^ 2 * (3 * alpha ^ 2 + 10 * alpha + 12) /
          (16 * (alpha + 2) ^ 3) := by
    positivity
  have hrewrite :
      -(alpha ^ 2) * (3 * alpha ^ 2 + 10 * alpha + 12) /
          (16 * (alpha + 2) ^ 3) =
        -(alpha ^ 2 * (3 * alpha ^ 2 + 10 * alpha + 12) /
            (16 * (alpha + 2) ^ 3)) := by
    ring
  rw [hrewrite]
  exact neg_neg_of_pos hpos

/-- No positive power-family parameter satisfies the same-sign `1/8` coupling
law.  So the old first-even separation API is structurally wrong for this
normalized family if slippage is reoriented into a benefit delta. -/
theorem powerFamilyOriginalHODLNormalizedCoeffGap_sameSign_ne_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureCoeff alpha -
        powerFamilyOriginalHODLNormalizedSlippageCoeff alpha / 8 ≠ 0 := by
  have hneg := powerFamilyOriginalHODLNormalizedCoeffGap_sameSign_neg halpha
  exact ne_of_lt hneg

end
end LocalJetFrontier
end Impossibility
end TauSwap
