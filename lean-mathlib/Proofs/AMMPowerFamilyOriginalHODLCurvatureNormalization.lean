import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proofs.AMMPowerFamilyGlobal

/-!
# Power-family original-HODL curvature normalization

This file records the curvature-side semantic boundary complementary to the
normalized slippage bridge.

For the power family against CPMM, the raw candidate-minus-baseline curvature
gap in the `d` coordinate is already nonzero at the center `d = 0`. So, just as
on the slippage side, any local bridge object must first normalize away the
center offset before asking for an even-order separation law.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

open scoped Polynomial
open Filter Topology

/-- Raw candidate-minus-CPMM original-HODL curvature gap for the power family
after substituting `w = sech(d)^2`. -/
def powerFamilyOriginalHODLCurvatureGap (alpha d : ℝ) : ℝ :=
  powerFamilyGlobalCurvatureFromSechSq alpha (sechSq d) -
    powerFamilyGlobalCurvatureFromSechSq 0 (sechSq d)

/-- The raw curvature gap has center offset `alpha / 16`. -/
theorem powerFamilyOriginalHODLCurvatureGap_zero {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    powerFamilyOriginalHODLCurvatureGap alpha 0 = alpha / 16 := by
  unfold powerFamilyOriginalHODLCurvatureGap
  simp [sechSq]
  rw [powerFamilyGlobalCurvatureFromSechSq_one halpha]
  rw [powerFamilyGlobalCurvatureFromSechSq_one (show (0 : ℝ) ≤ 0 by positivity)]
  nlinarith

/-- For positive `alpha`, the raw curvature gap is already strictly positive at
the center, so it cannot serve directly as a first-even local bridge surface. -/
theorem powerFamilyOriginalHODLCurvatureGap_zero_pos {alpha : ℝ}
    (halpha : 0 < alpha) :
    0 < powerFamilyOriginalHODLCurvatureGap alpha 0 := by
  rw [powerFamilyOriginalHODLCurvatureGap_zero (le_of_lt halpha)]
  nlinarith

/-- Center-normalized curvature gap for the power family against CPMM. -/
def powerFamilyOriginalHODLNormalizedCurvatureDelta (alpha d : ℝ) : ℝ :=
  powerFamilyOriginalHODLCurvatureGap alpha d - alpha / 16

/-- The same normalized curvature surface, but viewed directly in the
`w = sech(d)^2` coordinate. -/
def powerFamilyOriginalHODLNormalizedCurvatureFromW (alpha w : ℝ) : ℝ :=
  powerFamilyGlobalCurvatureFromSechSq alpha w - cpmmGlobalCurvatureFromSechSq w - alpha / 16

/-- The `d`-coordinate normalized curvature surface is the `w`-coordinate surface
composed with `w = sech(d)^2`. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureDelta_eq_fromW (alpha d : ℝ) :
    powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d =
      powerFamilyOriginalHODLNormalizedCurvatureFromW alpha (sechSq d) := by
  unfold powerFamilyOriginalHODLNormalizedCurvatureDelta
  unfold powerFamilyOriginalHODLCurvatureGap
  unfold powerFamilyOriginalHODLNormalizedCurvatureFromW
  rw [powerFamilyGlobalCurvatureFromSechSq_zero]

/-- The normalized `w`-coordinate curvature surface vanishes at `w = 1`. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureFromW_one {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureFromW alpha 1 = 0 := by
  unfold powerFamilyOriginalHODLNormalizedCurvatureFromW
  rw [powerFamilyGlobalCurvatureFromSechSq_one halpha]
  simp [cpmmGlobalCurvatureFromSechSq]
  ring

/-- The center-normalized curvature gap now vanishes at `d = 0`. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureDelta_zero {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    powerFamilyOriginalHODLNormalizedCurvatureDelta alpha 0 = 0 := by
  unfold powerFamilyOriginalHODLNormalizedCurvatureDelta
  rw [powerFamilyOriginalHODLCurvatureGap_zero halpha]
  ring

/-- Any curvature-side bridge surface that vanishes at the center is
incompatible with the raw power-family curvature gap for positive `alpha`. -/
theorem powerFamilyOriginalHODLCurvatureGap_ne_of_zeroAtZero {alpha : ℝ}
    (halpha : 0 < alpha) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    powerFamilyOriginalHODLCurvatureGap alpha ≠ f := by
  intro hEq
  have hcenter :
      powerFamilyOriginalHODLCurvatureGap alpha 0 = f 0 := by
    simpa using congrArg (fun g : ℝ → ℝ => g 0) hEq
  rw [powerFamilyOriginalHODLCurvatureGap_zero (le_of_lt halpha), hf0] at hcenter
  nlinarith

/-- Polynomial presentation of the power-family curvature numerator. -/
private def powerFamilyGlobalCurvaturePolyPolynomial (alpha : ℝ) : ℝ[X] :=
  Polynomial.C (alpha ^ 4) * Polynomial.X ^ 3 +
    Polynomial.C (8 * alpha ^ 3 - 4 * alpha ^ 2 - 16 * alpha) * Polynomial.X ^ 2 +
    Polynomial.C (44 * alpha ^ 2 + 80 * alpha + 32) * Polynomial.X +
    Polynomial.C (-16 * alpha ^ 2 - 32 * alpha - 16)

private lemma powerFamilyGlobalCurvaturePolyPolynomial_eval (alpha w : ℝ) :
    (powerFamilyGlobalCurvaturePolyPolynomial alpha).eval w =
      powerFamilyGlobalCurvaturePoly alpha w := by
  simp [powerFamilyGlobalCurvaturePolyPolynomial, powerFamilyGlobalCurvaturePoly]
  ring

private lemma powerFamilyGlobalCurvaturePolyPolynomial_eval_one (alpha : ℝ) :
    (powerFamilyGlobalCurvaturePolyPolynomial alpha).eval 1 = (alpha + 2) ^ 4 := by
  simp [powerFamilyGlobalCurvaturePolyPolynomial]
  ring

private lemma powerFamilyGlobalCurvaturePolyPolynomial_derivative_eval_one (alpha : ℝ) :
    (Polynomial.derivative (powerFamilyGlobalCurvaturePolyPolynomial alpha)).eval 1 =
      (alpha + 2) ^ 2 * (3 * alpha ^ 2 + 4 * alpha + 8) := by
  simp [powerFamilyGlobalCurvaturePolyPolynomial, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring_nf

/-- Polynomial presentation of the rational-part numerator. -/
private def powerFamilyGlobalCurvatureRatPartNumPolynomial (alpha : ℝ) : ℝ[X] :=
  (Polynomial.C (alpha ^ 2) * Polynomial.X + Polynomial.C (4 * alpha + 4)) *
    powerFamilyGlobalCurvaturePolyPolynomial alpha

/-- Polynomial presentation of the rational-part denominator. -/
private def powerFamilyGlobalCurvatureRatPartDenPolynomial (alpha : ℝ) : ℝ[X] :=
  Polynomial.C (16 * (alpha + 2)) *
    (Polynomial.C alpha * Polynomial.X + Polynomial.C 2) ^ 3 *
      (Polynomial.C (2 * alpha + 2) - Polynomial.C alpha * Polynomial.X)

private lemma powerFamilyGlobalCurvatureRatPartNumPolynomial_eval (alpha w : ℝ) :
    (powerFamilyGlobalCurvatureRatPartNumPolynomial alpha).eval w =
      (alpha ^ 2 * w + 4 * alpha + 4) * powerFamilyGlobalCurvaturePoly alpha w := by
  unfold powerFamilyGlobalCurvatureRatPartNumPolynomial
  rw [Polynomial.eval_mul, powerFamilyGlobalCurvaturePolyPolynomial_eval]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]
  ring

private lemma powerFamilyGlobalCurvatureRatPartDenPolynomial_eval (alpha w : ℝ) :
    (powerFamilyGlobalCurvatureRatPartDenPolynomial alpha).eval w =
      16 * (alpha + 2) * (alpha * w + 2) ^ 3 * (2 * alpha + 2 - alpha * w) := by
  simp [powerFamilyGlobalCurvatureRatPartDenPolynomial]

private lemma powerFamilyGlobalCurvaturePoly_eval_one (alpha : ℝ) :
    powerFamilyGlobalCurvaturePoly alpha 1 = (alpha + 2) ^ 4 := by
  unfold powerFamilyGlobalCurvaturePoly
  ring

private lemma powerFamilyGlobalCurvatureRatPartNumPolynomial_eval_one (alpha : ℝ) :
    (powerFamilyGlobalCurvatureRatPartNumPolynomial alpha).eval 1 = (alpha + 2) ^ 6 := by
  rw [powerFamilyGlobalCurvatureRatPartNumPolynomial_eval]
  rw [powerFamilyGlobalCurvaturePoly_eval_one]
  ring

private lemma powerFamilyGlobalCurvatureRatPartDenPolynomial_eval_one (alpha : ℝ) :
    (powerFamilyGlobalCurvatureRatPartDenPolynomial alpha).eval 1 = 16 * (alpha + 2) ^ 5 := by
  rw [powerFamilyGlobalCurvatureRatPartDenPolynomial_eval]
  ring

private lemma powerFamilyGlobalCurvatureRatPartNumPolynomial_derivative_eval_one (alpha : ℝ) :
    (Polynomial.derivative (powerFamilyGlobalCurvatureRatPartNumPolynomial alpha)).eval 1 =
      4 * (alpha + 2) ^ 4 * (alpha ^ 2 + alpha + 2) := by
  simp [powerFamilyGlobalCurvatureRatPartNumPolynomial, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X, powerFamilyGlobalCurvaturePolyPolynomial_eval_one,
    powerFamilyGlobalCurvaturePolyPolynomial_derivative_eval_one]
  ring_nf

private lemma powerFamilyGlobalCurvatureRatPartDenPolynomial_derivative_eval_one (alpha : ℝ) :
    (Polynomial.derivative (powerFamilyGlobalCurvatureRatPartDenPolynomial alpha)).eval 1 =
      32 * alpha * (alpha + 2) ^ 4 := by
  simp [powerFamilyGlobalCurvatureRatPartDenPolynomial, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X]
  ring_nf

/-- Derivative of the polynomial curvature numerator at the center. -/
private lemma powerFamilyGlobalCurvaturePoly_hasDerivAt_one (alpha : ℝ) :
    HasDerivAt (powerFamilyGlobalCurvaturePoly alpha)
      ((alpha + 2) ^ 2 * (3 * alpha ^ 2 + 4 * alpha + 8)) 1 := by
  convert (powerFamilyGlobalCurvaturePolyPolynomial alpha).hasDerivAt 1 using 1
  · ext w
    rw [powerFamilyGlobalCurvaturePolyPolynomial_eval]
  · rw [powerFamilyGlobalCurvaturePolyPolynomial_derivative_eval_one]

/-- The rational compensation factor has explicit center value. -/
private lemma powerFamilyGlobalCurvatureRatPart_one {alpha : ℝ} (halpha : 0 ≤ alpha) :
    powerFamilyGlobalCurvatureRatPart alpha 1 = (alpha + 2) / 16 := by
  have hpow : Real.rpow 1 ((alpha + 1) / (alpha + 2)) = 1 := by simp
  have hfull := powerFamilyGlobalCurvatureFromSechSq_one halpha
  rw [powerFamilyGlobalCurvatureFromSechSq_eq_rpow_mul_ratPart, hpow, one_mul] at hfull
  exact hfull

/-- Derivative of the rational compensation factor at the center. -/
private lemma powerFamilyGlobalCurvatureRatPart_hasDerivAt_one {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    HasDerivAt (powerFamilyGlobalCurvatureRatPart alpha)
      ((alpha ^ 2 + 4) / (8 * (alpha + 2))) 1 := by
  have hN := (powerFamilyGlobalCurvatureRatPartNumPolynomial alpha).hasDerivAt 1
  have hD := (powerFamilyGlobalCurvatureRatPartDenPolynomial alpha).hasDerivAt 1
  have hDne : (powerFamilyGlobalCurvatureRatPartDenPolynomial alpha).eval 1 ≠ 0 := by
    rw [powerFamilyGlobalCurvatureRatPartDenPolynomial_eval_one]
    positivity
  convert hN.div hD hDne using 1
  · ext w
    simp [powerFamilyGlobalCurvatureRatPart, powerFamilyGlobalCurvatureRatPartNumPolynomial_eval,
      powerFamilyGlobalCurvatureRatPartDenPolynomial_eval]
  · rw [powerFamilyGlobalCurvatureRatPartNumPolynomial_derivative_eval_one,
      powerFamilyGlobalCurvatureRatPartDenPolynomial_derivative_eval_one,
      powerFamilyGlobalCurvatureRatPartNumPolynomial_eval_one,
      powerFamilyGlobalCurvatureRatPartDenPolynomial_eval_one]
    have hden : alpha + 2 ≠ 0 := by positivity
    field_simp [hden]
    ring

/-- Derivative of the full power-family curvature surface at `w = 1`. -/
private lemma powerFamilyGlobalCurvatureFromSechSq_hasDerivAt_one {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    HasDerivAt (powerFamilyGlobalCurvatureFromSechSq alpha)
      ((3 * alpha ^ 2 + 3 * alpha + 10) / (16 * (alpha + 2))) 1 := by
  let p : ℝ := (alpha + 1) / (alpha + 2)
  have hpow : HasDerivAt (fun w : ℝ => w ^ p) (p * 1 ^ (p - 1)) 1 := by
    simpa [p] using (Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero))
  have hrat := powerFamilyGlobalCurvatureRatPart_hasDerivAt_one halpha
  have hmul := hpow.mul hrat
  convert hmul using 1
  · ext w
    rw [powerFamilyGlobalCurvatureFromSechSq_eq_rpow_mul_ratPart]
    rfl
  · rw [powerFamilyGlobalCurvatureRatPart_one halpha]
    have hden : alpha + 2 ≠ 0 := by positivity
    simp [p]
    field_simp [hden]
    ring

/-- Derivative of the CPMM curvature surface at `w = 1`. -/
private lemma cpmmGlobalCurvatureFromSechSq_hasDerivAt_one :
    HasDerivAt cpmmGlobalCurvatureFromSechSq (5 / 16 : ℝ) 1 := by
  have hsqrt : HasDerivAt (fun w : ℝ => Real.sqrt w) (1 / (2 * Real.sqrt 1)) 1 := by
    simpa using Real.hasDerivAt_sqrt (show (1 : ℝ) ≠ 0 by norm_num)
  have hlin : HasDerivAt (fun w : ℝ => (2 * w - 1) / 8) (1 / 4 : ℝ) 1 := by
    convert ((((hasDerivAt_id 1).const_mul (2 : ℝ)).sub_const (1 : ℝ)).div_const (8 : ℝ)) using 1
    ring
  convert hsqrt.mul hlin using 1
  · ext w
    simp [cpmmGlobalCurvatureFromSechSq, div_eq_mul_inv, mul_assoc]
  · simp
    ring

/-- The center derivative of the normalized `w`-coordinate curvature surface. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureFromW_hasDerivAt_one
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    HasDerivAt (powerFamilyOriginalHODLNormalizedCurvatureFromW alpha)
      (alpha * (3 * alpha - 2) / (16 * (alpha + 2))) 1 := by
  have hpow := powerFamilyGlobalCurvatureFromSechSq_hasDerivAt_one halpha
  have hcpmm := cpmmGlobalCurvatureFromSechSq_hasDerivAt_one
  have hsub :
      HasDerivAt
        (fun w : ℝ =>
          powerFamilyGlobalCurvatureFromSechSq alpha w -
            cpmmGlobalCurvatureFromSechSq w)
        (((3 * alpha ^ 2 + 3 * alpha + 10) / (16 * (alpha + 2))) - 5 / 16) 1 := by
    exact hpow.sub hcpmm
  have hden : alpha + 2 ≠ 0 := by positivity
  have hcoeff :
      ((3 * alpha ^ 2 + 3 * alpha + 10) / (16 * (alpha + 2)) - 5 / 16) =
        alpha * (3 * alpha - 2) / (16 * (alpha + 2)) := by
    field_simp [hden]
    ring
  change HasDerivAt
    (fun w : ℝ =>
      powerFamilyGlobalCurvatureFromSechSq alpha w -
        cpmmGlobalCurvatureFromSechSq w - alpha / 16)
    (alpha * (3 * alpha - 2) / (16 * (alpha + 2))) 1
  rw [← hcoeff]
  simpa using hsub.sub_const (alpha / 16)

/-- The coordinate change `w = sech(d)^2` tends to `1` through non-center values. -/
private lemma tendsto_sechSq_punctured :
    Tendsto sechSq (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
  have hsech : Tendsto sechSq (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt sechSq 0 := by
      unfold sechSq
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    simpa [sechSq] using hcont.tendsto.mono_left inf_le_left
  have hne : Tendsto sechSq (𝓝[≠] (0 : ℝ)) (𝓟 ({1}ᶜ)) := by
    apply tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact sechSq_ne_one hd
  rw [show 𝓝[≠] (1 : ℝ) = 𝓝 (1 : ℝ) ⊓ 𝓟 ({1}ᶜ) by rfl]
  exact tendsto_inf.2 ⟨hsech, hne⟩

/-- The normalized curvature gap starts at even order two, with explicit
quadratic coefficient after the `w = sech(d)^2` substitution. -/
theorem powerFamilyOriginalHODLNormalizedCurvatureDelta_div_sq_tendsto
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto
      (fun d => powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / d ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-alpha * (3 * alpha - 2) / (16 * (alpha + 2)))) := by
  have hcoeffDeriv :
      HasDerivAt (powerFamilyOriginalHODLNormalizedCurvatureFromW alpha)
        (alpha * (3 * alpha - 2) / (16 * (alpha + 2))) 1 :=
    powerFamilyOriginalHODLNormalizedCurvatureFromW_hasDerivAt_one (le_of_lt halpha)
  have hslope :
      Tendsto
        (fun d => slope (powerFamilyOriginalHODLNormalizedCurvatureFromW alpha) 1 (sechSq d))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (alpha * (3 * alpha - 2) / (16 * (alpha + 2)))) := by
    exact hcoeffDeriv.tendsto_slope.comp tendsto_sechSq_punctured
  have hslope_eq :
      (fun d => slope (powerFamilyOriginalHODLNormalizedCurvatureFromW alpha) 1 (sechSq d))
        =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d => powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / (sechSq d - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hneq : sechSq d ≠ 1 := sechSq_ne_one hd
    rw [slope_def_field]
    rw [powerFamilyOriginalHODLNormalizedCurvatureFromW_one (le_of_lt halpha)]
    rw [← powerFamilyOriginalHODLNormalizedCurvatureDelta_eq_fromW]
    field_simp [hneq]
    simp
  have hratio :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / (sechSq d - 1))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (alpha * (3 * alpha - 2) / (16 * (alpha + 2)))) := by
    exact hslope.congr' hslope_eq
  have hmul :
      Tendsto
        (fun d =>
          (powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / (sechSq d - 1)) *
            ((sechSq d - 1) / d ^ 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((alpha * (3 * alpha - 2) / (16 * (alpha + 2))) * (-1))) := by
    simpa using hratio.mul sechSq_sub_one_div_sq_tendsto
  have hrewrite :
      (fun d => powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / d ^ 2)
        =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d =>
            (powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / (sechSq d - 1)) *
              ((sechSq d - 1) / d ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hneq : sechSq d - 1 ≠ 0 := sub_ne_zero.mpr (sechSq_ne_one hd)
    have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
    field_simp [hneq, hd, hd2]
  have hmain :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedCurvatureDelta alpha d / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((alpha * (3 * alpha - 2) / (16 * (alpha + 2))) * (-1))) := by
    exact hmul.congr' hrewrite.symm
  have htarget :
      (alpha * (3 * alpha - 2) / (16 * (alpha + 2))) * (-1) =
        -alpha * (3 * alpha - 2) / (16 * (alpha + 2)) := by
    ring
  simpa [htarget] using hmain

end
end LocalJetFrontier
end Impossibility
end TauSwap
