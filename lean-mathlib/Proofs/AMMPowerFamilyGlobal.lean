import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Proofs.AMMLocalJetFrontier

/-!
# Power-family global no-free-lunch facts

This file records the first concrete bridge fact for the global AMM frontier
program.  For the power family `K_alpha(x,y)=x*y*(x+y)^alpha`, after the
substitution `w = sech(d)^2`, the original-HODL global slippage coefficient is
the rational expression below, while the curvature coefficient separates into a
real-power factor and a rational compensation factor.  The final theorem in the
main block proves the concrete no-free-lunch comparison against CPMM on the
convexity band: positive `alpha` strictly improves global slippage but cannot
also improve the original-HODL curvature coefficient.
-/

namespace TauSwap
namespace Impossibility
namespace LocalJetFrontier

noncomputable section

open Filter Topology

/-- Original-HODL global slippage coefficient for
`K_alpha(x,y)=x*y*(x+y)^alpha`, written in the coordinate
`w = sech(d)^2`.

For `alpha = 0`, this specializes to the CPMM value `1`. -/
def powerFamilyGlobalSlippageFromSechSq (alpha w : ℝ) : ℝ :=
  2 * (2 * (alpha + 1) - alpha * w) /
    (4 * (alpha + 1) + alpha ^ 2 * w)

/-- CPMM has global original-HODL slippage coefficient `1` in the same
coordinate. -/
lemma powerFamilyGlobalSlippageFromSechSq_zero (w : ℝ) :
    powerFamilyGlobalSlippageFromSechSq 0 w = 1 := by
  norm_num [powerFamilyGlobalSlippageFromSechSq]

/-- Nonnegative power-family parameter never has worse global slippage than
CPMM in the `w = sech(d)^2` coordinate. -/
theorem power_family_global_slippage_le_cpmm {alpha w : ℝ}
    (halpha : 0 ≤ alpha) (hw : 0 ≤ w) :
    powerFamilyGlobalSlippageFromSechSq alpha w ≤ 1 := by
  unfold powerFamilyGlobalSlippageFromSechSq
  have hden_pos : 0 < 4 * (alpha + 1) + alpha ^ 2 * w := by
    have hbase : 0 < 4 * (alpha + 1) := by positivity
    have hquad : 0 ≤ alpha ^ 2 * w := mul_nonneg (sq_nonneg alpha) hw
    positivity
  rw [div_le_one hden_pos]
  nlinarith [mul_nonneg halpha hw, sq_nonneg alpha]

/-- Positive power-family parameter has strictly better global slippage than
CPMM at any nonzero `w = sech(d)^2` point. -/
theorem power_family_global_slippage_lt_cpmm {alpha w : ℝ}
    (halpha : 0 < alpha) (hw : 0 < w) :
    powerFamilyGlobalSlippageFromSechSq alpha w < 1 := by
  unfold powerFamilyGlobalSlippageFromSechSq
  have hden_pos : 0 < 4 * (alpha + 1) + alpha ^ 2 * w := by positivity
  rw [div_lt_one hden_pos]
  nlinarith [mul_pos halpha hw, sq_pos_of_pos halpha]

/-!
### Local-normalized `d`-coordinate slippage delta

The global slippage surface above is expressed in the coordinate `w = sech(d)^2`,
but its raw candidate-minus-CPMM gap is already nonzero at `d = 0`.  For the
first-even bridge we instead want the center-normalized local gap, so that the
leading separation really starts at an even order.
-/

/-- The coordinate `w = sech(d)^2`, written using only `cosh`. -/
def sechSq (d : ℝ) : ℝ :=
  (Real.cosh d ^ 2)⁻¹

/-- Center-normalized original-HODL slippage gap for the power family against
CPMM after substituting `w = sech(d)^2`.

The subtraction by `2 / (alpha + 2)` removes the nonzero center offset, so the
remaining local gap vanishes at `d = 0`. -/
def powerFamilyOriginalHODLNormalizedSlippageDelta (alpha d : ℝ) : ℝ :=
  powerFamilyGlobalSlippageFromSechSq alpha (sechSq d) - 2 / (alpha + 2)

/-- Explicit closed form of the center-normalized slippage gap. -/
lemma powerFamilyOriginalHODLNormalizedSlippageDelta_eq
    {alpha d : ℝ} (halpha : 0 < alpha) (halpha2 : alpha + 2 ≠ 0) :
    powerFamilyOriginalHODLNormalizedSlippageDelta alpha d =
      4 * alpha * (alpha + 1) * Real.sinh d ^ 2 /
        ((alpha + 2) *
          (alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2)) := by
  unfold powerFamilyOriginalHODLNormalizedSlippageDelta
  unfold powerFamilyGlobalSlippageFromSechSq sechSq
  have hcosh_sq_ne : Real.cosh d ^ 2 ≠ 0 := by positivity
  have hden_ne : alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2 ≠ 0 := by
    have hden_pos : 0 < alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2 := by
      positivity
    exact ne_of_gt hden_pos
  field_simp [halpha2, hcosh_sq_ne, hden_ne]
  rw [Real.cosh_sq d]
  ring_nf

/-- The center-normalized local slippage gap vanishes at the center. -/
lemma powerFamilyOriginalHODLNormalizedSlippageDelta_zero
    {alpha : ℝ} (halpha : 0 < alpha) (halpha2 : alpha + 2 ≠ 0) :
    powerFamilyOriginalHODLNormalizedSlippageDelta alpha 0 = 0 := by
  rw [powerFamilyOriginalHODLNormalizedSlippageDelta_eq halpha halpha2]
  simp

/-- Leading-ratio form of the center-normalized slippage gap after dividing by
`d^2`. -/
def powerFamilyOriginalHODLNormalizedSlippageLeadingRatio (alpha d : ℝ) : ℝ :=
  4 * alpha * (alpha + 1) * (Real.sinh d / d) ^ 2 /
    ((alpha + 2) *
      (alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2))

/-- Away from the center, dividing the normalized slippage gap by `d^2`
produces the explicit leading-ratio form. -/
lemma powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_eventuallyEq
    {alpha : ℝ} (halpha : 0 < alpha) (halpha2 : alpha + 2 ≠ 0) :
    (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
      =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun d => powerFamilyOriginalHODLNormalizedSlippageLeadingRatio alpha d) := by
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [powerFamilyOriginalHODLNormalizedSlippageDelta_eq halpha halpha2]
  unfold powerFamilyOriginalHODLNormalizedSlippageLeadingRatio
  have hd2 : d ^ 2 ≠ 0 := by exact pow_ne_zero 2 hd
  field_simp [halpha2, hd, hd2]

private theorem sinh_div_tendsto :
    Tendsto (fun d => Real.sinh d / d) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa [div_eq_inv_mul] using
    (Real.hasDerivAt_sinh 0).tendsto_slope_zero

private theorem cosh_sq_tendsto :
    Tendsto (fun d : ℝ => Real.cosh d ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hcont : ContinuousAt (fun x : ℝ => Real.cosh x ^ 2) 0 := by
    fun_prop
  simpa using hcont.tendsto.mono_left inf_le_left

/-- Away from the center, the coordinate change `w = sech(d)^2` is never equal
to `1`. -/
lemma sechSq_ne_one {d : ℝ} (hd : d ≠ 0) : sechSq d ≠ 1 := by
  intro h
  unfold sechSq at h
  have hcosh_sq_ne : Real.cosh d ^ 2 ≠ 0 := by positivity
  have hmul := congrArg (fun x : ℝ => x * (Real.cosh d ^ 2)) h
  have hcosh_sq_eq : Real.cosh d ^ 2 = 1 := by
    have htmp : (1 : ℝ) = Real.cosh d ^ 2 := by
      simpa [hcosh_sq_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact htmp.symm
  have hsinh_sq_eq : Real.sinh d ^ 2 = 0 := by
    nlinarith [Real.cosh_sq d, hcosh_sq_eq]
  have hsinh_eq : Real.sinh d = 0 := by
    nlinarith
  exact hd (Real.sinh_eq_zero.mp hsinh_eq)

/-- The shifted coordinate `sechSq(d) - 1` tends to `0` through nonzero values
on the punctured neighborhood of the center. -/
theorem tendsto_sechSq_sub_one_punctured :
    Tendsto (fun d => sechSq d - 1) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  have hsech : Tendsto sechSq (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt sechSq 0 := by
      unfold sechSq
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    simpa [sechSq] using hcont.tendsto.mono_left inf_le_left
  have hsub : Tendsto (fun d => sechSq d - 1) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hsech.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) _ _)
  have hne : Tendsto (fun d => sechSq d - 1) (𝓝[≠] (0 : ℝ)) (𝓟 ({0}ᶜ)) := by
    apply tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact sub_ne_zero.mpr (sechSq_ne_one hd)
  rw [show (𝓝[≠] (0 : ℝ)) = 𝓝 (0 : ℝ) ⊓ 𝓟 ({0}ᶜ) by rfl]
  exact tendsto_inf.2 ⟨hsub, hne⟩

/-- The coordinate change `w = sech(d)^2` satisfies `w - 1 = -d^2 + o(d^2)` at
the center. -/
theorem sechSq_sub_one_div_sq_tendsto :
    Tendsto
      (fun d => (sechSq d - 1) / d ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-1 : ℝ)) := by
  have hsinh_sq :
      Tendsto (fun d => (Real.sinh d / d) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa [pow_two] using sinh_div_tendsto.mul sinh_div_tendsto
  have hsech_sq :
      Tendsto (fun d : ℝ => (Real.cosh d ^ 2)⁻¹)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun x : ℝ => (Real.cosh x ^ 2)⁻¹) 0 := by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    simpa using hcont.tendsto.mono_left inf_le_left
  have hmain :
      Tendsto
        (fun d => (-((Real.sinh d / d) ^ 2)) * (Real.cosh d ^ 2)⁻¹)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-1 : ℝ)) := by
    simpa using hsinh_sq.neg.mul hsech_sq
  have hrewrite :
      (fun d => (sechSq d - 1) / d ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun d => (-((Real.sinh d / d) ^ 2)) * (Real.cosh d ^ 2)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    unfold sechSq
    have hcosh_sq_ne : Real.cosh d ^ 2 ≠ 0 := by positivity
    have hd2 : d ^ 2 ≠ 0 := by exact pow_ne_zero 2 hd
    field_simp [hcosh_sq_ne, hd, hd2]
    rw [Real.cosh_sq d]
    ring
  exact hmain.congr' hrewrite.symm

/-- The center-normalized power-family slippage gap starts at even order two,
with coefficient `4*alpha*(alpha+1)/(alpha+2)^3`. -/
theorem powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_tendsto
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto
      (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (4 * alpha * (alpha + 1) / (alpha + 2) ^ 3)) := by
  have halpha2 : alpha + 2 ≠ 0 := by linarith
  have hsinh_sq :
      Tendsto (fun d => (Real.sinh d / d) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa [pow_two] using sinh_div_tendsto.mul sinh_div_tendsto
  have hden_inner :
      Tendsto
        (fun d => alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (alpha ^ 2 + 4 * alpha + 4)) := by
    have hconst :
        Tendsto (fun _ : ℝ => alpha ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (alpha ^ 2)) :=
      tendsto_const_nhds
    have hcosh_scaled :
        Tendsto (fun d : ℝ => (4 * alpha + 4) * (Real.cosh d ^ 2))
          (𝓝[≠] (0 : ℝ)) (𝓝 ((4 * alpha + 4) * 1)) := by
      simpa using cosh_sq_tendsto.const_mul (4 * alpha + 4)
    convert hconst.add hcosh_scaled using 1
    · ext d
      ring_nf
    · ring_nf
  have hden :
      Tendsto
        (fun d =>
          (alpha + 2) *
            (alpha ^ 2 + 4 * alpha * Real.cosh d ^ 2 + 4 * Real.cosh d ^ 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝 ((alpha + 2) * (alpha ^ 2 + 4 * alpha + 4))) := by
    simpa using hden_inner.const_mul (alpha + 2)
  have hratio :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedSlippageLeadingRatio alpha d)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (4 * alpha * (alpha + 1) * 1 /
            ((alpha + 2) * (alpha ^ 2 + 4 * alpha + 4)))) := by
    unfold powerFamilyOriginalHODLNormalizedSlippageLeadingRatio
    have hnum :
        Tendsto
          (fun d => 4 * alpha * (alpha + 1) * (Real.sinh d / d) ^ 2)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (4 * alpha * (alpha + 1) * 1)) := by
      simpa using hsinh_sq.const_mul (4 * alpha * (alpha + 1))
    have hden_ne : (alpha + 2) * (alpha ^ 2 + 4 * alpha + 4) ≠ 0 := by
      have h1 : alpha + 2 ≠ 0 := by linarith
      have h2 : alpha ^ 2 + 4 * alpha + 4 ≠ 0 := by
        have hpos : 0 < alpha ^ 2 + 4 * alpha + 4 := by nlinarith
        linarith
      exact mul_ne_zero h1 h2
    exact Tendsto.div hnum hden hden_ne
  have htarget :
      4 * alpha * (alpha + 1) /
          ((alpha + 2) * (alpha ^ 2 + 4 * alpha + 4)) =
        4 * alpha * (alpha + 1) / (alpha + 2) ^ 3 := by
    field_simp [halpha2]
    ring
  have hmain :
      Tendsto
        (fun d => powerFamilyOriginalHODLNormalizedSlippageDelta alpha d / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (4 * alpha * (alpha + 1) * 1 /
            ((alpha + 2) * (alpha ^ 2 + 4 * alpha + 4)))) :=
    Tendsto.congr'
      (powerFamilyOriginalHODLNormalizedSlippageDelta_div_sq_eventuallyEq halpha halpha2).symm
      hratio
  simpa [htarget] using hmain

/-- CPMM original-HODL curvature coefficient in the coordinate
`w = sech(d)^2`. -/
def cpmmGlobalCurvatureFromSechSq (w : ℝ) : ℝ :=
  Real.sqrt w * (2 * w - 1) / 8

/-- Polynomial numerator appearing in the power-family global original-HODL
curvature coefficient after symbolic differentiation. -/
def powerFamilyGlobalCurvaturePoly (alpha w : ℝ) : ℝ :=
  alpha ^ 4 * w ^ 3 +
    8 * alpha ^ 3 * w ^ 2 -
    4 * alpha ^ 2 * w ^ 2 +
    44 * alpha ^ 2 * w -
    16 * alpha ^ 2 -
    16 * alpha * w ^ 2 +
    80 * alpha * w -
    32 * alpha +
    32 * w -
    16

/-- Power-family original-HODL curvature coefficient in the coordinate
`w = sech(d)^2`. -/
def powerFamilyGlobalCurvatureFromSechSq (alpha w : ℝ) : ℝ :=
  Real.rpow w ((alpha + 1) / (alpha + 2)) *
    (alpha ^ 2 * w + 4 * alpha + 4) *
    powerFamilyGlobalCurvaturePoly alpha w /
    (16 * (alpha + 2) * (alpha * w + 2) ^ 3 *
      (2 * alpha + 2 - alpha * w))

/-- The rational factor of the power-family curvature expression.  Separating
this from the `w^p` term makes the global curvature comparison split into an
algebraic compensation inequality and a real-power lower bound. -/
def powerFamilyGlobalCurvatureRatPart (alpha w : ℝ) : ℝ :=
  (alpha ^ 2 * w + 4 * alpha + 4) *
    powerFamilyGlobalCurvaturePoly alpha w /
    (16 * (alpha + 2) * (alpha * w + 2) ^ 3 *
      (2 * alpha + 2 - alpha * w))

/-- The curvature expression factors as `w^p` times a rational part. -/
lemma powerFamilyGlobalCurvatureFromSechSq_eq_rpow_mul_ratPart (alpha w : ℝ) :
    powerFamilyGlobalCurvatureFromSechSq alpha w =
      Real.rpow w ((alpha + 1) / (alpha + 2)) *
        powerFamilyGlobalCurvatureRatPart alpha w := by
  unfold powerFamilyGlobalCurvatureFromSechSq powerFamilyGlobalCurvatureRatPart
  ring

/-- Polynomial certificate for the rational compensation step in the
`beta = alpha/(alpha+2)`, `t = 1-w` coordinates.  The variable `y` is the
normalized interval coordinate `y = 2*t`, so `0 <= y <= 1` corresponds to the
convexity band `1/2 <= w <= 1`. -/
def powerFamilyCurvatureLowerBoundPolyBeta (beta y : ℝ) : ℝ :=
  beta ^ 5 * y ^ 4 / 16 -
    beta ^ 3 * y ^ 4 / 8 -
    5 * beta ^ 3 * y ^ 3 / 8 +
    3 * beta ^ 3 * y ^ 2 / 4 +
    beta ^ 2 * y ^ 4 / 8 +
    3 * beta ^ 2 * y ^ 3 / 8 -
    3 * beta ^ 2 * y ^ 2 / 4 -
    beta * y ^ 3 / 4 +
    5 * beta * y ^ 2 / 2 -
    5 * beta * y / 2 -
    y ^ 2 +
    y / 2 +
    1

/-- Bernstein-basis certificate for nonnegativity of the lower-bound
polynomial on the unit square.  This is intentionally explicit: each summand is
nonnegative under `0 <= beta <= 1` and `0 <= y <= 1`. -/
lemma powerFamilyCurvatureLowerBoundPolyBeta_bernstein (beta y : ℝ) :
    powerFamilyCurvatureLowerBoundPolyBeta beta y =
      (1 - beta) ^ 5 * (1 - y) ^ 4
      + (9 / 2 : ℝ) * (1 - beta) ^ 5 * y * (1 - y) ^ 3
      + (13 / 2 : ℝ) * (1 - beta) ^ 5 * y ^ 2 * (1 - y) ^ 2
      + (7 / 2 : ℝ) * (1 - beta) ^ 5 * y ^ 3 * (1 - y)
      + (1 / 2 : ℝ) * (1 - beta) ^ 5 * y ^ 4
      + (5 : ℝ) * beta * (1 - beta) ^ 4 * (1 - y) ^ 4
      + (20 : ℝ) * beta * (1 - beta) ^ 4 * y * (1 - y) ^ 3
      + (55 / 2 : ℝ) * beta * (1 - beta) ^ 4 * y ^ 2 * (1 - y) ^ 2
      + (59 / 4 : ℝ) * beta * (1 - beta) ^ 4 * y ^ 3 * (1 - y)
      + (9 / 4 : ℝ) * beta * (1 - beta) ^ 4 * y ^ 4
      + (10 : ℝ) * beta ^ 2 * (1 - beta) ^ 3 * (1 - y) ^ 4
      + (35 : ℝ) * beta ^ 2 * (1 - beta) ^ 3 * y * (1 - y) ^ 3
      + (177 / 4 : ℝ) * beta ^ 2 * (1 - beta) ^ 3 * y ^ 2 * (1 - y) ^ 2
      + (183 / 8 : ℝ) * beta ^ 2 * (1 - beta) ^ 3 * y ^ 3 * (1 - y)
      + (15 / 4 : ℝ) * beta ^ 2 * (1 - beta) ^ 3 * y ^ 4
      + (10 : ℝ) * beta ^ 3 * (1 - beta) ^ 2 * (1 - y) ^ 4
      + (30 : ℝ) * beta ^ 3 * (1 - beta) ^ 2 * y * (1 - y) ^ 3
      + (67 / 2 : ℝ) * beta ^ 3 * (1 - beta) ^ 2 * y ^ 2 * (1 - y) ^ 2
      + (16 : ℝ) * beta ^ 3 * (1 - beta) ^ 2 * y ^ 3 * (1 - y)
      + (11 / 4 : ℝ) * beta ^ 3 * (1 - beta) ^ 2 * y ^ 4
      + (5 : ℝ) * beta ^ 4 * (1 - beta) * (1 - y) ^ 4
      + (25 / 2 : ℝ) * beta ^ 4 * (1 - beta) * y * (1 - y) ^ 3
      + (47 / 4 : ℝ) * beta ^ 4 * (1 - beta) * y ^ 2 * (1 - y) ^ 2
      + (39 / 8 : ℝ) * beta ^ 4 * (1 - beta) * y ^ 3 * (1 - y)
      + (3 / 4 : ℝ) * beta ^ 4 * (1 - beta) * y ^ 4
      + beta ^ 5 * (1 - y) ^ 4
      + (2 : ℝ) * beta ^ 5 * y * (1 - y) ^ 3
      + (3 / 2 : ℝ) * beta ^ 5 * y ^ 2 * (1 - y) ^ 2
      + (1 / 2 : ℝ) * beta ^ 5 * y ^ 3 * (1 - y)
      + (1 / 16 : ℝ) * beta ^ 5 * y ^ 4 := by
  unfold powerFamilyCurvatureLowerBoundPolyBeta
  ring

/-- The rational lower-bound polynomial is nonnegative on the normalized
rectangle. -/
lemma powerFamilyCurvatureLowerBoundPolyBeta_nonneg {beta y : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ powerFamilyCurvatureLowerBoundPolyBeta beta y := by
  have hbeta_tail : 0 ≤ 1 - beta := by linarith
  have hy_tail : 0 ≤ 1 - y := by linarith
  rw [powerFamilyCurvatureLowerBoundPolyBeta_bernstein]
  positivity

/-- The rational part of the curvature expression after the substitution
`beta = alpha/(alpha+2)` and `t = 1-w`. -/
def powerFamilyGlobalCurvatureRatPartBeta (beta t : ℝ) : ℝ :=
  (1 - beta ^ 2 * t) *
    (- beta ^ 4 * t ^ 3 +
      5 * beta ^ 2 * t ^ 2 -
      3 * beta ^ 2 * t -
      2 * beta * t ^ 2 +
      2 * beta * t -
      2 * t +
      1) /
    (8 * (1 - beta) * (1 - beta * t) ^ 3 * (1 + beta * t))

/-!
### Interval facts for the beta/t coordinate

The global curvature comparison repeatedly uses the same rectangle

```text
0 <= beta < 1,  0 <= t <= 1/2.
```

The following lemmas keep that coordinate change explicit instead of burying the
domain arithmetic inside the main proof.
-/

lemma betaT_two_mul_le_one {t : ℝ} (ht1 : t ≤ 1 / 2) :
    2 * t ≤ 1 := by
  nlinarith

lemma betaT_mul_lt_one {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (ht1 : t ≤ 1 / 2) :
    beta * t < 1 := by
  have hbt_le : beta * t ≤ beta * (1 / 2) :=
    mul_le_mul_of_nonneg_left ht1 hbeta0
  nlinarith

lemma betaT_one_sub_mul_pos {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (ht1 : t ≤ 1 / 2) :
    0 < 1 - beta * t :=
  sub_pos.mpr (betaT_mul_lt_one hbeta0 hbeta1 ht1)

lemma betaT_cpmm_factor_nonneg {t : ℝ} (ht1 : t ≤ 1 / 2) :
    0 ≤ (1 - 2 * t) / 8 := by
  have hnum : 0 ≤ 1 - 2 * t := sub_nonneg.mpr (betaT_two_mul_le_one ht1)
  positivity

lemma betaT_one_sub_t_pos {t : ℝ} (ht1 : t ≤ 1 / 2) :
    0 < 1 - t := by
  nlinarith

lemma betaT_beta_div_two_le_one {beta : ℝ} (hbeta1 : beta < 1) :
    beta / 2 ≤ 1 := by
  nlinarith

lemma powerFamilyBand_w_pos {w : ℝ} (hwlo : (1 / 2 : ℝ) ≤ w) :
    0 < w := by
  nlinarith

lemma powerFamilyBand_t_nonneg {w : ℝ} (hwle : w ≤ 1) :
    0 ≤ 1 - w :=
  sub_nonneg.mpr hwle

lemma powerFamilyBand_t_le_half {w : ℝ} (hwlo : (1 / 2 : ℝ) ≤ w) :
    1 - w ≤ 1 / 2 := by
  nlinarith

lemma powerFamilyBeta_nonneg {alpha : ℝ} (halpha : 0 ≤ alpha) :
    0 ≤ alpha / (alpha + 2) := by
  positivity

lemma powerFamilyBeta_lt_one {alpha : ℝ} (halpha : 0 ≤ alpha) :
    alpha / (alpha + 2) < 1 := by
  have hden_pos : 0 < alpha + 2 := by positivity
  rw [div_lt_one hden_pos]
  linarith

/-- The rational compensation inequality needed for the global curvature
comparison.  It says that the rational part of the power-family curvature
offsets at least the linear lower bound `1 - beta*t` for the exponent term. -/
lemma powerFamilyGlobalCurvatureRatPartBeta_lower {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t ≥
      (1 - 2 * t) / 8 := by
  have hbeta_le_one : beta ≤ 1 := le_of_lt hbeta1
  have hy0 : 0 ≤ 2 * t := by positivity
  have hy1 : 2 * t ≤ 1 := betaT_two_mul_le_one ht1
  have hpoly : 0 ≤ powerFamilyCurvatureLowerBoundPolyBeta beta (2 * t) :=
    powerFamilyCurvatureLowerBoundPolyBeta_nonneg hbeta0 hbeta_le_one hy0 hy1
  have h_one_sub_beta : 0 < 1 - beta := sub_pos.mpr hbeta1
  have hbt_nonneg : 0 ≤ beta * t := mul_nonneg hbeta0 ht0
  have hbt_lt_one : beta * t < 1 := betaT_mul_lt_one hbeta0 hbeta1 ht1
  have h_one_sub_bt : 0 < 1 - beta * t :=
    betaT_one_sub_mul_pos hbeta0 hbeta1 ht1
  have h_one_add_bt : 0 < 1 + beta * t := by positivity
  have hden_pos : 0 < 8 * (1 - beta) * (1 - beta * t) ^ 2 * (1 + beta * t) := by
    positivity
  have hrat_den_pos : 0 < 8 * (1 - beta) * (1 - beta * t) ^ 3 * (1 + beta * t) := by
    positivity
  have hdiff :
      0 ≤ (1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t -
        (1 - 2 * t) / 8 := by
    have hrewrite :
        (1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t -
            (1 - 2 * t) / 8 =
          beta * powerFamilyCurvatureLowerBoundPolyBeta beta (2 * t) /
            (8 * (1 - beta) * (1 - beta * t) ^ 2 * (1 + beta * t)) := by
      unfold powerFamilyGlobalCurvatureRatPartBeta
        powerFamilyCurvatureLowerBoundPolyBeta
      field_simp [hden_pos.ne', hrat_den_pos.ne']
      ring_nf
    rw [hrewrite]
    exact div_nonneg (mul_nonneg hbeta0 hpoly) (le_of_lt hden_pos)
  linarith

/-- The beta/t rational curvature part is nonnegative on the comparison
rectangle. -/
lemma powerFamilyGlobalCurvatureRatPartBeta_nonneg {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    0 ≤ powerFamilyGlobalCurvatureRatPartBeta beta t := by
  have hlower := powerFamilyGlobalCurvatureRatPartBeta_lower hbeta0 hbeta1 ht0 ht1
  have hfactor_pos : 0 < 1 - beta * t :=
    betaT_one_sub_mul_pos hbeta0 hbeta1 ht1
  have hrhs_nonneg : 0 ≤ (1 - 2 * t) / 8 := betaT_cpmm_factor_nonneg ht1
  have hprod : 0 ≤ (1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t :=
    hrhs_nonneg.trans hlower
  have hdiv :
      0 ≤ ((1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t) /
        (1 - beta * t) :=
    div_nonneg hprod (le_of_lt hfactor_pos)
  have hcancel :
      ((1 - beta * t) * powerFamilyGlobalCurvatureRatPartBeta beta t) /
          (1 - beta * t) =
        powerFamilyGlobalCurvatureRatPartBeta beta t := by
    field_simp [hfactor_pos.ne']
  rwa [hcancel] at hdiv

/-- Real-power lower bound for the beta/t curvature comparison.  The proof
uses Bernoulli on the reciprocal `(1-t)^(-beta/2)`, then inverts. -/
lemma rpow_one_sub_ge_one_sub_beta_mul {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    1 - beta * t ≤ Real.rpow (1 - t) (beta / 2) := by
  have hbase_pos : 0 < 1 - t := betaT_one_sub_t_pos ht1
  have hp0 : 0 ≤ beta / 2 := by positivity
  have hp1 : beta / 2 ≤ 1 := betaT_beta_div_two_le_one hbeta1
  have hs_nonneg : 0 ≤ t / (1 - t) := div_nonneg ht0 (le_of_lt hbase_pos)
  have hs : -1 ≤ t / (1 - t) := by linarith
  have hbern := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have hbase_eq : 1 + t / (1 - t) = (1 - t)⁻¹ := by
    field_simp [hbase_pos.ne']
    ring
  have hratio : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ hbase_pos]
    nlinarith
  have hscaled : 1 + (beta / 2) * (t / (1 - t)) ≤ 1 + beta * t := by
    have hmul := mul_le_mul_of_nonneg_left hratio hp0
    nlinarith
  have hinvpow_le : (Real.rpow (1 - t) (beta / 2))⁻¹ ≤ 1 + beta * t := by
    calc
      (Real.rpow (1 - t) (beta / 2))⁻¹ =
          Real.rpow ((1 - t)⁻¹) (beta / 2) := by
        exact (Real.inv_rpow (le_of_lt hbase_pos) (beta / 2)).symm
      _ = Real.rpow (1 + t / (1 - t)) (beta / 2) := by rw [hbase_eq]
      _ ≤ 1 + (beta / 2) * (t / (1 - t)) := hbern
      _ ≤ 1 + beta * t := hscaled
  have hpow_pos : 0 < Real.rpow (1 - t) (beta / 2) :=
    Real.rpow_pos_of_pos hbase_pos _
  have hlin_pos : 0 < 1 + beta * t := by positivity
  have hrecip : (1 + beta * t)⁻¹ ≤ Real.rpow (1 - t) (beta / 2) :=
    (inv_le_comm₀ hpow_pos hlin_pos).mp hinvpow_le
  have hone_sub_le_inv : 1 - beta * t ≤ (1 + beta * t)⁻¹ := by
    rw [inv_eq_one_div]
    rw [le_div_iff₀ hlin_pos]
    nlinarith [sq_nonneg (beta * t)]
  exact hone_sub_le_inv.trans hrecip

/-- Core beta/t curvature comparison after separating the common nonnegative
`sqrt(1-t)` factor. -/
theorem powerFamilyGlobalCurvatureBeta_core_ge_cpmm_rat {beta t : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (1 - 2 * t) / 8 ≤
      Real.rpow (1 - t) (beta / 2) *
        powerFamilyGlobalCurvatureRatPartBeta beta t := by
  have hlower := powerFamilyGlobalCurvatureRatPartBeta_lower hbeta0 hbeta1 ht0 ht1
  have hpow_lower := rpow_one_sub_ge_one_sub_beta_mul hbeta0 hbeta1 ht0 ht1
  have hrat_nonneg := powerFamilyGlobalCurvatureRatPartBeta_nonneg hbeta0 hbeta1 ht0 ht1
  exact hlower.trans (mul_le_mul_of_nonneg_right hpow_lower hrat_nonneg)

/-- The alpha/w rational factor equals the beta/t rational factor under
`beta = alpha/(alpha+2)` and `t = 1-w`. -/
lemma powerFamilyGlobalCurvatureRatPart_eq_beta {alpha w : ℝ}
    (halpha : 0 ≤ alpha) :
    powerFamilyGlobalCurvatureRatPart alpha w =
      powerFamilyGlobalCurvatureRatPartBeta (alpha / (alpha + 2)) (1 - w) := by
  have hden : alpha + 2 ≠ 0 := by positivity
  unfold powerFamilyGlobalCurvatureRatPart powerFamilyGlobalCurvatureRatPartBeta
    powerFamilyGlobalCurvaturePoly
  field_simp [hden]
  ring_nf

/-- On the original-HODL convexity band, nonnegative power-family parameter has
at least CPMM's global curvature coefficient.  Combined with the slippage
theorems above, this gives the concrete global no-free-lunch direction for the
power family: improving global slippage over CPMM does not improve curvature. -/
theorem power_family_global_curvature_ge_cpmm {alpha w : ℝ}
    (halpha : 0 ≤ alpha) (hwlo : (1 / 2 : ℝ) ≤ w) (hwle : w ≤ 1) :
    cpmmGlobalCurvatureFromSechSq w ≤
      powerFamilyGlobalCurvatureFromSechSq alpha w := by
  let beta : ℝ := alpha / (alpha + 2)
  let t : ℝ := 1 - w
  have hw_pos : 0 < w := by nlinarith
  have hden_pos : 0 < alpha + 2 := by positivity
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta]
    exact powerFamilyBeta_nonneg halpha
  have hbeta1 : beta < 1 := by
    dsimp [beta]
    exact powerFamilyBeta_lt_one halpha
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact powerFamilyBand_t_nonneg hwle
  have ht1 : t ≤ 1 / 2 := by
    dsimp [t]
    exact powerFamilyBand_t_le_half hwlo
  have hcore := powerFamilyGlobalCurvatureBeta_core_ge_cpmm_rat hbeta0 hbeta1 ht0 ht1
  have hcore_w :
      (2 * w - 1) / 8 ≤
        Real.rpow w (beta / 2) *
          powerFamilyGlobalCurvatureRatPartBeta beta (1 - w) := by
    convert hcore using 1 <;> dsimp [t] <;> ring_nf
  have hmul := mul_le_mul_of_nonneg_left hcore_w (Real.sqrt_nonneg w)
  have hright_eq :
      Real.sqrt w *
          (Real.rpow w (beta / 2) *
            powerFamilyGlobalCurvatureRatPartBeta beta (1 - w)) =
        powerFamilyGlobalCurvatureFromSechSq alpha w := by
    rw [powerFamilyGlobalCurvatureFromSechSq_eq_rpow_mul_ratPart]
    rw [powerFamilyGlobalCurvatureRatPart_eq_beta halpha]
    dsimp [beta]
    have hexp :
        (alpha + 1) / (alpha + 2) =
          1 / 2 + (alpha / (alpha + 2)) / 2 := by
      field_simp [ne_of_gt hden_pos]
      ring
    rw [hexp]
    rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_add hw_pos]
    ring
  have hleft_eq :
      Real.sqrt w * ((2 * w - 1) / 8) = cpmmGlobalCurvatureFromSechSq w := by
    unfold cpmmGlobalCurvatureFromSechSq
    ring
  rw [hleft_eq, hright_eq] at hmul
  exact hmul

/-- Concrete global no-free-lunch theorem for the power family against CPMM:
strictly improving global original-HODL slippage on the convexity band comes
with no improvement in the global curvature coefficient. -/
theorem power_family_global_no_free_lunch_vs_cpmm {alpha w : ℝ}
    (halpha : 0 < alpha) (hwlo : (1 / 2 : ℝ) ≤ w) (hwle : w ≤ 1) :
    powerFamilyGlobalSlippageFromSechSq alpha w <
        powerFamilyGlobalSlippageFromSechSq 0 w ∧
      cpmmGlobalCurvatureFromSechSq w ≤
        powerFamilyGlobalCurvatureFromSechSq alpha w := by
  constructor
  · rw [powerFamilyGlobalSlippageFromSechSq_zero]
    exact power_family_global_slippage_lt_cpmm halpha (by nlinarith)
  · exact power_family_global_curvature_ge_cpmm (le_of_lt halpha) hwlo hwle

/-- At `alpha = 0`, the power-family curvature expression reduces to the CPMM
curvature expression. -/
lemma powerFamilyGlobalCurvatureFromSechSq_zero (w : ℝ) :
    powerFamilyGlobalCurvatureFromSechSq 0 w = cpmmGlobalCurvatureFromSechSq w := by
  unfold powerFamilyGlobalCurvatureFromSechSq cpmmGlobalCurvatureFromSechSq
    powerFamilyGlobalCurvaturePoly
  rw [Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The polynomial curvature factor has a nonnegative-coefficient certificate
after writing `u = 2*w - 1`. -/
lemma powerFamilyGlobalCurvaturePoly_recentered (alpha w : ℝ) :
    powerFamilyGlobalCurvaturePoly alpha w =
      (alpha ^ 4 * (2 * w - 1) ^ 3 +
        3 * alpha ^ 4 * (2 * w - 1) ^ 2 +
        3 * alpha ^ 4 * (2 * w - 1) +
        alpha ^ 4 +
        16 * alpha ^ 3 * (2 * w - 1) ^ 2 +
        32 * alpha ^ 3 * (2 * w - 1) +
        16 * alpha ^ 3 +
        alpha ^ 2 * (8 * (2 * w - 1) * (20 - (2 * w - 1)) + 40) +
        alpha * (32 * (2 * w - 1) * (8 - (2 * w - 1)) + 32) +
        128 * (2 * w - 1)) / 8 := by
  unfold powerFamilyGlobalCurvaturePoly
  ring

/-- On the original-HODL convexity band, the polynomial curvature factor is
nonnegative. -/
lemma powerFamilyGlobalCurvaturePoly_nonneg {alpha w : ℝ}
    (halpha : 0 ≤ alpha) (hwlo : (1 / 2 : ℝ) ≤ w) (hwle : w ≤ 1) :
    0 ≤ powerFamilyGlobalCurvaturePoly alpha w := by
  let u : ℝ := 2 * w - 1
  have hu0 : 0 ≤ u := by
    dsimp [u]
    nlinarith
  have hu1 : u ≤ 1 := by
    dsimp [u]
    nlinarith
  have h20 : 0 ≤ 20 - u := by nlinarith
  have h8 : 0 ≤ 8 - u := by nlinarith
  rw [powerFamilyGlobalCurvaturePoly_recentered]
  positivity

/-- The denominator of the power-family curvature expression is positive on the
same band. -/
lemma powerFamilyGlobalCurvatureDen_pos {alpha w : ℝ}
    (halpha : 0 ≤ alpha) (hwlo : (1 / 2 : ℝ) ≤ w) (hwle : w ≤ 1) :
    0 < 16 * (alpha + 2) * (alpha * w + 2) ^ 3 *
      (2 * alpha + 2 - alpha * w) := by
  have hw_nonneg : 0 ≤ w := by nlinarith
  have h_alpha_two : 0 < alpha + 2 := by positivity
  have h_alpha_w_two : 0 < alpha * w + 2 := by positivity
  have h_tail : 0 < 2 * alpha + 2 - alpha * w := by
    have hmul_le : alpha * w ≤ alpha * 1 := by
      exact mul_le_mul_of_nonneg_left hwle halpha
    nlinarith
  positivity

/-- CPMM global curvature is nonnegative on the convexity band. -/
lemma cpmmGlobalCurvatureFromSechSq_nonneg {w : ℝ}
    (hwlo : (1 / 2 : ℝ) ≤ w) :
    0 ≤ cpmmGlobalCurvatureFromSechSq w := by
  unfold cpmmGlobalCurvatureFromSechSq
  have hterm : 0 ≤ 2 * w - 1 := by nlinarith
  positivity

/-- Power-family global curvature is nonnegative on the same convexity band. -/
lemma powerFamilyGlobalCurvatureFromSechSq_nonneg {alpha w : ℝ}
    (halpha : 0 ≤ alpha) (hwlo : (1 / 2 : ℝ) ≤ w) (hwle : w ≤ 1) :
    0 ≤ powerFamilyGlobalCurvatureFromSechSq alpha w := by
  unfold powerFamilyGlobalCurvatureFromSechSq
  have hw_nonneg : 0 ≤ w := by nlinarith
  have hpoly : 0 ≤ powerFamilyGlobalCurvaturePoly alpha w :=
    powerFamilyGlobalCurvaturePoly_nonneg halpha hwlo hwle
  have hden_nonneg :
      0 ≤ 16 * (alpha + 2) * (alpha * w + 2) ^ 3 *
        (2 * alpha + 2 - alpha * w) :=
    le_of_lt (powerFamilyGlobalCurvatureDen_pos halpha hwlo hwle)
  have hrpow : 0 ≤ w ^ ((alpha + 1) / (alpha + 2)) :=
    Real.rpow_nonneg hw_nonneg ((alpha + 1) / (alpha + 2))
  have hfactor : 0 ≤ alpha ^ 2 * w + 4 * alpha + 4 := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg hrpow hfactor) hpoly) hden_nonneg

/-!
## Function-level global packaging on the convexity band

The previous theorems are pointwise in `w`.  The following definitions package
the concrete power-family comparison into actual coefficient functions on the
convexity band `1/2 <= w <= 1`, so the result reads as a genuine global
dominance statement rather than a theorem with a free price point.
-/

/-- The original-HODL convexity band used by the checked global power-family
comparison. -/
def PowerFamilyConvexityBand : Type :=
  {w : ℝ // (1 / 2 : ℝ) ≤ w ∧ w ≤ 1}

/-- Power-family global original-HODL slippage coefficient as a function on the
convexity band. -/
def powerFamilyBandSlippage (alpha : ℝ) : PowerFamilyConvexityBand → ℝ :=
  fun w => powerFamilyGlobalSlippageFromSechSq alpha w.1

/-- Power-family global original-HODL curvature coefficient as a function on the
convexity band. -/
def powerFamilyBandCurvature (alpha : ℝ) : PowerFamilyConvexityBand → ℝ :=
  fun w => powerFamilyGlobalCurvatureFromSechSq alpha w.1

/-- The right endpoint `w = 1` lies in the convexity band. -/
def powerFamilyBandOne : PowerFamilyConvexityBand :=
  ⟨1, by constructor <;> norm_num⟩

/-- On the whole convexity band, nonnegative power-family parameter has no
worse global slippage than CPMM. -/
theorem power_family_band_slippage_no_worse_cpmm {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    GloballyNoWorse (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) := by
  intro w
  have hw : 0 ≤ w.1 := by nlinarith [w.2.1]
  simpa [powerFamilyBandSlippage, powerFamilyGlobalSlippageFromSechSq_zero] using
    power_family_global_slippage_le_cpmm halpha hw

/-- Positive power-family parameter is strictly better than CPMM in global
slippage at some point on the convexity band. -/
theorem power_family_band_slippage_strict_somewhere_cpmm {alpha : ℝ}
    (halpha : 0 < alpha) :
    StrictlyBetterSomewhere (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) := by
  refine ⟨powerFamilyBandOne, by
    simpa [powerFamilyBandSlippage, powerFamilyBandOne,
      powerFamilyGlobalSlippageFromSechSq_zero] using
      power_family_global_slippage_lt_cpmm halpha (by norm_num : (0 : ℝ) < 1)⟩

/-- On the whole convexity band, CPMM has no worse global original-HODL
curvature coefficient than a nonnegative power-family parameter. -/
theorem power_family_band_curvature_cpmm_no_worse {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    GloballyNoWorse (powerFamilyBandCurvature 0) (powerFamilyBandCurvature alpha) := by
  intro w
  simpa [powerFamilyBandCurvature, powerFamilyGlobalCurvatureFromSechSq_zero] using
    power_family_global_curvature_ge_cpmm halpha w.2.1 w.2.2

/-- At the endpoint `w = 1`, the power-family global original-HODL curvature
coefficient simplifies to a linear expression in `alpha`. -/
lemma powerFamilyGlobalCurvatureFromSechSq_one {alpha : ℝ}
    (halpha : 0 ≤ alpha) :
    powerFamilyGlobalCurvatureFromSechSq alpha 1 = (alpha + 2) / 16 := by
  have hden : alpha + 2 ≠ 0 := by positivity
  have hpow : Real.rpow 1 ((alpha + 1) / (alpha + 2)) = 1 := by
    simp
  have hfactor :
      alpha ^ 2 * 1 + 4 * alpha + 4 = (alpha + 2) ^ 2 := by
    ring
  have hpoly :
      powerFamilyGlobalCurvaturePoly alpha 1 = (alpha + 2) ^ 4 := by
    unfold powerFamilyGlobalCurvaturePoly
    ring
  have hdenom :
      16 * (alpha + 2) * (alpha * 1 + 2) ^ 3 * (2 * alpha + 2 - alpha * 1) =
        16 * (alpha + 2) ^ 5 := by
    ring
  unfold powerFamilyGlobalCurvatureFromSechSq
  rw [hpow]
  rw [hfactor, hpoly, hdenom]
  field_simp [hden]

/-- Positive power-family parameter has strictly worse global original-HODL
curvature than CPMM somewhere on the convexity band. -/
theorem power_family_band_curvature_cpmm_strictly_better_somewhere {alpha : ℝ}
    (halpha : 0 < alpha) :
    StrictlyBetterSomewhere (powerFamilyBandCurvature 0) (powerFamilyBandCurvature alpha) := by
  refine ⟨powerFamilyBandOne, by
    change powerFamilyGlobalCurvatureFromSechSq 0 1 <
      powerFamilyGlobalCurvatureFromSechSq alpha 1
    rw [powerFamilyGlobalCurvatureFromSechSq_one (show (0 : ℝ) ≤ 0 by positivity)]
    rw [powerFamilyGlobalCurvatureFromSechSq_one (le_of_lt halpha)]
    nlinarith⟩

/-- Function-level global no-free-lunch theorem for the power family against
CPMM on the original-HODL convexity band.  Positive `alpha` gives globally no
worse slippage and a strict slippage gain somewhere, but CPMM remains globally
no worse in the original-HODL curvature coefficient and is strictly better
somewhere. -/
theorem power_family_band_no_free_lunch_vs_cpmm {alpha : ℝ}
    (halpha : 0 < alpha) :
    GloballyNoWorse (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) ∧
      StrictlyBetterSomewhere (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) ∧
      GloballyNoWorse (powerFamilyBandCurvature 0) (powerFamilyBandCurvature alpha) ∧
      StrictlyBetterSomewhere (powerFamilyBandCurvature 0) (powerFamilyBandCurvature alpha) := by
  refine ⟨power_family_band_slippage_no_worse_cpmm (le_of_lt halpha),
    power_family_band_slippage_strict_somewhere_cpmm halpha,
    power_family_band_curvature_cpmm_no_worse (le_of_lt halpha),
    power_family_band_curvature_cpmm_strictly_better_somewhere halpha⟩

/-- Equivalent obstruction form: on the convexity band, a positive power-family
parameter cannot simultaneously be globally no worse in slippage, strictly
better in slippage somewhere, and globally no worse in original-HODL
curvature relative to CPMM. -/
theorem power_family_band_not_simultaneous_global_no_worse_vs_cpmm {alpha : ℝ}
    (halpha : 0 < alpha) :
    ¬ (GloballyNoWorse (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) ∧
        StrictlyBetterSomewhere (powerFamilyBandSlippage alpha) (powerFamilyBandSlippage 0) ∧
        GloballyNoWorse (powerFamilyBandCurvature alpha) (powerFamilyBandCurvature 0)) := by
  intro h
  rcases power_family_band_curvature_cpmm_strictly_better_somewhere halpha with ⟨w, hw⟩
  exact not_lt_of_ge (h.2.2 w) hw

end

end LocalJetFrontier
end Impossibility
end TauSwap
