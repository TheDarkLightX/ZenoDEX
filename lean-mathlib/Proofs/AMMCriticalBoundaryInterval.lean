import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Critical-boundary interval theorem

This file promotes the isolated critical-boundary packet into the main Lean
proof tree.  The exact Julia receipt discovered that after setting
`a = w^(1/8)`, the critical boundary expression factors as `(a - 1)^2` times a
polynomial quotient.  Lean proves both the local quartic limit and an explicit
rational interval where the factorized critical model is strictly negative.

The intended payoff is the same theorem as v1:

```text
criticalFromD d / d^4 -> -179/1536
```

The interval proof uses a Horner interval certificate so the checker does not
need to normalize a degree-42 polynomial in one large step.
-/

namespace TauSwap
namespace Impossibility
namespace CriticalBoundaryInterval

open Filter Topology

noncomputable section

def sechSq (d : ℝ) : ℝ :=
  (Real.cosh d ^ 2)⁻¹

def criticalAFromD (d : ℝ) : ℝ :=
  Real.rpow (sechSq d) (1 / 8 : ℝ)

def cpmmGlobalCurvatureFromSechSq (w : ℝ) : ℝ :=
  Real.sqrt w * (2 * w - 1) / 8

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

def powerFamilyGlobalCurvatureFromSechSq (alpha w : ℝ) : ℝ :=
  Real.rpow w ((alpha + 1) / (alpha + 2)) *
    (alpha ^ 2 * w + 4 * alpha + 4) *
    powerFamilyGlobalCurvaturePoly alpha w /
    (16 * (alpha + 2) * (alpha * w + 2) ^ 3 *
      (2 * alpha + 2 - alpha * w))

def normalizedCurvatureFromW (alpha w : ℝ) : ℝ :=
  powerFamilyGlobalCurvatureFromSechSq alpha w -
    cpmmGlobalCurvatureFromSechSq w -
    alpha / 16

def criticalFromD (d : ℝ) : ℝ :=
  normalizedCurvatureFromW (2 / 3 : ℝ) (sechSq d)

/-- The polynomial quotient in the exact factorization. -/
def criticalFactorPoly (a : ℝ) : ℝ :=
  24 * a ^ 42 + 48 * a ^ 41 + 72 * a ^ 40 + 96 * a ^ 39 +
    120 * a ^ 38 + 144 * a ^ 37 + 168 * a ^ 36 + 193 * a ^ 35 +
    302 * a ^ 34 + 411 * a ^ 33 + 520 * a ^ 32 + 629 * a ^ 31 +
    742 * a ^ 30 + 855 * a ^ 29 + 968 * a ^ 28 + 1045 * a ^ 27 +
    642 * a ^ 26 + 239 * a ^ 25 - 164 * a ^ 24 - 567 * a ^ 23 -
    954 * a ^ 22 - 1341 * a ^ 21 - 1728 * a ^ 20 - 2349 * a ^ 19 -
    5346 * a ^ 18 - 8343 * a ^ 17 - 11340 * a ^ 16 -
    14337 * a ^ 15 - 17406 * a ^ 14 - 20475 * a ^ 13 -
    23544 * a ^ 12 - 18873 * a ^ 11 - 16146 * a ^ 10 -
    13419 * a ^ 9 - 10692 * a ^ 8 - 7965 * a ^ 7 -
    5670 * a ^ 6 - 3375 * a ^ 5 - 1080 * a ^ 4 -
    2160 * a ^ 3 - 1620 * a ^ 2 - 1080 * a - 540

/-- The exact factorized expression in the `a = w^(1/8)` coordinate. -/
def criticalFactorModel (a : ℝ) : ℝ :=
  -((a - 1) ^ 2 * criticalFactorPoly a) /
    (96 * (a ^ 8 - 5) * (a ^ 8 + 3) ^ 3)

/-- The geometric quotient `(a^8 - 1)/(a - 1)` in expanded form. -/
def eighthShiftQuotient (a : ℝ) : ℝ :=
  a ^ 7 + a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1

/-- The pole-free local model after cancelling `(a - 1)^2` from the normalized
factor expression away from `a = 1`. -/
def criticalFactorLimitModel (a : ℝ) : ℝ :=
  -criticalFactorPoly a /
    (96 * eighthShiftQuotient a ^ 2 * (a ^ 8 - 5) * (a ^ 8 + 3) ^ 3)

/-- Positive eighth-power collapse for the fractional exponent in the critical
factorization route. -/
theorem rpow_eight_five_eighths {a : ℝ} (ha : 0 < a) :
    Real.rpow (a ^ 8) (5 / 8 : ℝ) = a ^ 5 := by
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  calc
    Real.rpow (a ^ 8) (5 / 8 : ℝ)
        = Real.rpow a ((8 : ℝ) * (5 / 8 : ℝ)) := by
            simpa using
              (Real.rpow_natCast_mul (x := a) ha_nonneg 8 (5 / 8 : ℝ)).symm
    _ = Real.rpow a (5 : ℝ) := by norm_num
    _ = a ^ 5 := by
        simp

/-- Positive eighth-power collapse for the square-root term in the critical
factorization route. -/
theorem sqrt_eight {a : ℝ} (ha : 0 < a) :
    Real.sqrt (a ^ 8) = a ^ 4 := by
  have ha4_nonneg : 0 ≤ a ^ 4 := by positivity
  have hpow : a ^ 8 = (a ^ 4) ^ 2 := by ring
  rw [hpow]
  exact Real.sqrt_sq ha4_nonneg

/-- Algebraic factorization target.  For positive `a` away from the pole
`a^8 = 5`, the fractional powers in `normalizedCurvatureFromW (2/3) (a^8)`
collapse to `a^5` and `a^4`, exposing the square factor.

The side condition is necessary because Lean's real division is total:
at the pole, both rational presentations no longer denote the same value. -/
theorem critical_factorization
    {a : ℝ} (ha : 0 < a) (hden : a ^ 8 ≠ 5) :
    normalizedCurvatureFromW (2 / 3 : ℝ) (a ^ 8) =
      criticalFactorModel a := by
  have hpow : Real.rpow (a ^ 8) (((2 / 3 : ℝ) + 1) / ((2 / 3 : ℝ) + 2)) = a ^ 5 := by
    norm_num
    exact rpow_eight_five_eighths ha
  have hsqrt : Real.sqrt (a ^ 8) = a ^ 4 := sqrt_eight ha
  have hden_sub : a ^ 8 - 5 ≠ 0 := sub_ne_zero.mpr hden
  have hden_sub_rev : 5 - a ^ 8 ≠ 0 := sub_ne_zero.mpr hden.symm
  have hden_five : 2 + 3 - a ^ 8 ≠ 0 := by
    norm_num
    exact hden_sub_rev
  have hden_add : a ^ 8 + 3 ≠ 0 := by positivity
  have hden_linear : 2 * (2 / 3 : ℝ) + 2 - (2 / 3 : ℝ) * a ^ 8 ≠ 0 := by
    intro hzero
    apply hden
    nlinarith
  have hden_mid : (2 / 3 : ℝ) * a ^ 8 + 2 ≠ 0 := by positivity
  unfold normalizedCurvatureFromW powerFamilyGlobalCurvatureFromSechSq
    cpmmGlobalCurvatureFromSechSq criticalFactorModel powerFamilyGlobalCurvaturePoly
    criticalFactorPoly
  rw [hpow, hsqrt]
  field_simp [hden_sub, hden_sub_rev, hden_five, hden_add, hden_linear, hden_mid]
  ring_nf

private lemma pow_eight_sub_one_factor (a : ℝ) :
    a ^ 8 - 1 = (a - 1) * eighthShiftQuotient a := by
  unfold eighthShiftQuotient
  ring

private lemma criticalFactorLimitModel_one :
    criticalFactorLimitModel 1 = (-(179 : ℝ) / 1536) := by
  norm_num [criticalFactorLimitModel, criticalFactorPoly, eighthShiftQuotient]

private lemma continuousAt_eighthShiftQuotient_one :
    ContinuousAt eighthShiftQuotient 1 := by
  unfold eighthShiftQuotient
  fun_prop

private lemma continuousAt_criticalFactorLimitModel_one :
    ContinuousAt criticalFactorLimitModel 1 := by
  unfold criticalFactorLimitModel
  apply ContinuousAt.div
  · unfold criticalFactorPoly
    fun_prop
  · unfold eighthShiftQuotient
    fun_prop
  · norm_num [eighthShiftQuotient]

private lemma criticalFactorModel_div_w_shift_sq_eventually_eq :
    (fun a : ℝ => criticalFactorModel a / (a ^ 8 - 1) ^ 2)
      =ᶠ[𝓝[≠] (1 : ℝ)]
        criticalFactorLimitModel := by
  have hev_pow_ne :
      ∀ᶠ a : ℝ in 𝓝[≠] (1 : ℝ), a ^ 8 ≠ 5 := by
    have hcont : ContinuousAt (fun a : ℝ => a ^ 8) 1 := by fun_prop
    have hne : (fun a : ℝ => a ^ 8) 1 ≠ 5 := by norm_num
    exact Filter.Eventually.filter_mono inf_le_left (hcont.eventually_ne hne)
  have hev_sum_ne :
      ∀ᶠ a : ℝ in 𝓝[≠] (1 : ℝ), eighthShiftQuotient a ≠ 0 := by
    have hne : eighthShiftQuotient 1 ≠ 0 := by
      norm_num [eighthShiftQuotient]
    exact Filter.Eventually.filter_mono inf_le_left
      (continuousAt_eighthShiftQuotient_one.eventually_ne hne)
  filter_upwards [self_mem_nhdsWithin, hev_pow_ne, hev_sum_ne] with a ha hpow_ne hsum_ne
  have ha_sub : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hpow_sub : a ^ 8 - 5 ≠ 0 := sub_ne_zero.mpr hpow_ne
  have hpow_add : a ^ 8 + 3 ≠ 0 := by positivity
  have hfactor : (a ^ 8 - 1) ^ 2 =
      (a - 1) ^ 2 * eighthShiftQuotient a ^ 2 := by
    rw [pow_eight_sub_one_factor]
    ring
  unfold criticalFactorModel criticalFactorLimitModel
  rw [hfactor]
  field_simp [ha_sub, hsum_ne, hpow_sub, hpow_add]

/-- The factorized model has the expected normalized limit after dividing by
`(a^8 - 1)^2`, which is exactly the `z = w - 1` coefficient. -/
theorem critical_factor_model_div_w_shift_sq_tendsto :
    Tendsto
      (fun a : ℝ => criticalFactorModel a / (a ^ 8 - 1) ^ 2)
      (𝓝[≠] (1 : ℝ))
      (𝓝 (-(179 : ℝ) / 1536)) := by
  have hlim :
      Tendsto criticalFactorLimitModel
        (𝓝[≠] (1 : ℝ))
        (𝓝 (criticalFactorLimitModel 1)) :=
    continuousAt_criticalFactorLimitModel_one.tendsto.mono_left inf_le_left
  have htarget :
      Tendsto criticalFactorLimitModel
        (𝓝[≠] (1 : ℝ))
        (𝓝 (-(179 : ℝ) / 1536)) := by
    simpa [criticalFactorLimitModel_one] using hlim
  exact htarget.congr' criticalFactorModel_div_w_shift_sq_eventually_eq.symm

private theorem sinh_div_tendsto :
    Tendsto (fun d => Real.sinh d / d) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  simpa [div_eq_inv_mul] using
    (Real.hasDerivAt_sinh 0).tendsto_slope_zero

private lemma sechSq_pos (d : ℝ) : 0 < sechSq d := by
  unfold sechSq
  positivity

private lemma criticalAFromD_pos (d : ℝ) : 0 < criticalAFromD d := by
  unfold criticalAFromD
  exact Real.rpow_pos_of_pos (sechSq_pos d) _

private lemma criticalAFromD_pow_eight (d : ℝ) :
    criticalAFromD d ^ 8 = sechSq d := by
  have hnonneg : 0 ≤ sechSq d := le_of_lt (sechSq_pos d)
  unfold criticalAFromD
  calc
    (Real.rpow (sechSq d) (1 / 8 : ℝ)) ^ 8
        = Real.rpow (Real.rpow (sechSq d) (1 / 8 : ℝ)) (8 : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow (sechSq d) (1 / 8 : ℝ)) 8).symm
    _ = Real.rpow (sechSq d) ((1 / 8 : ℝ) * 8) := by
            exact (Real.rpow_mul hnonneg (1 / 8 : ℝ) 8).symm
    _ = sechSq d := by norm_num

/-- Away from the center, the coordinate change `w = sech(d)^2` is never equal
to `1`. -/
private lemma sechSq_ne_one {d : ℝ} (hd : d ≠ 0) : sechSq d ≠ 1 := by
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

/-- The coordinate change `w = sech(d)^2` satisfies `w - 1 = -d^2 + o(d^2)` at
the center. -/
private theorem sechSq_sub_one_div_sq_tendsto :
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

private lemma criticalAFromD_tendsto_punctured :
    Tendsto criticalAFromD (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
  have hsech : Tendsto sechSq (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt sechSq 0 := by
      unfold sechSq
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    simpa [sechSq] using hcont.tendsto.mono_left inf_le_left
  have hroot_cont : ContinuousAt (fun x : ℝ => Real.rpow x (1 / 8 : ℝ)) 1 := by
    exact Real.continuousAt_rpow_const 1 (1 / 8 : ℝ) (Or.inl one_ne_zero)
  have hnhds : Tendsto criticalAFromD (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    unfold criticalAFromD
    simpa using hroot_cont.tendsto.comp hsech
  have hne : Tendsto criticalAFromD (𝓝[≠] (0 : ℝ)) (𝓟 ({1}ᶜ)) := by
    apply tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with d hd
    intro hroot
    apply sechSq_ne_one hd
    rw [← criticalAFromD_pow_eight d, hroot]
    norm_num
  rw [show 𝓝[≠] (1 : ℝ) = 𝓝 (1 : ℝ) ⊓ 𝓟 ({1}ᶜ) by rfl]
  exact tendsto_inf.2 ⟨hnhds, hne⟩

/-- Final d-coordinate theorem.  This statement intentionally matches the v1
target but the proof can use `critical_factorization` plus continuity of
`a(d) = sqrt(sqrt(sqrt(sechSq d)))`, or any equivalent positive eighth-root
route. -/
theorem criticalFromD_div_four_tendsto :
    Tendsto
      (fun d : ℝ => criticalFromD d / d ^ 4)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-(179 : ℝ) / 1536)) := by
  have hfirst :
      Tendsto
        (fun d : ℝ =>
          criticalFactorModel (criticalAFromD d) /
            (criticalAFromD d ^ 8 - 1) ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-(179 : ℝ) / 1536)) :=
    critical_factor_model_div_w_shift_sq_tendsto.comp
      criticalAFromD_tendsto_punctured
  have hshift :
      Tendsto
        (fun d : ℝ => (criticalAFromD d ^ 8 - 1) / d ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-1 : ℝ)) := by
    simpa [criticalAFromD_pow_eight] using sechSq_sub_one_div_sq_tendsto
  have hshift_sq :
      Tendsto
        (fun d : ℝ => ((criticalAFromD d ^ 8 - 1) / d ^ 2) ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (1 : ℝ)) := by
    simpa [pow_two] using hshift.mul hshift
  have hprod :
      Tendsto
        (fun d : ℝ =>
          (criticalFactorModel (criticalAFromD d) /
            (criticalAFromD d ^ 8 - 1) ^ 2) *
            (((criticalAFromD d ^ 8 - 1) / d ^ 2) ^ 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-(179 : ℝ) / 1536)) := by
    simpa using hfirst.mul hshift_sq
  have hev_sech_ne_five :
      ∀ᶠ d : ℝ in 𝓝[≠] (0 : ℝ), sechSq d ≠ 5 := by
    have hcont : ContinuousAt sechSq 0 := by
      unfold sechSq
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    have hne : sechSq 0 ≠ 5 := by
      norm_num [sechSq]
    exact Filter.Eventually.filter_mono inf_le_left (hcont.eventually_ne hne)
  have heq :
      (fun d : ℝ => criticalFromD d / d ^ 4)
        =ᶠ[𝓝[≠] (0 : ℝ)]
          (fun d : ℝ =>
            (criticalFactorModel (criticalAFromD d) /
              (criticalAFromD d ^ 8 - 1) ^ 2) *
      (((criticalAFromD d ^ 8 - 1) / d ^ 2) ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hev_sech_ne_five] with d hd hsech_ne_five
    have ha_pow : criticalAFromD d ^ 8 = sechSq d := criticalAFromD_pow_eight d
    have hden_a : criticalAFromD d ^ 8 ≠ 5 := by
      rw [ha_pow]
      exact hsech_ne_five
    have hcrit : criticalFromD d = criticalFactorModel (criticalAFromD d) := by
      unfold criticalFromD
      rw [← ha_pow]
      exact critical_factorization (criticalAFromD_pos d) hden_a
    have hshift_ne : criticalAFromD d ^ 8 - 1 ≠ 0 := by
      rw [ha_pow]
      exact sub_ne_zero.mpr (sechSq_ne_one hd)
    have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
    rw [hcrit]
    field_simp [hd, hd2, hshift_ne]
  exact hprod.congr' heq.symm

/-- The quartic coefficient theorem has the expected sign consequence: at the
critical boundary, the normalized original-HODL curvature delta is negative in
a punctured neighborhood of the center. -/
theorem criticalFromD_eventually_negative :
    ∀ᶠ d : ℝ in 𝓝[≠] (0 : ℝ), criticalFromD d < 0 := by
  have hcoeff : (-(179 : ℝ) / 1536) < 0 := by norm_num
  have hratio :
      ∀ᶠ d : ℝ in 𝓝[≠] (0 : ℝ), criticalFromD d / d ^ 4 < 0 :=
    criticalFromD_div_four_tendsto.eventually (eventually_lt_nhds hcoeff)
  filter_upwards [hratio, self_mem_nhdsWithin] with d hratio hd
  have hd2_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hd4 : 0 < d ^ 4 := by
    rw [show d ^ 4 = (d ^ 2) ^ 2 by ring]
    exact sq_pos_of_ne_zero hd2_ne
  have hmul : criticalFromD d / d ^ 4 * d ^ 4 < 0 * d ^ 4 :=
    mul_lt_mul_of_pos_right hratio hd4
  simpa [ne_of_gt hd4] using hmul

/-- Horner stages for interval-certified evaluation of `criticalFactorPoly`.
They keep the interval proof local and avoid large degree-42 polynomial
normalization during the sign proof. -/
private def criticalFactorHorner0 (_a : ℝ) : ℝ := (24 : ℝ)
private def criticalFactorHorner1 (a : ℝ) : ℝ := (48 : ℝ) + criticalFactorHorner0 a * a
private def criticalFactorHorner2 (a : ℝ) : ℝ := (72 : ℝ) + criticalFactorHorner1 a * a
private def criticalFactorHorner3 (a : ℝ) : ℝ := (96 : ℝ) + criticalFactorHorner2 a * a
private def criticalFactorHorner4 (a : ℝ) : ℝ := (120 : ℝ) + criticalFactorHorner3 a * a
private def criticalFactorHorner5 (a : ℝ) : ℝ := (144 : ℝ) + criticalFactorHorner4 a * a
private def criticalFactorHorner6 (a : ℝ) : ℝ := (168 : ℝ) + criticalFactorHorner5 a * a
private def criticalFactorHorner7 (a : ℝ) : ℝ := (193 : ℝ) + criticalFactorHorner6 a * a
private def criticalFactorHorner8 (a : ℝ) : ℝ := (302 : ℝ) + criticalFactorHorner7 a * a
private def criticalFactorHorner9 (a : ℝ) : ℝ := (411 : ℝ) + criticalFactorHorner8 a * a
private def criticalFactorHorner10 (a : ℝ) : ℝ := (520 : ℝ) + criticalFactorHorner9 a * a
private def criticalFactorHorner11 (a : ℝ) : ℝ := (629 : ℝ) + criticalFactorHorner10 a * a
private def criticalFactorHorner12 (a : ℝ) : ℝ := (742 : ℝ) + criticalFactorHorner11 a * a
private def criticalFactorHorner13 (a : ℝ) : ℝ := (855 : ℝ) + criticalFactorHorner12 a * a
private def criticalFactorHorner14 (a : ℝ) : ℝ := (968 : ℝ) + criticalFactorHorner13 a * a
private def criticalFactorHorner15 (a : ℝ) : ℝ := (1045 : ℝ) + criticalFactorHorner14 a * a
private def criticalFactorHorner16 (a : ℝ) : ℝ := (642 : ℝ) + criticalFactorHorner15 a * a
private def criticalFactorHorner17 (a : ℝ) : ℝ := (239 : ℝ) + criticalFactorHorner16 a * a
private def criticalFactorHorner18 (a : ℝ) : ℝ := (-164 : ℝ) + criticalFactorHorner17 a * a
private def criticalFactorHorner19 (a : ℝ) : ℝ := (-567 : ℝ) + criticalFactorHorner18 a * a
private def criticalFactorHorner20 (a : ℝ) : ℝ := (-954 : ℝ) + criticalFactorHorner19 a * a
private def criticalFactorHorner21 (a : ℝ) : ℝ := (-1341 : ℝ) + criticalFactorHorner20 a * a
private def criticalFactorHorner22 (a : ℝ) : ℝ := (-1728 : ℝ) + criticalFactorHorner21 a * a
private def criticalFactorHorner23 (a : ℝ) : ℝ := (-2349 : ℝ) + criticalFactorHorner22 a * a
private def criticalFactorHorner24 (a : ℝ) : ℝ := (-5346 : ℝ) + criticalFactorHorner23 a * a
private def criticalFactorHorner25 (a : ℝ) : ℝ := (-8343 : ℝ) + criticalFactorHorner24 a * a
private def criticalFactorHorner26 (a : ℝ) : ℝ := (-11340 : ℝ) + criticalFactorHorner25 a * a
private def criticalFactorHorner27 (a : ℝ) : ℝ := (-14337 : ℝ) + criticalFactorHorner26 a * a
private def criticalFactorHorner28 (a : ℝ) : ℝ := (-17406 : ℝ) + criticalFactorHorner27 a * a
private def criticalFactorHorner29 (a : ℝ) : ℝ := (-20475 : ℝ) + criticalFactorHorner28 a * a
private def criticalFactorHorner30 (a : ℝ) : ℝ := (-23544 : ℝ) + criticalFactorHorner29 a * a
private def criticalFactorHorner31 (a : ℝ) : ℝ := (-18873 : ℝ) + criticalFactorHorner30 a * a
private def criticalFactorHorner32 (a : ℝ) : ℝ := (-16146 : ℝ) + criticalFactorHorner31 a * a
private def criticalFactorHorner33 (a : ℝ) : ℝ := (-13419 : ℝ) + criticalFactorHorner32 a * a
private def criticalFactorHorner34 (a : ℝ) : ℝ := (-10692 : ℝ) + criticalFactorHorner33 a * a
private def criticalFactorHorner35 (a : ℝ) : ℝ := (-7965 : ℝ) + criticalFactorHorner34 a * a
private def criticalFactorHorner36 (a : ℝ) : ℝ := (-5670 : ℝ) + criticalFactorHorner35 a * a
private def criticalFactorHorner37 (a : ℝ) : ℝ := (-3375 : ℝ) + criticalFactorHorner36 a * a
private def criticalFactorHorner38 (a : ℝ) : ℝ := (-1080 : ℝ) + criticalFactorHorner37 a * a
private def criticalFactorHorner39 (a : ℝ) : ℝ := (-2160 : ℝ) + criticalFactorHorner38 a * a
private def criticalFactorHorner40 (a : ℝ) : ℝ := (-1620 : ℝ) + criticalFactorHorner39 a * a
private def criticalFactorHorner41 (a : ℝ) : ℝ := (-1080 : ℝ) + criticalFactorHorner40 a * a
private def criticalFactorHorner42 (a : ℝ) : ℝ := (-540 : ℝ) + criticalFactorHorner41 a * a

private theorem criticalFactorPoly_horner (a : ℝ) :
    criticalFactorPoly a = criticalFactorHorner42 a := by
  unfold criticalFactorHorner42 criticalFactorHorner41 criticalFactorHorner40 criticalFactorHorner39 criticalFactorHorner38 criticalFactorHorner37 criticalFactorHorner36 criticalFactorHorner35 criticalFactorHorner34 criticalFactorHorner33 criticalFactorHorner32 criticalFactorHorner31 criticalFactorHorner30 criticalFactorHorner29 criticalFactorHorner28 criticalFactorHorner27 criticalFactorHorner26 criticalFactorHorner25 criticalFactorHorner24 criticalFactorHorner23 criticalFactorHorner22 criticalFactorHorner21 criticalFactorHorner20 criticalFactorHorner19 criticalFactorHorner18 criticalFactorHorner17 criticalFactorHorner16 criticalFactorHorner15 criticalFactorHorner14 criticalFactorHorner13 criticalFactorHorner12 criticalFactorHorner11 criticalFactorHorner10 criticalFactorHorner9 criticalFactorHorner8 criticalFactorHorner7 criticalFactorHorner6 criticalFactorHorner5 criticalFactorHorner4 criticalFactorHorner3 criticalFactorHorner2 criticalFactorHorner1 criticalFactorHorner0 criticalFactorPoly
  ring_nf

/-- Julia-discovered finite-interval strengthening.  This is the exact
polynomial sign obligation extracted from the candidate interval
`4/5 <= a <= 23/20`.  A proof may use a Bernstein certificate on this interval
or split at `a = 1` and use rational Taylor bounds on the two sides. -/
theorem criticalFactorPoly_neg_candidate_interval
    {a : ℝ} (ha_lo : (4 / 5 : ℝ) ≤ a) (ha_hi : a ≤ (23 / 20 : ℝ)) :
    criticalFactorPoly a < 0 := by
  have ha_nonneg : 0 ≤ a := le_trans (by norm_num : (0 : ℝ) ≤ 4 / 5) ha_lo
  have ha_lo_nonneg : 0 ≤ (4 / 5 : ℝ) := by norm_num
  have hL0 : (24 : ℝ) ≤ criticalFactorHorner0 a := by norm_num [criticalFactorHorner0]
  have hU0 : criticalFactorHorner0 a ≤ (24 : ℝ) := by norm_num [criticalFactorHorner0]
  have hL1 : (336 / 5 : ℝ) ≤ criticalFactorHorner1 a := by
    unfold criticalFactorHorner1
    have hmul_left : (24 : ℝ) * (4 / 5 : ℝ) ≤ (24 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (24 : ℝ))
    have hmul_right : (24 : ℝ) * a ≤ criticalFactorHorner0 a * a := by
      exact mul_le_mul_of_nonneg_right hL0 ha_nonneg
    have hmul : (24 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner0 a * a := le_trans hmul_left hmul_right
    calc
      (336 / 5 : ℝ) = (48 : ℝ) + (24 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (48 : ℝ) + criticalFactorHorner0 a * a := add_le_add_right hmul (48 : ℝ)
  have hU1 : criticalFactorHorner1 a ≤ (378 / 5 : ℝ) := by
    unfold criticalFactorHorner1
    have hmul_left : criticalFactorHorner0 a * a ≤ (24 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU0 ha_nonneg
    have hmul_right : (24 : ℝ) * a ≤ (24 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (24 : ℝ))
    have hmul : criticalFactorHorner0 a * a ≤ (24 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (48 : ℝ) + criticalFactorHorner0 a * a ≤ (48 : ℝ) + (24 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (48 : ℝ)
      _ = (378 / 5 : ℝ) := by norm_num
  have hL2 : (3144 / 25 : ℝ) ≤ criticalFactorHorner2 a := by
    unfold criticalFactorHorner2
    have hmul_left : (336 / 5 : ℝ) * (4 / 5 : ℝ) ≤ (336 / 5 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (336 / 5 : ℝ))
    have hmul_right : (336 / 5 : ℝ) * a ≤ criticalFactorHorner1 a * a := by
      exact mul_le_mul_of_nonneg_right hL1 ha_nonneg
    have hmul : (336 / 5 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner1 a * a := le_trans hmul_left hmul_right
    calc
      (3144 / 25 : ℝ) = (72 : ℝ) + (336 / 5 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (72 : ℝ) + criticalFactorHorner1 a * a := add_le_add_right hmul (72 : ℝ)
  have hU2 : criticalFactorHorner2 a ≤ (7947 / 50 : ℝ) := by
    unfold criticalFactorHorner2
    have hmul_left : criticalFactorHorner1 a * a ≤ (378 / 5 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU1 ha_nonneg
    have hmul_right : (378 / 5 : ℝ) * a ≤ (378 / 5 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (378 / 5 : ℝ))
    have hmul : criticalFactorHorner1 a * a ≤ (378 / 5 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (72 : ℝ) + criticalFactorHorner1 a * a ≤ (72 : ℝ) + (378 / 5 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (72 : ℝ)
      _ = (7947 / 50 : ℝ) := by norm_num
  have hL3 : (24576 / 125 : ℝ) ≤ criticalFactorHorner3 a := by
    unfold criticalFactorHorner3
    have hmul_left : (3144 / 25 : ℝ) * (4 / 5 : ℝ) ≤ (3144 / 25 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (3144 / 25 : ℝ))
    have hmul_right : (3144 / 25 : ℝ) * a ≤ criticalFactorHorner2 a * a := by
      exact mul_le_mul_of_nonneg_right hL2 ha_nonneg
    have hmul : (3144 / 25 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner2 a * a := le_trans hmul_left hmul_right
    calc
      (24576 / 125 : ℝ) = (96 : ℝ) + (3144 / 25 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (96 : ℝ) + criticalFactorHorner2 a * a := add_le_add_right hmul (96 : ℝ)
  have hU3 : criticalFactorHorner3 a ≤ (278781 / 1000 : ℝ) := by
    unfold criticalFactorHorner3
    have hmul_left : criticalFactorHorner2 a * a ≤ (7947 / 50 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU2 ha_nonneg
    have hmul_right : (7947 / 50 : ℝ) * a ≤ (7947 / 50 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (7947 / 50 : ℝ))
    have hmul : criticalFactorHorner2 a * a ≤ (7947 / 50 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (96 : ℝ) + criticalFactorHorner2 a * a ≤ (96 : ℝ) + (7947 / 50 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (96 : ℝ)
      _ = (278781 / 1000 : ℝ) := by norm_num
  have hL4 : (173304 / 625 : ℝ) ≤ criticalFactorHorner4 a := by
    unfold criticalFactorHorner4
    have hmul_left : (24576 / 125 : ℝ) * (4 / 5 : ℝ) ≤ (24576 / 125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (24576 / 125 : ℝ))
    have hmul_right : (24576 / 125 : ℝ) * a ≤ criticalFactorHorner3 a * a := by
      exact mul_le_mul_of_nonneg_right hL3 ha_nonneg
    have hmul : (24576 / 125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner3 a * a := le_trans hmul_left hmul_right
    calc
      (173304 / 625 : ℝ) = (120 : ℝ) + (24576 / 125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (120 : ℝ) + criticalFactorHorner3 a * a := add_le_add_right hmul (120 : ℝ)
  have hU4 : criticalFactorHorner4 a ≤ (8811963 / 20000 : ℝ) := by
    unfold criticalFactorHorner4
    have hmul_left : criticalFactorHorner3 a * a ≤ (278781 / 1000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU3 ha_nonneg
    have hmul_right : (278781 / 1000 : ℝ) * a ≤ (278781 / 1000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (278781 / 1000 : ℝ))
    have hmul : criticalFactorHorner3 a * a ≤ (278781 / 1000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (120 : ℝ) + criticalFactorHorner3 a * a ≤ (120 : ℝ) + (278781 / 1000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (120 : ℝ)
      _ = (8811963 / 20000 : ℝ) := by norm_num
  have hL5 : (1143216 / 3125 : ℝ) ≤ criticalFactorHorner5 a := by
    unfold criticalFactorHorner5
    have hmul_left : (173304 / 625 : ℝ) * (4 / 5 : ℝ) ≤ (173304 / 625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (173304 / 625 : ℝ))
    have hmul_right : (173304 / 625 : ℝ) * a ≤ criticalFactorHorner4 a * a := by
      exact mul_le_mul_of_nonneg_right hL4 ha_nonneg
    have hmul : (173304 / 625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner4 a * a := le_trans hmul_left hmul_right
    calc
      (1143216 / 3125 : ℝ) = (144 : ℝ) + (173304 / 625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (144 : ℝ) + criticalFactorHorner4 a * a := add_le_add_right hmul (144 : ℝ)
  have hU5 : criticalFactorHorner5 a ≤ (260275149 / 400000 : ℝ) := by
    unfold criticalFactorHorner5
    have hmul_left : criticalFactorHorner4 a * a ≤ (8811963 / 20000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU4 ha_nonneg
    have hmul_right : (8811963 / 20000 : ℝ) * a ≤ (8811963 / 20000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (8811963 / 20000 : ℝ))
    have hmul : criticalFactorHorner4 a * a ≤ (8811963 / 20000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (144 : ℝ) + criticalFactorHorner4 a * a ≤ (144 : ℝ) + (8811963 / 20000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (144 : ℝ)
      _ = (260275149 / 400000 : ℝ) := by norm_num
  have hL6 : (7197864 / 15625 : ℝ) ≤ criticalFactorHorner6 a := by
    unfold criticalFactorHorner6
    have hmul_left : (1143216 / 3125 : ℝ) * (4 / 5 : ℝ) ≤ (1143216 / 3125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (1143216 / 3125 : ℝ))
    have hmul_right : (1143216 / 3125 : ℝ) * a ≤ criticalFactorHorner5 a * a := by
      exact mul_le_mul_of_nonneg_right hL5 ha_nonneg
    have hmul : (1143216 / 3125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner5 a * a := le_trans hmul_left hmul_right
    calc
      (7197864 / 15625 : ℝ) = (168 : ℝ) + (1143216 / 3125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (168 : ℝ) + criticalFactorHorner5 a * a := add_le_add_right hmul (168 : ℝ)
  have hU6 : criticalFactorHorner6 a ≤ (7330328427 / 8000000 : ℝ) := by
    unfold criticalFactorHorner6
    have hmul_left : criticalFactorHorner5 a * a ≤ (260275149 / 400000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU5 ha_nonneg
    have hmul_right : (260275149 / 400000 : ℝ) * a ≤ (260275149 / 400000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (260275149 / 400000 : ℝ))
    have hmul : criticalFactorHorner5 a * a ≤ (260275149 / 400000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (168 : ℝ) + criticalFactorHorner5 a * a ≤ (168 : ℝ) + (260275149 / 400000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (168 : ℝ)
      _ = (7330328427 / 8000000 : ℝ) := by norm_num
  have hL7 : (43869581 / 78125 : ℝ) ≤ criticalFactorHorner7 a := by
    unfold criticalFactorHorner7
    have hmul_left : (7197864 / 15625 : ℝ) * (4 / 5 : ℝ) ≤ (7197864 / 15625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (7197864 / 15625 : ℝ))
    have hmul_right : (7197864 / 15625 : ℝ) * a ≤ criticalFactorHorner6 a * a := by
      exact mul_le_mul_of_nonneg_right hL6 ha_nonneg
    have hmul : (7197864 / 15625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner6 a * a := le_trans hmul_left hmul_right
    calc
      (43869581 / 78125 : ℝ) = (193 : ℝ) + (7197864 / 15625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (193 : ℝ) + criticalFactorHorner6 a * a := add_le_add_right hmul (193 : ℝ)
  have hU7 : criticalFactorHorner7 a ≤ (199477553821 / 160000000 : ℝ) := by
    unfold criticalFactorHorner7
    have hmul_left : criticalFactorHorner6 a * a ≤ (7330328427 / 8000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU6 ha_nonneg
    have hmul_right : (7330328427 / 8000000 : ℝ) * a ≤ (7330328427 / 8000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (7330328427 / 8000000 : ℝ))
    have hmul : criticalFactorHorner6 a * a ≤ (7330328427 / 8000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (193 : ℝ) + criticalFactorHorner6 a * a ≤ (193 : ℝ) + (7330328427 / 8000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (193 : ℝ)
      _ = (199477553821 / 160000000 : ℝ) := by norm_num
  have hL8 : (293447074 / 390625 : ℝ) ≤ criticalFactorHorner8 a := by
    unfold criticalFactorHorner8
    have hmul_left : (43869581 / 78125 : ℝ) * (4 / 5 : ℝ) ≤ (43869581 / 78125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (43869581 / 78125 : ℝ))
    have hmul_right : (43869581 / 78125 : ℝ) * a ≤ criticalFactorHorner7 a * a := by
      exact mul_le_mul_of_nonneg_right hL7 ha_nonneg
    have hmul : (43869581 / 78125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner7 a * a := le_trans hmul_left hmul_right
    calc
      (293447074 / 390625 : ℝ) = (302 : ℝ) + (43869581 / 78125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (302 : ℝ) + criticalFactorHorner7 a * a := add_le_add_right hmul (302 : ℝ)
  have hU8 : criticalFactorHorner8 a ≤ (5554383737883 / 3200000000 : ℝ) := by
    unfold criticalFactorHorner8
    have hmul_left : criticalFactorHorner7 a * a ≤ (199477553821 / 160000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU7 ha_nonneg
    have hmul_right : (199477553821 / 160000000 : ℝ) * a ≤ (199477553821 / 160000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (199477553821 / 160000000 : ℝ))
    have hmul : criticalFactorHorner7 a * a ≤ (199477553821 / 160000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (302 : ℝ) + criticalFactorHorner7 a * a ≤ (302 : ℝ) + (199477553821 / 160000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (302 : ℝ)
      _ = (5554383737883 / 3200000000 : ℝ) := by norm_num
  have hL9 : (1976522671 / 1953125 : ℝ) ≤ criticalFactorHorner9 a := by
    unfold criticalFactorHorner9
    have hmul_left : (293447074 / 390625 : ℝ) * (4 / 5 : ℝ) ≤ (293447074 / 390625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (293447074 / 390625 : ℝ))
    have hmul_right : (293447074 / 390625 : ℝ) * a ≤ criticalFactorHorner8 a * a := by
      exact mul_le_mul_of_nonneg_right hL8 ha_nonneg
    have hmul : (293447074 / 390625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner8 a * a := le_trans hmul_left hmul_right
    calc
      (1976522671 / 1953125 : ℝ) = (411 : ℝ) + (293447074 / 390625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (411 : ℝ) + criticalFactorHorner8 a * a := add_le_add_right hmul (411 : ℝ)
  have hU9 : criticalFactorHorner9 a ≤ (154054825971309 / 64000000000 : ℝ) := by
    unfold criticalFactorHorner9
    have hmul_left : criticalFactorHorner8 a * a ≤ (5554383737883 / 3200000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU8 ha_nonneg
    have hmul_right : (5554383737883 / 3200000000 : ℝ) * a ≤ (5554383737883 / 3200000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (5554383737883 / 3200000000 : ℝ))
    have hmul : criticalFactorHorner8 a * a ≤ (5554383737883 / 3200000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (411 : ℝ) + criticalFactorHorner8 a * a ≤ (411 : ℝ) + (5554383737883 / 3200000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (411 : ℝ)
      _ = (154054825971309 / 64000000000 : ℝ) := by norm_num
  have hL10 : (12984215684 / 9765625 : ℝ) ≤ criticalFactorHorner10 a := by
    unfold criticalFactorHorner10
    have hmul_left : (1976522671 / 1953125 : ℝ) * (4 / 5 : ℝ) ≤ (1976522671 / 1953125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (1976522671 / 1953125 : ℝ))
    have hmul_right : (1976522671 / 1953125 : ℝ) * a ≤ criticalFactorHorner9 a * a := by
      exact mul_le_mul_of_nonneg_right hL9 ha_nonneg
    have hmul : (1976522671 / 1953125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner9 a * a := le_trans hmul_left hmul_right
    calc
      (12984215684 / 9765625 : ℝ) = (520 : ℝ) + (1976522671 / 1953125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (520 : ℝ) + criticalFactorHorner9 a * a := add_le_add_right hmul (520 : ℝ)
  have hU10 : criticalFactorHorner10 a ≤ (4208860997340107 / 1280000000000 : ℝ) := by
    unfold criticalFactorHorner10
    have hmul_left : criticalFactorHorner9 a * a ≤ (154054825971309 / 64000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU9 ha_nonneg
    have hmul_right : (154054825971309 / 64000000000 : ℝ) * a ≤ (154054825971309 / 64000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (154054825971309 / 64000000000 : ℝ))
    have hmul : criticalFactorHorner9 a * a ≤ (154054825971309 / 64000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (520 : ℝ) + criticalFactorHorner9 a * a ≤ (520 : ℝ) + (154054825971309 / 64000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (520 : ℝ)
      _ = (4208860997340107 / 1280000000000 : ℝ) := by norm_num
  have hL11 : (82649753361 / 48828125 : ℝ) ≤ criticalFactorHorner11 a := by
    unfold criticalFactorHorner11
    have hmul_left : (12984215684 / 9765625 : ℝ) * (4 / 5 : ℝ) ≤ (12984215684 / 9765625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (12984215684 / 9765625 : ℝ))
    have hmul_right : (12984215684 / 9765625 : ℝ) * a ≤ criticalFactorHorner10 a * a := by
      exact mul_le_mul_of_nonneg_right hL10 ha_nonneg
    have hmul : (12984215684 / 9765625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner10 a * a := le_trans hmul_left hmul_right
    calc
      (82649753361 / 48828125 : ℝ) = (629 : ℝ) + (12984215684 / 9765625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (629 : ℝ) + criticalFactorHorner10 a * a := add_le_add_right hmul (629 : ℝ)
  have hU11 : criticalFactorHorner11 a ≤ (112906202938822461 / 25600000000000 : ℝ) := by
    unfold criticalFactorHorner11
    have hmul_left : criticalFactorHorner10 a * a ≤ (4208860997340107 / 1280000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU10 ha_nonneg
    have hmul_right : (4208860997340107 / 1280000000000 : ℝ) * a ≤ (4208860997340107 / 1280000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (4208860997340107 / 1280000000000 : ℝ))
    have hmul : criticalFactorHorner10 a * a ≤ (4208860997340107 / 1280000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (629 : ℝ) + criticalFactorHorner10 a * a ≤ (629 : ℝ) + (4208860997340107 / 1280000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (629 : ℝ)
      _ = (112906202938822461 / 25600000000000 : ℝ) := by norm_num
  have hL12 : (511751357194 / 244140625 : ℝ) ≤ criticalFactorHorner12 a := by
    unfold criticalFactorHorner12
    have hmul_left : (82649753361 / 48828125 : ℝ) * (4 / 5 : ℝ) ≤ (82649753361 / 48828125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (82649753361 / 48828125 : ℝ))
    have hmul_right : (82649753361 / 48828125 : ℝ) * a ≤ criticalFactorHorner11 a * a := by
      exact mul_le_mul_of_nonneg_right hL11 ha_nonneg
    have hmul : (82649753361 / 48828125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner11 a * a := le_trans hmul_left hmul_right
    calc
      (511751357194 / 244140625 : ℝ) = (742 : ℝ) + (82649753361 / 48828125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (742 : ℝ) + criticalFactorHorner11 a * a := add_le_add_right hmul (742 : ℝ)
  have hU12 : criticalFactorHorner12 a ≤ (2976746667592916603 / 512000000000000 : ℝ) := by
    unfold criticalFactorHorner12
    have hmul_left : criticalFactorHorner11 a * a ≤ (112906202938822461 / 25600000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU11 ha_nonneg
    have hmul_right : (112906202938822461 / 25600000000000 : ℝ) * a ≤ (112906202938822461 / 25600000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (112906202938822461 / 25600000000000 : ℝ))
    have hmul : criticalFactorHorner11 a * a ≤ (112906202938822461 / 25600000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (742 : ℝ) + criticalFactorHorner11 a * a ≤ (742 : ℝ) + (112906202938822461 / 25600000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (742 : ℝ)
      _ = (2976746667592916603 / 512000000000000 : ℝ) := by norm_num
  have hL13 : (3090706600651 / 1220703125 : ℝ) ≤ criticalFactorHorner13 a := by
    unfold criticalFactorHorner13
    have hmul_left : (511751357194 / 244140625 : ℝ) * (4 / 5 : ℝ) ≤ (511751357194 / 244140625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (511751357194 / 244140625 : ℝ))
    have hmul_right : (511751357194 / 244140625 : ℝ) * a ≤ criticalFactorHorner12 a * a := by
      exact mul_le_mul_of_nonneg_right hL12 ha_nonneg
    have hmul : (511751357194 / 244140625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner12 a * a := le_trans hmul_left hmul_right
    calc
      (3090706600651 / 1220703125 : ℝ) = (855 : ℝ) + (511751357194 / 244140625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (855 : ℝ) + criticalFactorHorner12 a * a := add_le_add_right hmul (855 : ℝ)
  have hU13 : criticalFactorHorner13 a ≤ (77220373354637081869 / 10240000000000000 : ℝ) := by
    unfold criticalFactorHorner13
    have hmul_left : criticalFactorHorner12 a * a ≤ (2976746667592916603 / 512000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU12 ha_nonneg
    have hmul_right : (2976746667592916603 / 512000000000000 : ℝ) * a ≤ (2976746667592916603 / 512000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (2976746667592916603 / 512000000000000 : ℝ))
    have hmul : criticalFactorHorner12 a * a ≤ (2976746667592916603 / 512000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (855 : ℝ) + criticalFactorHorner12 a * a ≤ (855 : ℝ) + (2976746667592916603 / 512000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (855 : ℝ)
      _ = (77220373354637081869 / 10240000000000000 : ℝ) := by norm_num
  have hL14 : (18271029527604 / 6103515625 : ℝ) ≤ criticalFactorHorner14 a := by
    unfold criticalFactorHorner14
    have hmul_left : (3090706600651 / 1220703125 : ℝ) * (4 / 5 : ℝ) ≤ (3090706600651 / 1220703125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (3090706600651 / 1220703125 : ℝ))
    have hmul_right : (3090706600651 / 1220703125 : ℝ) * a ≤ criticalFactorHorner13 a * a := by
      exact mul_le_mul_of_nonneg_right hL13 ha_nonneg
    have hmul : (3090706600651 / 1220703125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner13 a * a := le_trans hmul_left hmul_right
    calc
      (18271029527604 / 6103515625 : ℝ) = (968 : ℝ) + (3090706600651 / 1220703125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (968 : ℝ) + criticalFactorHorner13 a * a := add_le_add_right hmul (968 : ℝ)
  have hU14 : criticalFactorHorner14 a ≤ (1974314987156652882987 / 204800000000000000 : ℝ) := by
    unfold criticalFactorHorner14
    have hmul_left : criticalFactorHorner13 a * a ≤ (77220373354637081869 / 10240000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU13 ha_nonneg
    have hmul_right : (77220373354637081869 / 10240000000000000 : ℝ) * a ≤ (77220373354637081869 / 10240000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (77220373354637081869 / 10240000000000000 : ℝ))
    have hmul : criticalFactorHorner13 a * a ≤ (77220373354637081869 / 10240000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (968 : ℝ) + criticalFactorHorner13 a * a ≤ (968 : ℝ) + (77220373354637081869 / 10240000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (968 : ℝ)
      _ = (1974314987156652882987 / 204800000000000000 : ℝ) := by norm_num
  have hL15 : (104974987251041 / 30517578125 : ℝ) ≤ criticalFactorHorner15 a := by
    unfold criticalFactorHorner15
    have hmul_left : (18271029527604 / 6103515625 : ℝ) * (4 / 5 : ℝ) ≤ (18271029527604 / 6103515625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (18271029527604 / 6103515625 : ℝ))
    have hmul_right : (18271029527604 / 6103515625 : ℝ) * a ≤ criticalFactorHorner14 a * a := by
      exact mul_le_mul_of_nonneg_right hL14 ha_nonneg
    have hmul : (18271029527604 / 6103515625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner14 a * a := le_trans hmul_left hmul_right
    calc
      (104974987251041 / 30517578125 : ℝ) = (1045 : ℝ) + (18271029527604 / 6103515625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (1045 : ℝ) + criticalFactorHorner14 a * a := add_le_add_right hmul (1045 : ℝ)
  have hU15 : criticalFactorHorner15 a ≤ (49689564704603016308701 / 4096000000000000000 : ℝ) := by
    unfold criticalFactorHorner15
    have hmul_left : criticalFactorHorner14 a * a ≤ (1974314987156652882987 / 204800000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU14 ha_nonneg
    have hmul_right : (1974314987156652882987 / 204800000000000000 : ℝ) * a ≤ (1974314987156652882987 / 204800000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (1974314987156652882987 / 204800000000000000 : ℝ))
    have hmul : criticalFactorHorner14 a * a ≤ (1974314987156652882987 / 204800000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (1045 : ℝ) + criticalFactorHorner14 a * a ≤ (1045 : ℝ) + (1974314987156652882987 / 204800000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (1045 : ℝ)
      _ = (49689564704603016308701 / 4096000000000000000 : ℝ) := by norm_num
  have hL16 : (517861374785414 / 152587890625 : ℝ) ≤ criticalFactorHorner16 a := by
    unfold criticalFactorHorner16
    have hmul_left : (104974987251041 / 30517578125 : ℝ) * (4 / 5 : ℝ) ≤ (104974987251041 / 30517578125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (104974987251041 / 30517578125 : ℝ))
    have hmul_right : (104974987251041 / 30517578125 : ℝ) * a ≤ criticalFactorHorner15 a * a := by
      exact mul_le_mul_of_nonneg_right hL15 ha_nonneg
    have hmul : (104974987251041 / 30517578125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner15 a * a := le_trans hmul_left hmul_right
    calc
      (517861374785414 / 152587890625 : ℝ) = (642 : ℝ) + (104974987251041 / 30517578125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (642 : ℝ) + criticalFactorHorner15 a * a := add_le_add_right hmul (642 : ℝ)
  have hU16 : criticalFactorHorner16 a ≤ (1195452628205869375100123 / 81920000000000000000 : ℝ) := by
    unfold criticalFactorHorner16
    have hmul_left : criticalFactorHorner15 a * a ≤ (49689564704603016308701 / 4096000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU15 ha_nonneg
    have hmul_right : (49689564704603016308701 / 4096000000000000000 : ℝ) * a ≤ (49689564704603016308701 / 4096000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (49689564704603016308701 / 4096000000000000000 : ℝ))
    have hmul : criticalFactorHorner15 a * a ≤ (49689564704603016308701 / 4096000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (642 : ℝ) + criticalFactorHorner15 a * a ≤ (642 : ℝ) + (49689564704603016308701 / 4096000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (642 : ℝ)
      _ = (1195452628205869375100123 / 81920000000000000000 : ℝ) := by norm_num
  have hL17 : (2253788028438531 / 762939453125 : ℝ) ≤ criticalFactorHorner17 a := by
    unfold criticalFactorHorner17
    have hmul_left : (517861374785414 / 152587890625 : ℝ) * (4 / 5 : ℝ) ≤ (517861374785414 / 152587890625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (517861374785414 / 152587890625 : ℝ))
    have hmul_right : (517861374785414 / 152587890625 : ℝ) * a ≤ criticalFactorHorner16 a * a := by
      exact mul_le_mul_of_nonneg_right hL16 ha_nonneg
    have hmul : (517861374785414 / 152587890625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner16 a * a := le_trans hmul_left hmul_right
    calc
      (2253788028438531 / 762939453125 : ℝ) = (239 : ℝ) + (517861374785414 / 152587890625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (239 : ℝ) + criticalFactorHorner16 a * a := add_le_add_right hmul (239 : ℝ)
  have hU17 : criticalFactorHorner17 a ≤ (27886988048734995627302829 / 1638400000000000000000 : ℝ) := by
    unfold criticalFactorHorner17
    have hmul_left : criticalFactorHorner16 a * a ≤ (1195452628205869375100123 / 81920000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU16 ha_nonneg
    have hmul_right : (1195452628205869375100123 / 81920000000000000000 : ℝ) * a ≤ (1195452628205869375100123 / 81920000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (1195452628205869375100123 / 81920000000000000000 : ℝ))
    have hmul : criticalFactorHorner16 a * a ≤ (1195452628205869375100123 / 81920000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (239 : ℝ) + criticalFactorHorner16 a * a ≤ (239 : ℝ) + (1195452628205869375100123 / 81920000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (239 : ℝ)
      _ = (27886988048734995627302829 / 1638400000000000000000 : ℝ) := by norm_num
  have hL18 : (8389541762191624 / 3814697265625 : ℝ) ≤ criticalFactorHorner18 a := by
    unfold criticalFactorHorner18
    have hmul_left : (2253788028438531 / 762939453125 : ℝ) * (4 / 5 : ℝ) ≤ (2253788028438531 / 762939453125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (2253788028438531 / 762939453125 : ℝ))
    have hmul_right : (2253788028438531 / 762939453125 : ℝ) * a ≤ criticalFactorHorner17 a * a := by
      exact mul_le_mul_of_nonneg_right hL17 ha_nonneg
    have hmul : (2253788028438531 / 762939453125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner17 a * a := le_trans hmul_left hmul_right
    calc
      (8389541762191624 / 3814697265625 : ℝ) = (-164 : ℝ) + (2253788028438531 / 762939453125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (-164 : ℝ) + criticalFactorHorner17 a * a := add_le_add_right hmul (-164 : ℝ)
  have hU18 : criticalFactorHorner18 a ≤ (636026773120904899427965067 / 32768000000000000000000 : ℝ) := by
    unfold criticalFactorHorner18
    have hmul_left : criticalFactorHorner17 a * a ≤ (27886988048734995627302829 / 1638400000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU17 ha_nonneg
    have hmul_right : (27886988048734995627302829 / 1638400000000000000000 : ℝ) * a ≤ (27886988048734995627302829 / 1638400000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (27886988048734995627302829 / 1638400000000000000000 : ℝ))
    have hmul : criticalFactorHorner17 a * a ≤ (27886988048734995627302829 / 1638400000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-164 : ℝ) + criticalFactorHorner17 a * a ≤ (-164 : ℝ) + (27886988048734995627302829 / 1638400000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-164 : ℝ)
      _ = (636026773120904899427965067 / 32768000000000000000000 : ℝ) := by norm_num
  have hL19 : (22743500300719621 / 19073486328125 : ℝ) ≤ criticalFactorHorner19 a := by
    unfold criticalFactorHorner19
    have hmul_left : (8389541762191624 / 3814697265625 : ℝ) * (4 / 5 : ℝ) ≤ (8389541762191624 / 3814697265625 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (8389541762191624 / 3814697265625 : ℝ))
    have hmul_right : (8389541762191624 / 3814697265625 : ℝ) * a ≤ criticalFactorHorner18 a * a := by
      exact mul_le_mul_of_nonneg_right hL18 ha_nonneg
    have hmul : (8389541762191624 / 3814697265625 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner18 a * a := le_trans hmul_left hmul_right
    calc
      (22743500300719621 / 19073486328125 : ℝ) = (-567 : ℝ) + (8389541762191624 / 3814697265625 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (-567 : ℝ) + criticalFactorHorner18 a * a := add_le_add_right hmul (-567 : ℝ)
  have hU19 : criticalFactorHorner19 a ≤ (14257026661780812686843196541 / 655360000000000000000000 : ℝ) := by
    unfold criticalFactorHorner19
    have hmul_left : criticalFactorHorner18 a * a ≤ (636026773120904899427965067 / 32768000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU18 ha_nonneg
    have hmul_right : (636026773120904899427965067 / 32768000000000000000000 : ℝ) * a ≤ (636026773120904899427965067 / 32768000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (636026773120904899427965067 / 32768000000000000000000 : ℝ))
    have hmul : criticalFactorHorner18 a * a ≤ (636026773120904899427965067 / 32768000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-567 : ℝ) + criticalFactorHorner18 a * a ≤ (-567 : ℝ) + (636026773120904899427965067 / 32768000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-567 : ℝ)
      _ = (14257026661780812686843196541 / 655360000000000000000000 : ℝ) := by norm_num
  have hL20 : (-6528582277766 / 95367431640625 : ℝ) ≤ criticalFactorHorner20 a := by
    unfold criticalFactorHorner20
    have hmul_left : (22743500300719621 / 19073486328125 : ℝ) * (4 / 5 : ℝ) ≤ (22743500300719621 / 19073486328125 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_left ha_lo (by norm_num : (0 : ℝ) ≤ (22743500300719621 / 19073486328125 : ℝ))
    have hmul_right : (22743500300719621 / 19073486328125 : ℝ) * a ≤ criticalFactorHorner19 a * a := by
      exact mul_le_mul_of_nonneg_right hL19 ha_nonneg
    have hmul : (22743500300719621 / 19073486328125 : ℝ) * (4 / 5 : ℝ) ≤ criticalFactorHorner19 a * a := le_trans hmul_left hmul_right
    calc
      (-6528582277766 / 95367431640625 : ℝ) = (-954 : ℝ) + (22743500300719621 / 19073486328125 : ℝ) * (4 / 5 : ℝ) := by norm_num
      _ ≤ (-954 : ℝ) + criticalFactorHorner19 a * a := add_le_add_right hmul (-954 : ℝ)
  have hU20 : criticalFactorHorner20 a ≤ (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) := by
    unfold criticalFactorHorner20
    have hmul_left : criticalFactorHorner19 a * a ≤ (14257026661780812686843196541 / 655360000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU19 ha_nonneg
    have hmul_right : (14257026661780812686843196541 / 655360000000000000000000 : ℝ) * a ≤ (14257026661780812686843196541 / 655360000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (14257026661780812686843196541 / 655360000000000000000000 : ℝ))
    have hmul : criticalFactorHorner19 a * a ≤ (14257026661780812686843196541 / 655360000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-954 : ℝ) + criticalFactorHorner19 a * a ≤ (-954 : ℝ) + (14257026661780812686843196541 / 655360000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-954 : ℝ)
      _ = (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) := by norm_num
  have hL21 : (-1278952336996975559 / 953674316406250 : ℝ) ≤ criticalFactorHorner21 a := by
    unfold criticalFactorHorner21
    have hmul_left : (-6528582277766 / 95367431640625 : ℝ) * (23 / 20 : ℝ) ≤ (-6528582277766 / 95367431640625 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-6528582277766 / 95367431640625 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-6528582277766 / 95367431640625 : ℝ) * a ≤ criticalFactorHorner20 a * a := by
      exact mul_le_mul_of_nonneg_right hL20 ha_nonneg
    have hmul : (-6528582277766 / 95367431640625 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner20 a * a := le_trans hmul_left hmul_right
    calc
      (-1278952336996975559 / 953674316406250 : ℝ) = (-1341 : ℝ) + (-6528582277766 / 95367431640625 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-1341 : ℝ) + criticalFactorHorner20 a * a := add_le_add_right hmul (-1341 : ℝ)
  have hU21 : criticalFactorHorner21 a ≤ (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner21
    have hmul_left : criticalFactorHorner20 a * a ≤ (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU20 ha_nonneg
    have hmul_right : (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) * a ≤ (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (315407344420958691797393520443 / 13107200000000000000000000 : ℝ))
    have hmul : criticalFactorHorner20 a * a ≤ (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-1341 : ℝ) + criticalFactorHorner20 a * a ≤ (-1341 : ℝ) + (315407344420958691797393520443 / 13107200000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-1341 : ℝ)
      _ = (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) := by norm_num
  have hL22 : (-62374888125930437857 / 19073486328125000 : ℝ) ≤ criticalFactorHorner22 a := by
    unfold criticalFactorHorner22
    have hmul_left : (-1278952336996975559 / 953674316406250 : ℝ) * (23 / 20 : ℝ) ≤ (-1278952336996975559 / 953674316406250 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-1278952336996975559 / 953674316406250 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-1278952336996975559 / 953674316406250 : ℝ) * a ≤ criticalFactorHorner21 a * a := by
      exact mul_le_mul_of_nonneg_right hL21 ha_nonneg
    have hmul : (-1278952336996975559 / 953674316406250 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner21 a * a := le_trans hmul_left hmul_right
    calc
      (-62374888125930437857 / 19073486328125000 : ℝ) = (-1728 : ℝ) + (-1278952336996975559 / 953674316406250 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-1728 : ℝ) + criticalFactorHorner21 a * a := add_le_add_right hmul (-1728 : ℝ)
  have hU22 : criticalFactorHorner22 a ≤ (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner22
    have hmul_left : criticalFactorHorner21 a * a ≤ (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU21 ha_nonneg
    have hmul_right : (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) * a ≤ (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner21 a * a ≤ (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-1728 : ℝ) + criticalFactorHorner21 a * a ≤ (-1728 : ℝ) + (6902833817682049911340050970189 / 262144000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-1728 : ℝ)
      _ = (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) := by norm_num
  have hL23 : (-2330694814591712570711 / 381469726562500000 : ℝ) ≤ criticalFactorHorner23 a := by
    unfold criticalFactorHorner23
    have hmul_left : (-62374888125930437857 / 19073486328125000 : ℝ) * (23 / 20 : ℝ) ≤ (-62374888125930437857 / 19073486328125000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-62374888125930437857 / 19073486328125000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-62374888125930437857 / 19073486328125000 : ℝ) * a ≤ criticalFactorHorner22 a * a := by
      exact mul_le_mul_of_nonneg_right hL22 ha_nonneg
    have hmul : (-62374888125930437857 / 19073486328125000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner22 a * a := le_trans hmul_left hmul_right
    calc
      (-2330694814591712570711 / 381469726562500000 : ℝ) = (-2349 : ℝ) + (-62374888125930437857 / 19073486328125000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-2349 : ℝ) + criticalFactorHorner22 a * a := add_le_add_right hmul (-2349 : ℝ)
  have hU23 : criticalFactorHorner23 a ≤ (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner23
    have hmul_left : criticalFactorHorner22 a * a ≤ (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU22 ha_nonneg
    have hmul_right : (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) * a ≤ (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner22 a * a ≤ (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-2349 : ℝ) + criticalFactorHorner22 a * a ≤ (-2349 : ℝ) + (149705481166687147960821172314347 / 5242880000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-2349 : ℝ)
      _ = (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) := by norm_num
  have hL24 : (-94392723899671889126353 / 7629394531250000000 : ℝ) ≤ criticalFactorHorner24 a := by
    unfold criticalFactorHorner24
    have hmul_left : (-2330694814591712570711 / 381469726562500000 : ℝ) * (23 / 20 : ℝ) ≤ (-2330694814591712570711 / 381469726562500000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-2330694814591712570711 / 381469726562500000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-2330694814591712570711 / 381469726562500000 : ℝ) * a ≤ criticalFactorHorner23 a * a := by
      exact mul_le_mul_of_nonneg_right hL23 ha_nonneg
    have hmul : (-2330694814591712570711 / 381469726562500000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner23 a * a := le_trans hmul_left hmul_right
    calc
      (-94392723899671889126353 / 7629394531250000000 : ℝ) = (-5346 : ℝ) + (-2330694814591712570711 / 381469726562500000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-5346 : ℝ) + criticalFactorHorner23 a * a := add_le_add_right hmul (-5346 : ℝ)
  have hU24 : criticalFactorHorner24 a ≤ (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner24
    have hmul_left : criticalFactorHorner23 a * a ≤ (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU23 ha_nonneg
    have hmul_right : (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) * a ≤ (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner23 a * a ≤ (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-5346 : ℝ) + criticalFactorHorner23 a * a ≤ (-5346 : ℝ) + (3196915564433804403098886963229981 / 104857600000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-5346 : ℝ)
      _ = (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) := by norm_num
  have hL25 : (-3444073421176828449906119 / 152587890625000000000 : ℝ) ≤ criticalFactorHorner25 a := by
    unfold criticalFactorHorner25
    have hmul_left : (-94392723899671889126353 / 7629394531250000000 : ℝ) * (23 / 20 : ℝ) ≤ (-94392723899671889126353 / 7629394531250000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-94392723899671889126353 / 7629394531250000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-94392723899671889126353 / 7629394531250000000 : ℝ) * a ≤ criticalFactorHorner24 a * a := by
      exact mul_le_mul_of_nonneg_right hL24 ha_nonneg
    have hmul : (-94392723899671889126353 / 7629394531250000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner24 a * a := le_trans hmul_left hmul_right
    calc
      (-3444073421176828449906119 / 152587890625000000000 : ℝ) = (-8343 : ℝ) + (-94392723899671889126353 / 7629394531250000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-8343 : ℝ) + criticalFactorHorner24 a * a := add_le_add_right hmul (-8343 : ℝ)
  have hU25 : criticalFactorHorner25 a ≤ (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner25
    have hmul_left : criticalFactorHorner24 a * a ≤ (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU24 ha_nonneg
    have hmul_right : (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) * a ≤ (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner24 a * a ≤ (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-8343 : ℝ) + criticalFactorHorner24 a * a ≤ (-8343 : ℝ) + (62317683389977501271274400154289563 / 2097152000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-8343 : ℝ)
      _ = (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) := by norm_num
  have hL26 : (-113820622280817054347840737 / 3051757812500000000000 : ℝ) ≤ criticalFactorHorner26 a := by
    unfold criticalFactorHorner26
    have hmul_left : (-3444073421176828449906119 / 152587890625000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-3444073421176828449906119 / 152587890625000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-3444073421176828449906119 / 152587890625000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-3444073421176828449906119 / 152587890625000000000 : ℝ) * a ≤ criticalFactorHorner25 a * a := by
      exact mul_le_mul_of_nonneg_right hL25 ha_nonneg
    have hmul : (-3444073421176828449906119 / 152587890625000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner25 a * a := le_trans hmul_left hmul_right
    calc
      (-113820622280817054347840737 / 3051757812500000000000 : ℝ) = (-11340 : ℝ) + (-3444073421176828449906119 / 152587890625000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-11340 : ℝ) + criticalFactorHorner25 a * a := add_le_add_right hmul (-11340 : ℝ)
  have hU26 : criticalFactorHorner26 a ≤ (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner26
    have hmul_left : criticalFactorHorner25 a * a ≤ (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU25 ha_nonneg
    have hmul_right : (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) * a ≤ (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner25 a * a ≤ (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-11340 : ℝ) + criticalFactorHorner25 a * a ≤ (-11340 : ℝ) + (1083375935249482529239311203548659949 / 41943040000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-11340 : ℝ)
      _ = (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) := by norm_num
  have hL27 : (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) ≤ criticalFactorHorner27 a := by
    unfold criticalFactorHorner27
    have hmul_left : (-113820622280817054347840737 / 3051757812500000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-113820622280817054347840737 / 3051757812500000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-113820622280817054347840737 / 3051757812500000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-113820622280817054347840737 / 3051757812500000000000 : ℝ) * a ≤ criticalFactorHorner26 a * a := by
      exact mul_le_mul_of_nonneg_right hL26 ha_nonneg
    have hmul : (-113820622280817054347840737 / 3051757812500000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner26 a * a := le_trans hmul_left hmul_right
    calc
      (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) = (-14337 : ℝ) + (-113820622280817054347840737 / 3051757812500000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-14337 : ℝ) + criticalFactorHorner26 a * a := add_le_add_right hmul (-14337 : ℝ)
  have hU27 : criticalFactorHorner27 a ≤ (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner27
    have hmul_left : criticalFactorHorner26 a * a ≤ (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU26 ha_nonneg
    have hmul_right : (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) * a ≤ (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner26 a * a ≤ (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-14337 : ℝ) + criticalFactorHorner26 a * a ≤ (-14337 : ℝ) + (15404965038738098172504157681619178827 / 838860800000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-14337 : ℝ)
      _ = (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) := by norm_num
  have hL28 : (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) ≤ criticalFactorHorner28 a := by
    unfold criticalFactorHorner28
    have hmul_left : (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) * a ≤ criticalFactorHorner27 a * a := by
      exact mul_le_mul_of_nonneg_right hL27 ha_nonneg
    have hmul : (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner27 a * a := le_trans hmul_left hmul_right
    calc
      (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) = (-17406 : ℝ) + (-3492935347615042250000336951 / 61035156250000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-17406 : ℝ) + criticalFactorHorner27 a * a := add_le_add_right hmul (-17406 : ℝ)
  have hU28 : criticalFactorHorner28 a ≤ (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner28
    have hmul_left : criticalFactorHorner27 a * a ≤ (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hU27 ha_nonneg
    have hmul_right : (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) * a ≤ (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by
      exact mul_le_mul_of_nonneg_left ha_hi (by norm_num : (0 : ℝ) ≤ (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ))
    have hmul : criticalFactorHorner27 a * a ≤ (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-17406 : ℝ) + criticalFactorHorner27 a * a ≤ (-17406 : ℝ) + (113779250098976257967595626677241113021 / 16777216000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := add_le_add_right hmul (-17406 : ℝ)
      _ = (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) := by norm_num
  have hL29 : (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) ≤ criticalFactorHorner29 a := by
    unfold criticalFactorHorner29
    have hmul_left : (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) * a ≤ criticalFactorHorner28 a * a := by
      exact mul_le_mul_of_nonneg_right hL28 ha_nonneg
    have hmul : (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner28 a * a := le_trans hmul_left hmul_right
    calc
      (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) = (-20475 : ℝ) + (-101585071588895971750007749873 / 1220703125000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-20475 : ℝ) + criticalFactorHorner28 a * a := add_le_add_right hmul (-20475 : ℝ)
  have hU29 : criticalFactorHorner29 a ≤ (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner29
    have hp_nonpos : criticalFactorHorner28 a ≤ 0 := le_trans hU28 (by norm_num : (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner28 a * a ≤ criticalFactorHorner28 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner28 a * (4 / 5 : ℝ) ≤ (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU28 ha_lo_nonneg
    have hmul : criticalFactorHorner28 a * a ≤ (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-20475 : ℝ) + criticalFactorHorner28 a * a ≤ (-20475 : ℝ) + (-3223561681643546066745300586423454400517 / 335544320000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-20475 : ℝ)
      _ = (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) := by norm_num
  have hL30 : (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) ≤ criticalFactorHorner30 a := by
    unfold criticalFactorHorner30
    have hmul_left : (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) * a ≤ criticalFactorHorner29 a * a := by
      exact mul_le_mul_of_nonneg_right hL29 ha_nonneg
    have hmul : (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner29 a * a := le_trans hmul_left hmul_right
    calc
      (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) = (-23544 : ℝ) + (-2836334576232107350250178247079 / 24414062500000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-23544 : ℝ) + criticalFactorHorner29 a * a := add_le_add_right hmul (-23544 : ℝ)
  have hU30 : criticalFactorHorner30 a ≤ (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner30
    have hp_nonpos : criticalFactorHorner29 a ≤ 0 := le_trans hU29 (by norm_num : (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner29 a * a ≤ criticalFactorHorner29 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner29 a * (4 / 5 : ℝ) ≤ (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU29 ha_lo_nonneg
    have hmul : criticalFactorHorner29 a * a ≤ (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-23544 : ℝ) + criticalFactorHorner29 a * a ≤ (-23544 : ℝ) + (-11811399121643546066745300586423454400517 / 419430400000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-23544 : ℝ)
      _ = (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) := by norm_num
  have hL31 : (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) ≤ criticalFactorHorner31 a := by
    unfold criticalFactorHorner31
    have hmul_left : (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) * a ≤ criticalFactorHorner30 a * a := by
      exact mul_le_mul_of_nonneg_right hL30 ha_nonneg
    have hmul : (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner30 a * a := le_trans hmul_left hmul_right
    calc
      (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) = (-18873 : ℝ) + (-76731789003338469055754099682817 / 488281250000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-18873 : ℝ) + criticalFactorHorner30 a * a := add_le_add_right hmul (-18873 : ℝ)
  have hU31 : criticalFactorHorner31 a ≤ (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner31
    have hp_nonpos : criticalFactorHorner30 a ≤ 0 := le_trans hU30 (by norm_num : (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner30 a * a ≤ criticalFactorHorner30 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner30 a * (4 / 5 : ℝ) ≤ (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU30 ha_lo_nonneg
    have hmul : criticalFactorHorner30 a * a ≤ (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-18873 : ℝ) + criticalFactorHorner30 a * a ≤ (-18873 : ℝ) + (-24155235793643546066745300586423454400517 / 524288000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-18873 : ℝ)
      _ = (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) := by norm_num
  have hL32 : (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) ≤ criticalFactorHorner32 a := by
    unfold criticalFactorHorner32
    have hmul_left : (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) * a ≤ criticalFactorHorner31 a * a := by
      exact mul_le_mul_of_nonneg_right hL31 ha_nonneg
    have hmul : (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner31 a * a := le_trans hmul_left hmul_right
    calc
      (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) = (-16146 : ℝ) + (-1949137787701784788282344292704791 / 9765625000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-16146 : ℝ) + criticalFactorHorner31 a * a := add_le_add_right hmul (-16146 : ℝ)
  have hU32 : criticalFactorHorner32 a ≤ (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner32
    have hp_nonpos : criticalFactorHorner31 a ≤ 0 := le_trans hU31 (by norm_num : (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner31 a * a ≤ criticalFactorHorner31 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner31 a * (4 / 5 : ℝ) ≤ (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU31 ha_lo_nonneg
    have hmul : criticalFactorHorner31 a * a ≤ (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-16146 : ℝ) + criticalFactorHorner31 a * a ≤ (-16146 : ℝ) + (-36523845073643546066745300586423454400517 / 655360000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-16146 : ℝ)
      _ = (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) := by norm_num
  have hL33 : (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) ≤ criticalFactorHorner33 a := by
    unfold criticalFactorHorner33
    have hmul_left : (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) * a ≤ criticalFactorHorner32 a * a := by
      exact mul_le_mul_of_nonneg_right hL32 ha_nonneg
    have hmul : (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner32 a * a := le_trans hmul_left hmul_right
    calc
      (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) = (-13419 : ℝ) + (-47983684742141050130493918732210193 / 195312500000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-13419 : ℝ) + criticalFactorHorner32 a * a := add_le_add_right hmul (-13419 : ℝ)
  have hU33 : criticalFactorHorner33 a ≤ (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner33
    have hp_nonpos : criticalFactorHorner32 a ≤ 0 := le_trans hU32 (by norm_num : (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner32 a * a ≤ criticalFactorHorner32 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner32 a * (4 / 5 : ℝ) ≤ (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU32 ha_lo_nonneg
    have hmul : criticalFactorHorner32 a * a ≤ (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-13419 : ℝ) + criticalFactorHorner32 a * a ≤ (-13419 : ℝ) + (-49750648273643546066745300586423454400517 / 819200000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-13419 : ℝ)
      _ = (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) := by norm_num
  have hL34 : (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) ≤ criticalFactorHorner34 a := by
    unfold criticalFactorHorner34
    have hmul_left : (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner33 a * a := by
      exact mul_le_mul_of_nonneg_right hL33 ha_nonneg
    have hmul : (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner33 a * a := le_trans hmul_left hmul_right
    calc
      (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) = (-10692 : ℝ) + (-1156042717819244153001360130840834439 / 3906250000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-10692 : ℝ) + criticalFactorHorner33 a * a := add_le_add_right hmul (-10692 : ℝ)
  have hU34 : criticalFactorHorner34 a ≤ (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner34
    have hp_nonpos : criticalFactorHorner33 a ≤ 0 := le_trans hU33 (by norm_num : (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner33 a * a ≤ criticalFactorHorner33 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner33 a * (4 / 5 : ℝ) ≤ (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU33 ha_lo_nonneg
    have hmul : criticalFactorHorner33 a * a ≤ (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-10692 : ℝ) + criticalFactorHorner33 a * a ≤ (-10692 : ℝ) + (-63491704273643546066745300586423454400517 / 1024000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-10692 : ℝ)
      _ = (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) := by norm_num
  have hL35 : (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) ≤ criticalFactorHorner35 a := by
    unfold criticalFactorHorner35
    have hmul_left : (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner34 a * a := by
      exact mul_le_mul_of_nonneg_right hL34 ha_nonneg
    have hmul : (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner34 a * a := le_trans hmul_left hmul_right
    calc
      (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) = (-7965 : ℝ) + (-27424295009842615519031283009339192097 / 78125000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-7965 : ℝ) + criticalFactorHorner34 a * a := add_le_add_right hmul (-7965 : ℝ)
  have hU35 : criticalFactorHorner35 a ≤ (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner35
    have hp_nonpos : criticalFactorHorner34 a ≤ 0 := le_trans hU34 (by norm_num : (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner34 a * a ≤ criticalFactorHorner34 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner34 a * (4 / 5 : ℝ) ≤ (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU34 ha_lo_nonneg
    have hmul : criticalFactorHorner34 a * a ≤ (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-7965 : ℝ) + criticalFactorHorner34 a * a ≤ (-7965 : ℝ) + (-77177464273643546066745300586423454400517 / 1280000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-7965 : ℝ)
      _ = (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) := by norm_num
  have hL36 : (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner36 a := by
    unfold criticalFactorHorner36
    have hmul_left : (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner35 a * a := by
      exact mul_le_mul_of_nonneg_right hL35 ha_nonneg
    have hmul : (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner35 a * a := le_trans hmul_left hmul_right
    calc
      (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) = (-5670 : ℝ) + (-643204097726380156937719509214801418231 / 1562500000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-5670 : ℝ) + criticalFactorHorner35 a * a := add_le_add_right hmul (-5670 : ℝ)
  have hU36 : criticalFactorHorner36 a ≤ (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner36
    have hp_nonpos : criticalFactorHorner35 a ≤ 0 := le_trans hU35 (by norm_num : (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner35 a * a ≤ criticalFactorHorner35 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner35 a * (4 / 5 : ℝ) ≤ (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU35 ha_lo_nonneg
    have hmul : criticalFactorHorner35 a * a ≤ (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-5670 : ℝ) + criticalFactorHorner35 a * a ≤ (-5670 : ℝ) + (-89921464273643546066745300586423454400517 / 1600000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-5670 : ℝ)
      _ = (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) := by norm_num
  have hL37 : (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner37 a := by
    unfold criticalFactorHorner37
    have hmul_left : (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner36 a * a := by
      exact mul_le_mul_of_nonneg_right hL36 ha_nonneg
    have hmul : (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner36 a * a := le_trans hmul_left hmul_right
    calc
      (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) = (-3375 : ℝ) + (-14970881747706743609567548711940432619313 / 31250000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-3375 : ℝ) + criticalFactorHorner36 a * a := add_le_add_right hmul (-3375 : ℝ)
  have hU37 : criticalFactorHorner37 a ≤ (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner37
    have hp_nonpos : criticalFactorHorner36 a ≤ 0 := le_trans hU36 (by norm_num : (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner36 a * a ≤ criticalFactorHorner36 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner36 a * (4 / 5 : ℝ) ≤ (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU36 ha_lo_nonneg
    have hmul : criticalFactorHorner36 a * a ≤ (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-3375 : ℝ) + criticalFactorHorner36 a * a ≤ (-3375 : ℝ) + (-101261464273643546066745300586423454400517 / 2000000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-3375 : ℝ)
      _ = (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) := by norm_num
  have hL38 : (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner38 a := by
    unfold criticalFactorHorner38
    have hmul_left : (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner37 a * a := by
      exact mul_le_mul_of_nonneg_right hL37 ha_nonneg
    have hmul : (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner37 a * a := le_trans hmul_left hmul_right
    calc
      (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) = (-1080 : ℝ) + (-346439655197255103020053620374629950244199 / 625000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-1080 : ℝ) + criticalFactorHorner37 a * a := add_le_add_right hmul (-1080 : ℝ)
  have hU38 : criticalFactorHorner38 a ≤ (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner38
    have hp_nonpos : criticalFactorHorner37 a ≤ 0 := le_trans hU37 (by norm_num : (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner37 a * a ≤ criticalFactorHorner37 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner37 a * (4 / 5 : ℝ) ≤ (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU37 ha_lo_nonneg
    have hmul : criticalFactorHorner37 a * a ≤ (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-1080 : ℝ) + criticalFactorHorner37 a * a ≤ (-1080 : ℝ) + (-109698964273643546066745300586423454400517 / 2500000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-1080 : ℝ)
      _ = (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) := by norm_num
  have hL39 : (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner39 a := by
    unfold criticalFactorHorner39
    have hmul_left : (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner38 a * a := by
      exact mul_le_mul_of_nonneg_right hL38 ha_nonneg
    have hmul : (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner38 a * a := le_trans hmul_left hmul_right
    calc
      (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) = (-2160 : ℝ) + (-7981612069536867369461233268616488855616577 / 12500000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-2160 : ℝ) + criticalFactorHorner38 a * a := add_le_add_right hmul (-2160 : ℝ)
  have hU39 : criticalFactorHorner39 a ≤ (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner39
    have hp_nonpos : criticalFactorHorner38 a ≤ 0 := le_trans hU38 (by norm_num : (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner38 a * a ≤ criticalFactorHorner38 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner38 a * (4 / 5 : ℝ) ≤ (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU38 ha_lo_nonneg
    have hmul : criticalFactorHorner38 a * a ≤ (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-2160 : ℝ) + criticalFactorHorner38 a * a ≤ (-2160 : ℝ) + (-113073964273643546066745300586423454400517 / 3125000000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-2160 : ℝ)
      _ = (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) := by norm_num
  have hL40 : (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner40 a := by
    unfold criticalFactorHorner40
    have hmul_left : (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner39 a * a := by
      exact mul_le_mul_of_nonneg_right hL39 ha_nonneg
    have hmul : (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner39 a * a := le_trans hmul_left hmul_right
    calc
      (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) = (-1620 : ℝ) + (-184117077599347949497608365178179243679181271 / 250000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-1620 : ℝ) + criticalFactorHorner39 a * a := add_le_add_right hmul (-1620 : ℝ)
  have hU40 : criticalFactorHorner40 a ≤ (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner40
    have hp_nonpos : criticalFactorHorner39 a ≤ 0 := le_trans hU39 (by norm_num : (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner39 a * a ≤ criticalFactorHorner39 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner39 a * (4 / 5 : ℝ) ≤ (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU39 ha_lo_nonneg
    have hmul : criticalFactorHorner39 a * a ≤ (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-1620 : ℝ) + criticalFactorHorner39 a * a ≤ (-1620 : ℝ) + (-121511464273643546066745300586423454400517 / 3906250000000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-1620 : ℝ)
      _ = (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) := by norm_num
  have hL41 : (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner41 a := by
    unfold criticalFactorHorner41
    have hmul_left : (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner40 a * a := by
      exact mul_le_mul_of_nonneg_right hL40 ha_nonneg
    have hmul : (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner40 a * a := le_trans hmul_left hmul_right
    calc
      (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) = (-1080 : ℝ) + (-4242792784785002838444992399098122604621169233 / 5000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-1080 : ℝ) + criticalFactorHorner40 a * a := add_le_add_right hmul (-1080 : ℝ)
  have hU41 : criticalFactorHorner41 a ≤ (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner41
    have hp_nonpos : criticalFactorHorner40 a ≤ 0 := le_trans hU40 (by norm_num : (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner40 a * a ≤ criticalFactorHorner40 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner40 a * (4 / 5 : ℝ) ≤ (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU40 ha_lo_nonneg
    have hmul : criticalFactorHorner40 a * a ≤ (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-1080 : ℝ) + criticalFactorHorner40 a * a ≤ (-1080 : ℝ) + (-129421620523643546066745300586423454400517 / 4882812500000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-1080 : ℝ)
      _ = (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) := by norm_num
  have hL42 : (-2248001383151266501537400979122906857844598524257 / 2000000000000000000000000000000000000000000 : ℝ) ≤ criticalFactorHorner42 a := by
    unfold criticalFactorHorner42
    have hmul_left : (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) * a := by
      exact mul_le_mul_of_nonpos_left ha_hi (by norm_num : (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_right : (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) * a ≤ criticalFactorHorner41 a * a := by
      exact mul_le_mul_of_nonneg_right hL41 ha_nonneg
    have hmul : (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) ≤ criticalFactorHorner41 a * a := le_trans hmul_left hmul_right
    calc
      (-2248001383151266501537400979122906857844598524257 / 2000000000000000000000000000000000000000000 : ℝ) = (-540 : ℝ) + (-97692234050055065284234825179256819906286892359 / 100000000000000000000000000000000000000000 : ℝ) * (23 / 20 : ℝ) := by norm_num
      _ ≤ (-540 : ℝ) + criticalFactorHorner41 a * a := add_le_add_right hmul (-540 : ℝ)
  have hU42 : criticalFactorHorner42 a ≤ (-140133290445518546066745300586423454400517 / 7629394531250000000000000000000000000 : ℝ) := by
    unfold criticalFactorHorner42
    have hp_nonpos : criticalFactorHorner41 a ≤ 0 := le_trans hU41 (by norm_num : (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) ≤ (0 : ℝ))
    have hmul_left : criticalFactorHorner41 a * a ≤ criticalFactorHorner41 a * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonpos_left ha_lo hp_nonpos
    have hmul_right : criticalFactorHorner41 a * (4 / 5 : ℝ) ≤ (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hU41 ha_lo_nonneg
    have hmul : criticalFactorHorner41 a * a ≤ (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := le_trans hmul_left hmul_right
    calc
      (-540 : ℝ) + criticalFactorHorner41 a * a ≤ (-540 : ℝ) + (-136013417398643546066745300586423454400517 / 6103515625000000000000000000000000000 : ℝ) * (4 / 5 : ℝ) := add_le_add_right hmul (-540 : ℝ)
      _ = (-140133290445518546066745300586423454400517 / 7629394531250000000000000000000000000 : ℝ) := by norm_num
  rw [criticalFactorPoly_horner]
  exact lt_of_le_of_lt hU42 (by norm_num : (-140133290445518546066745300586423454400517 / 7629394531250000000000000000000000000 : ℝ) < (0 : ℝ))

/-- Consequence of the interval polynomial certificate: throughout the
candidate interval, away from the center where the square factor vanishes, the
factorized critical model is strictly negative. -/
theorem criticalFactorModel_neg_candidate_interval
    {a : ℝ}
    (ha_lo : (4 / 5 : ℝ) ≤ a)
    (ha_hi : a ≤ (23 / 20 : ℝ))
    (ha_ne : a ≠ 1) :
    criticalFactorModel a < 0 := by
  have hp : criticalFactorPoly a < 0 :=
    criticalFactorPoly_neg_candidate_interval ha_lo ha_hi
  have ha_nonneg : 0 ≤ a := by nlinarith
  have hsq : 0 < (a - 1) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr ha_ne)
  have ha8_le : a ^ 8 ≤ (23 / 20 : ℝ) ^ 8 :=
    pow_le_pow_left₀ ha_nonneg ha_hi 8
  have ha8_lt_five : a ^ 8 < 5 := by
    have hconst : (23 / 20 : ℝ) ^ 8 < 5 := by norm_num
    exact lt_of_le_of_lt ha8_le hconst
  have hsub_neg : a ^ 8 - 5 < 0 := by nlinarith
  have hadd_pos : 0 < (a ^ 8 + 3) ^ 3 := by positivity
  unfold criticalFactorModel
  apply div_neg_of_pos_of_neg
  · exact neg_pos.mpr (mul_neg_of_pos_of_neg hsq hp)
  · have h96 : 0 < (96 : ℝ) := by norm_num
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h96 hsub_neg) hadd_pos

end

end CriticalBoundaryInterval
end Impossibility
end TauSwap
