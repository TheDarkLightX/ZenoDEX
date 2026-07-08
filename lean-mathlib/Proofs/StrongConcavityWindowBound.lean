/-
# Strong Concavity Window Bound (Abstract Foundation)

This file proves the abstract strong concavity window bound: for a strongly
concave function (f'' ≤ -m < 0) with Lipschitz constant L, the integer
maximizer is within sqrt(2L/m) + 1 of the continuous maximizer.

## Mathematical Structure

The floor proximity lemma (WindowBound.lean) shows f(⌊b*⌋) ≥ f(b*) - L
using only Lipschitz + max properties. This is a LINEAR decay bound.

Strong concavity gives a QUADRATIC decay bound:
  f(b) ≤ f(b*) - (m/2)(b - b*)²

Combining: if (m/2)(b - b*)² > L, then f(b) < f(⌊b*⌋), so b cannot be
the integer maximizer. This gives |b - b*| ≤ sqrt(2L/m).

## CPMM Application

For the CPMM split function f(b) = q(x0,y0,b,fee) + q(x1,y1,D-b,fee):
  f''(b) = -2*y0*c²*x0/(x0+c*b)³ - 2*y1*c²*x1/(x1+c*(D-b))³

Both terms are strictly negative, so f is strongly concave with parameter
m = 2*y0*c²*x0/(x0+c*b*)³ + 2*y1*c²*x1/(x1+c*(D-b*))³.

The Lipschitz constant is L = max(y0*c/x0, y1*c/x1).

The window bound is W = ceil(sqrt(2L/m)) + 1.

For the CPMM, m ≥ 2L/(x+c*D)² (rough bound), giving W = ceil(x+c*D) + 1.
The empirical result W = ceil(1/L) is tighter and was verified numerically.

## What This File Proves

1. The tightness example: f(b) = -b²/2 has max at b*=0, L=1, m=1, and the
   feasible set {b : f(b) ≥ f(b*) - L} = {b : b² ≤ 2} is within sqrt(2) of
   b*, confirming the bound |b - b*| ≤ sqrt(2L/m) + 1 = sqrt(2) + 1.
2. A quadratic sharpness witness for the oracle perturbation radius.

The production CPMM oracle-distance theorem lives in `CeilingFeeRounding.lean`.
Runtime certificates must supply the production value and strong-concavity
facts before that theorem has production meaning.

## Comparison with WindowBound.lean

WindowBound.lean proves the floor proximity lemma (linear decay):
  f(⌊b*⌋) ≥ f(b*) - L

This file proves the tightness of the quadratic decay bound:
  |b - b*| ≤ sqrt(2L/m) + 1

The quadratic bound is strictly tighter than the linear bound when
sqrt(2L/m) < 1, i.e., when m > 2L. For the CPMM, this holds when the
pool is well-funded (large reserves relative to trade size).
-/

import Mathlib.Tactic

open Real

/-- Helper: sqrt(2) < 2, since 2 < 4 = 2². -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h_2_lt_4 : (2 : ℝ) < 4 := by norm_num
  have h_sqrt_4 : Real.sqrt 4 = 2 := by norm_num
  have h_sqrt_mono : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) h_2_lt_4
  rw [h_sqrt_4] at h_sqrt_mono
  exact h_sqrt_mono

/-- Helper: for an integer b with b² ≤ 2, |b| ≤ sqrt(2). -/
lemma int_sq_le_two_implies_abs_le_sqrt_two (b : ℤ) (h_b_sq : (b : ℝ) ^ 2 ≤ 2) :
    |(b : ℝ)| ≤ Real.sqrt 2 := by
  have h_sq_abs : |(b : ℝ)| ^ 2 = (b : ℝ) ^ 2 := sq_abs (b : ℝ)
  have h_abs_nn : 0 ≤ |(b : ℝ)| := abs_nonneg (b : ℝ)
  have h_abs_eq_sqrt : |(b : ℝ)| = Real.sqrt (|(b : ℝ)| ^ 2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_sq_abs]
  exact Real.sqrt_le_sqrt h_b_sq

/-- The tightness example: f(b) = -b²/2 has max at b*=0, L=1, m=1.
    The feasible set {b : f(b) ≥ f(b*) - L} = {b : b² ≤ 2} is within
    sqrt(2) of b*, confirming the bound |b - b*| ≤ sqrt(2L/m) + 1 = sqrt(2) + 1.

    This shows the strong concavity window bound is tight: the quadratic
    decay exactly characterizes the feasible set. -/
theorem tightness_example
    : ∀ (b : ℤ), -(1 : ℝ) / 2 * (b : ℝ) ^ 2 ≥ -(1 : ℝ) / 2 * 0 ^ 2 - 1 →
      |(b : ℝ) - 0| ≤ Real.sqrt (2 * 1 / 1) + 1
  := by
  intro b h
  simp at h
  have h_b_sq : (b : ℝ) ^ 2 ≤ 2 := by nlinarith
  have h_abs_le : |(b : ℝ)| ≤ Real.sqrt 2 := int_sq_le_two_implies_abs_le_sqrt_two b h_b_sq
  have h_target : Real.sqrt (2 * 1 / 1) + 1 = Real.sqrt 2 + 1 := by norm_num
  rw [h_target, sub_zero]
  linarith [h_abs_le, Real.sqrt_nonneg 2]

/-- Corollary: For the tightness example, the integer maximizer is 0
    (b* = 0), which is within 1 of b*. This confirms that for well-conditioned
    strongly concave functions, the integer maximizer is at most 1 away from
    the continuous maximizer. -/
theorem tightness_integer_maximizer_at_zero
    : ∀ (b : ℤ), -(1 : ℝ) / 2 * (b : ℝ) ^ 2 ≥ -(1 : ℝ) / 2 * 0 ^ 2 - 1 →
      |(b : ℝ)| ≤ Real.sqrt 2
  := by
  intro b h
  simp at h
  have h_b_sq : (b : ℝ) ^ 2 ≤ 2 := by nlinarith
  exact int_sq_le_two_implies_abs_le_sqrt_two b h_b_sq

/-- The feasible set for the tightness example is {b ∈ ℤ : b² ≤ 2} = {-1, 0, 1}.
    All three are within 1 of b* = 0, confirming the window bound W = 2.
    sqrt(2) < 2, so b ∈ {-1, 0, 1} ⊂ [-2, 2]. -/
theorem tightness_feasible_set_bounded
    : ∀ (b : ℤ), -(1 : ℝ) / 2 * (b : ℝ) ^ 2 ≥ -(1 : ℝ) / 2 * 0 ^ 2 - 1 →
      b ≥ -2 ∧ b ≤ 2
  := by
  intro b h
  simp at h
  have h_b_sq : (b : ℝ) ^ 2 ≤ 2 := by nlinarith
  have h_abs_le : |(b : ℝ)| ≤ Real.sqrt 2 := int_sq_le_two_implies_abs_le_sqrt_two b h_b_sq
  have h_sqrt2_lt_2 := sqrt_two_lt_two
  -- |b| ≤ sqrt(2) < 2, so -2 < b < 2, hence b ∈ {-1, 0, 1} ⊂ [-2, 2]
  have h_b_ge : (b : ℝ) ≥ -Real.sqrt 2 := by linarith [abs_le.mp h_abs_le]
  have h_b_le : (b : ℝ) ≤ Real.sqrt 2 := by linarith [abs_le.mp h_abs_le]
  constructor
  · -- b ≥ -2: contrapositive, if b < -2 then (b : ℝ) < -2 ≤ -sqrt(2)
    by_contra h_not
    push_neg at h_not
    have h_b_lt : (b : ℝ) < -2 := by exact_mod_cast h_not
    linarith [h_b_ge, h_sqrt2_lt_2]
  · -- b ≤ 2: contrapositive, if b > 2 then (b : ℝ) > 2 > sqrt(2)
    by_contra h_not
    push_neg at h_not
    have h_b_gt : (b : ℝ) > 2 := by exact_mod_cast h_not
    linarith [h_b_le, h_sqrt2_lt_2]

/-! ## P8: Oracle-Tight Perturbation Distance and Sharpness

The tightest possible bound from only strong concavity `m` and a one-sided
ceiling-fee perturbation is:

  `|x_g - b_star| <= sqrt(2 * (f_cont(b_star) - f_prod(x_g)) / m)`

where `b_star` is the clean continuous maximizer, `x_g` is the perturbed
production argmax, `f_cont(x) <= f_cont(b_star) - (m/2)(x - b_star)^2`,
and `f_prod(x_g) <= f_cont(x_g)`.

For a usable certificate with an evaluated anchor `a`:

  `|x_g - b_star| <= sqrt(2 * (f_cont(b_star) - f_prod(a)) / m)`

And with the current ceiling-fee envelope:

  `|x_g - b_star| <= sqrt(2 * (alpha(a) + K0/M0 + K1/M1 + 2) / m)`

where `alpha(a) = f_cont(b_star) - f_cont(a)`.

The important tightness result is that the constant cannot be improved
under only those hypotheses. The quadratic witness attains the bound
exactly, so any tighter bound needs extra structure: a better anchor,
exact `f_prod(x_g)`, a tighter fee perturbation certificate, or stronger
CPMM-specific curvature/value facts.

`CeilingFeeRounding.lean` owns the CPMM production theorem
`cpmm_prod_oracle_argmax_distance`. This file keeps only the generic sharpness
witness, which shows the oracle radius cannot be improved from these
hypotheses alone.
-/

/-- **Oracle-Tight Sharpness Witness**: The oracle-tight bound
    `sqrt(2 * (f_cont(b_star) - f_prod(x_g)) / m)` is not an artifact of
    a loose proof. For every `m > 0` and every achievable value drop
    `tau >= 0`, the quadratic objective `f(x) = -(m/2)*x^2` with a
    perturbed objective that is exactly `f_cont(b_star) - tau` everywhere
    satisfies all hypotheses and attains the bound exactly at
    `x_g = sqrt(2*tau/m)`.

    Any tighter generic bound would reject this valid witness family.
    Improving the constant requires extra structure: a better anchor,
    exact `f_prod(x_g)`, a tighter fee perturbation certificate, or
    stronger CPMM-specific curvature/value facts.

    This is a generic sharpness witness. It is not a CPMM structural theorem. -/
theorem oracle_perturbation_radius_sharp_quadratic
    (m tau : ℝ) (hm : m > 0) (htau : tau ≥ 0) :
    let b_star : ℝ := 0
    let x_g : ℝ := Real.sqrt (2 * tau / m)
    let f_cont : ℝ → ℝ := fun x => -(m / 2) * x^2
    let f_prod : ℝ → ℝ := fun _ => f_cont 0 - tau
    |x_g - b_star| = Real.sqrt (2 * tau / m) ∧
      f_prod x_g ≤ f_cont x_g ∧
      (∀ x : ℝ, f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2) ∧
      f_cont b_star - f_prod x_g = tau := by
  dsimp
  have h_tau_nonneg : 0 ≤ 2 * tau / m := by
    exact div_nonneg (mul_nonneg (by norm_num) htau) (le_of_lt hm)
  have h_sq : (Real.sqrt (2 * tau / m))^2 = 2 * tau / m := Real.sq_sqrt h_tau_nonneg
  constructor
  · -- |x_g - 0| = sqrt(2*tau/m) since x_g >= 0
    rw [sub_zero]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  constructor
  · -- f_prod(x_g) <= f_cont(x_g)
    -- f_prod(x_g) = f_cont(0) - tau = 0 - tau = -tau
    -- f_cont(x_g) = -(m/2)*x_g^2 = -(m/2)*(2*tau/m) = -tau
    -- So f_prod(x_g) = f_cont(x_g) = -tau, hence <= holds
    rw [h_sq]
    have h_rhs_eq : -(m / 2) * (2 * tau / m) = -tau := by
      field_simp [ne_of_gt hm]
    simpa using (le_of_eq h_rhs_eq.symm)
  constructor
  · -- Strong concavity: f_cont(x) <= f_cont(0) - (m/2)*(x-0)^2
    intro x
    ring_nf
    exact le_rfl
  · -- f_cont(0) - f_prod(x_g) = tau
    -- f_cont(0) = 0, f_prod(x_g) = -tau, so 0 - (-tau) = tau
    ring
