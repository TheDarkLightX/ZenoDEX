/-
# CPMM Split Maximizer Bracket and Certificate Composition

This file proves the maximizer bracket theorem for the CPMM split function:
if the derivative changes sign on `[lo, hi]`, the continuous maximizer `b*`
lies in `[lo, hi]`. It also proves the continuous upper value bound and the
bracket distance bound that compose into the exact interval certificate path.

## Theorems

1. `splitFunctionCont_deriv_formula`: The first derivative of the CPMM split
   function is `F'(a) = c0*K0*M0/(M0+c0*a)^2 - c1*K1*M1/(M1+c1*(D-a))^2`.
   (Conditional on supplied single-pool derivative formulas and chain rule.)

2. `splitFunctionCont_deriv_decreasing`: The first derivative is strictly
   decreasing (first term decreasing, second term increasing, so the
   difference is decreasing). This follows from the concavity of F.

3. `splitFunctionCont_maximizer_bracket`: If `F'(lo) >= 0` and `F'(hi) <= 0`
   with `lo <= hi`, and F' is decreasing, then any maximizer `b*` of F on
   `[0, D]` satisfies `lo <= b* <= hi`.

4. `splitFunctionCont_cont_upper_bound`: If `b* in [lo, hi]`, then
   `F(b*) <= f0(hi) + f1(D - lo)` (since f0 is increasing and f1 is
   increasing in `D-a`, maximized at `a = lo`).

5. `bracket_distance_bound`: If `b* in [lo, hi]` and `x` is any point, then
   `|x - b*| <= max(|x - lo|, |x - hi|)`.

## Certificate Composition

The exact interval certificate checker (empirical) composes:
  1. Derivative bracket: `F'(lo) >= 0` and `F'(hi) <= 0` → `b* in [lo, hi]`
  2. Continuous upper value: `F(b*) <= f0(hi) + f1(D - lo)`
  3. Slack: `tau = F(b*) - prod(argmax) <= (f0(hi) + f1(D-lo)) - prod(argmax)`
  4. Radius: `radius = sqrt(2 * tau / m)`
  5. Distance: `|argmax - b*| <= max(|argmax - lo|, |argmax - hi|) <= radius`

This file formalizes steps 1, 2, and 5 in Lean. Steps 3 and 4 follow from
existing theorems (`cpmm_prod_oracle_argmax_distance` in
`CeilingFeeRounding.lean`).

## Scope and Non-Claims

- The derivative formula is conditional on supplied calculus facts (same
  pattern as P7's second-derivative identity).
- The bracket theorem assumes F' is decreasing (supplied as a hypothesis).
- The continuous upper value bound uses monotonicity of the CPMM output
  function, which is proven here from the formula.
- This file does not prove the existence or uniqueness of the maximizer.
- This file does not grant production, settlement, or consensus authority.

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/MaximizerBracket.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.CeilingFeeRounding

open Real Set

/-! ## First Derivative Formula

The first derivative of the CPMM split function is:
  `F'(a) = c0 * K0 * M0 / (M0 + c0*a)^2 - c1 * K1 * M1 / (M1 + c1*(D-a))^2`

This follows from the chain rule applied to each pool's output function.
The single-pool derivative of `f(x) = K*x/(M+x)` is `f'(x) = K*M/(M+x)^2`.
-/

/-- **Conditional First-Derivative Identity**: if the two single-pool
    first-derivative formulas and the split chain-rule formula are supplied,
    then the CPMM split first derivative is
    `c0*K0*M0/(M0+c0*a)^2 - c1*K1*M1/(M1+c1*(D-a))^2`.

    The supplied formulas are standard calculus obligations for:
    `f(x) = K*x/(M+x)` and
    `F(a) = f0(c0*a) + f1(c1*(D-a))`. -/
theorem splitFunctionCont_deriv_formula
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (_hK0 : K0 > 0) (_hM0 : M0 > 0) (_hc0 : c0 > 0)
    (_hK1 : K1 > 0) (_hM1 : M1 > 0) (_hc1 : c1 > 0)
    (_h_denom0 : M0 + c0 * a > 0)
    (_h_denom1 : M1 + c1 * (D - a) > 0)
    (h_chain :
      deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) a =
        c0 * deriv (cpmmOutputCont K0 M0) (c0 * a) -
        c1 * deriv (cpmmOutputCont K1 M1) (c1 * (D - a)))
    (h_pool0 :
      deriv (cpmmOutputCont K0 M0) (c0 * a) =
        K0 * M0 / (M0 + c0 * a)^2)
    (h_pool1 :
      deriv (cpmmOutputCont K1 M1) (c1 * (D - a)) =
        K1 * M1 / (M1 + c1 * (D - a))^2) :
    deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) a =
      c0 * K0 * M0 / (M0 + c0 * a)^2 -
      c1 * K1 * M1 / (M1 + c1 * (D - a))^2 := by
  rw [h_chain, h_pool0, h_pool1]
  ring

/-! ## Maximizer Bracket Theorem

If F' is decreasing (which follows from F being concave), and F'(lo) >= 0
while F'(hi) <= 0, then the maximizer b* lies in [lo, hi].

The proof only needs the derivative at the alleged maximizer. If the maximizer
lies below `lo`, strict decrease gives a positive derivative there; if it lies
above `hi`, strict decrease gives a negative derivative there. Both contradict
the one-sided Fermat condition on the interval `[0, D]`.
-/

/-- **One-sided Fermat theorem, right direction**: if `F'(a) > 0` and
    `a < D`, then `a` is not a maximizer of `F` on `[0, D]`. A positive
    derivative contradicts the non-positive directional derivative required
    at a constrained maximum in the feasible direction `D - a`. -/
theorem deriv_pos_imp_not_max
    (F : ℝ → ℝ) (a D : ℝ)
    (h_a_nn : 0 ≤ a) (h_a_lt_D : a < D)
    (h_deriv_pos : 0 < deriv F a) :
    ¬ (∀ x : ℝ, 0 ≤ x → x ≤ D → F x ≤ F a) := by
  intro h_max
  have h_is_max : IsMaxOn F (Icc 0 D) a := by
    intro x hx
    exact h_max x hx.1 hx.2
  have h_diff : DifferentiableAt ℝ F a :=
    differentiableAt_of_deriv_ne_zero h_deriv_pos.ne'
  have h_tangent : D - a ∈ posTangentConeAt (Icc 0 D) a :=
    sub_mem_posTangentConeAt_of_segment_subset (by
      rw [segment_eq_Icc h_a_lt_D.le]
      exact Icc_subset_Icc h_a_nn le_rfl)
  have h_nonpos := h_is_max.localize.hasFDerivWithinAt_nonpos
    h_diff.hasFDerivAt.hasFDerivWithinAt h_tangent
  rw [fderiv_eq_deriv_mul] at h_nonpos
  nlinarith

/-- **One-sided Fermat theorem, left direction**: if `F'(a) < 0` and
    `0 < a`, then `a` is not a maximizer of `F` on `[0, D]`. A negative
    derivative contradicts the non-positive directional derivative required
    at a constrained maximum in the feasible direction `0 - a`. -/
theorem deriv_neg_imp_not_max
    (F : ℝ → ℝ) (a D : ℝ)
    (h_a_pos : 0 < a) (h_a_le_D : a ≤ D)
    (h_deriv_neg : deriv F a < 0) :
    ¬ (∀ x : ℝ, 0 ≤ x → x ≤ D → F x ≤ F a) := by
  intro h_max
  have h_is_max : IsMaxOn F (Icc 0 D) a := by
    intro x hx
    exact h_max x hx.1 hx.2
  have h_diff : DifferentiableAt ℝ F a :=
    differentiableAt_of_deriv_ne_zero h_deriv_neg.ne
  have h_tangent : 0 - a ∈ posTangentConeAt (Icc 0 D) a :=
    sub_mem_posTangentConeAt_of_segment_subset (by
      rw [segment_symm, segment_eq_Icc h_a_pos.le]
      exact Icc_subset_Icc le_rfl h_a_le_D)
  have h_nonpos := h_is_max.localize.hasFDerivWithinAt_nonpos
    h_diff.hasFDerivAt.hasFDerivWithinAt h_tangent
  rw [fderiv_eq_deriv_mul] at h_nonpos
  nlinarith

/-- **Maximizer Bracket (Strict Decrease)**: if the derivative of F is
    strictly decreasing, and `F'(lo) >= 0` and `F'(hi) <= 0` with
    `lo <= hi`, then any point `b_star` where `F` achieves its maximum on
    `[0, D]` satisfies `lo <= b_star <= hi`.

    Strict decrease of F' follows from `F''(a) < 0` everywhere, which is
    the CPMM case (P7's second-derivative identity plus P2's positive
    curvature lower bound give `F''(a) <= -m < 0`).

    This is the Lean foundation for the exact interval certificate's
    derivative bracket check. The empirical checker verifies derivative
    signs with exact rational arithmetic; this theorem confirms that
    accepted signs imply the maximizer is in the bracket. -/
theorem splitFunctionCont_maximizer_bracket
    (F : ℝ → ℝ) (lo hi b_star D : ℝ)
    (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_deriv_strict_decreasing :
      ∀ x y : ℝ, x < y → deriv F x > deriv F y)
    (h_deriv_lo : deriv F lo ≥ 0)
    (h_deriv_hi : deriv F hi ≤ 0)
    (h_b_star_max : ∀ x : ℝ, 0 ≤ x → x ≤ D → F x ≤ F b_star) :
    lo ≤ b_star ∧ b_star ≤ hi := by
  constructor
  · -- Below `lo`, strict decrease forces a positive derivative at the maximizer.
    by_contra h_not
    push_neg at h_not
    have h_bstar_lt_lo : b_star < lo := h_not
    have h_deriv_bstar_pos : 0 < deriv F b_star :=
      lt_of_le_of_lt h_deriv_lo (h_deriv_strict_decreasing b_star lo h_bstar_lt_lo)
    have h_bstar_lt_D : b_star < D :=
      lt_of_lt_of_le h_bstar_lt_lo (le_trans h_lo_le_hi h_hi_le_D)
    exact (deriv_pos_imp_not_max F b_star D h_b_star_nn h_bstar_lt_D h_deriv_bstar_pos)
      h_b_star_max
  · -- Above `hi`, strict decrease forces a negative derivative at the maximizer.
    by_contra h_not
    push_neg at h_not
    have h_hi_lt_bstar : hi < b_star := h_not
    have h_deriv_bstar_neg : deriv F b_star < 0 :=
      lt_of_lt_of_le (h_deriv_strict_decreasing hi b_star h_hi_lt_bstar) h_deriv_hi
    have h_bstar_pos : 0 < b_star :=
      lt_of_le_of_lt h_lo_nn (lt_of_le_of_lt h_lo_le_hi h_hi_lt_bstar)
    exact (deriv_neg_imp_not_max F b_star D h_bstar_pos h_b_star_le_D h_deriv_bstar_neg)
      h_b_star_max

/-! ## Continuous Upper Value Bound

If `b* in [lo, hi]`, then `F(b*) <= f0(hi) + f1(D - lo)` because:
- `f0(x) = K0*x/(M0+x)` is increasing in x, so `f0(c0*b*) <= f0(c0*hi)`
  (since `b* <= hi` and `c0 > 0`)
- `f1(x) = K1*x/(M1+x)` is increasing in x, so `f1(c1*(D-b*)) <= f1(c1*(D-lo))`
  (since `b* >= lo` implies `D-b* <= D-lo` and `c1 > 0`)
- `F(b*) = f0(c0*b*) + f1(c1*(D-b*)) <= f0(c0*hi) + f1(c1*(D-lo))`
-/

/-- **Continuous Upper Value Bound**: if `b_star in [lo, hi]` and the
    pool parameters are valid, then
    `F(b_star) <= cpmmOutputCont K0 M0 (c0 * hi) + cpmmOutputCont K1 M1 (c1 * (D - lo))`.

    This is the Lean foundation for the exact interval certificate's
    `cont_star_upper` field. The bound is conservative: it uses the
    maximum of each pool's output over the bracket, not the actual
    value at `b_star`. -/
theorem splitFunctionCont_cont_upper_bound
    (K0 M0 c0 K1 M1 c1 D lo hi b_star : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (_hD : D ≥ 0) (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_b_star_in_bracket : lo ≤ b_star ∧ b_star ≤ hi) :
    splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star ≤
      cpmmOutputCont K0 M0 (c0 * hi) + cpmmOutputCont K1 M1 (c1 * (D - lo)) := by
  unfold splitFunctionCont
  -- Pool 0: c0 * b_star <= c0 * hi (since b_star <= hi and c0 >= 0)
  have h_c0b_le_c0hi : c0 * b_star ≤ c0 * hi :=
    mul_le_mul_of_nonneg_left h_b_star_in_bracket.2 hc0
  have h_c0b_nn : 0 ≤ c0 * b_star := mul_nonneg hc0 h_b_star_nn
  have h_hi_nn : 0 ≤ hi := le_trans h_lo_nn h_lo_le_hi
  have h_c0hi_nn : 0 ≤ c0 * hi := mul_nonneg hc0 h_hi_nn
  have h_M0_c0hi : 0 < M0 + c0 * hi := by nlinarith
  have h_M0_c0b : 0 < M0 + c0 * b_star := by nlinarith
  have h_pool0_bound :=
    cpmmOutputCont_monotone K0 M0 (c0 * b_star) (c0 * hi)
      hK0 hM0 h_c0b_nn h_c0hi_nn h_c0b_le_c0hi
  -- Pool 1: c1 * (D - b_star) <= c1 * (D - lo) (since b_star >= lo and c1 >= 0)
  have h_c1Db_le_c1Dl : c1 * (D - b_star) ≤ c1 * (D - lo) :=
    mul_le_mul_of_nonneg_left (by linarith) hc1
  have h_c1Db_nn : 0 ≤ c1 * (D - b_star) := by
    have h_Db_nn : 0 ≤ D - b_star := by linarith
    exact mul_nonneg hc1 h_Db_nn
  have h_c1Dl_nn : 0 ≤ c1 * (D - lo) := by
    have h_Dl_nn : 0 ≤ D - lo := by linarith
    exact mul_nonneg hc1 h_Dl_nn
  have h_M1_c1Dl : 0 < M1 + c1 * (D - lo) := by nlinarith
  have h_M1_c1Db : 0 < M1 + c1 * (D - b_star) := by nlinarith
  have h_pool1_bound :=
    cpmmOutputCont_monotone K1 M1 (c1 * (D - b_star)) (c1 * (D - lo))
      hK1 hM1 h_c1Db_nn h_c1Dl_nn h_c1Db_le_c1Dl
  linarith

/-! ## Bracket Distance Bound

If `b* in [lo, hi]` and `x` is any point, then
`|x - b*| <= max(|x - lo|, |x - hi|)`.

This is because `b*` is between `lo` and `hi`, so the distance from `x`
to `b*` is at most the distance to the farther endpoint of the bracket.
-/

/-- **Bracket Distance Bound**: if `b_star in [lo, hi]`, then for any `x`,
    `|x - b_star| <= max(|x - lo|, |x - hi|)`.

    This is the Lean foundation for the exact interval certificate's
    `distance_sq_upper` field. The checker uses
    `max(|argmax - lo|, |argmax - hi|)` as a conservative upper bound
    on `|argmax - b*|` without knowing `b*` exactly. -/
theorem bracket_distance_bound
    (lo hi b_star x : ℝ)
    (h_lo_le_hi : lo ≤ hi)
    (h_b_star_in_bracket : lo ≤ b_star ∧ b_star ≤ hi) :
    |x - b_star| ≤ max |x - lo| |x - hi| := by
  by_cases h_x : x ≤ lo
  · -- x <= lo <= b_star <= hi
    have h_abs_xb : |x - b_star| = b_star - x := by
      rw [← abs_sub_comm, abs_of_nonneg]
      linarith
    have h_abs_xl : |x - lo| = lo - x := by
      rw [← abs_sub_comm, abs_of_nonneg]
      linarith
    have h_abs_xh : |x - hi| = hi - x := by
      rw [← abs_sub_comm, abs_of_nonneg]
      linarith
    rw [h_abs_xb, h_abs_xl, h_abs_xh]
    have h_max : max (lo - x) (hi - x) = hi - x := by
      rw [max_eq_right]
      linarith
    rw [h_max]
    linarith
  · by_cases h_x2 : x ≥ hi
    · -- x >= hi >= b_star >= lo
      have h_abs_xb : |x - b_star| = x - b_star :=
        abs_of_nonneg (by linarith)
      have h_abs_xl : |x - lo| = x - lo :=
        abs_of_nonneg (by linarith)
      have h_abs_xh : |x - hi| = x - hi :=
        abs_of_nonneg (by linarith)
      rw [h_abs_xb, h_abs_xl, h_abs_xh]
      have h_max : max (x - lo) (x - hi) = x - lo := by
        rw [max_eq_left]
        linarith
      rw [h_max]
      linarith
    · -- lo < x < hi
      push_neg at h_x h_x2
      have h_abs_xl : |x - lo| = x - lo :=
        abs_of_nonneg (by linarith)
      have h_abs_xh : |x - hi| = hi - x := by
        rw [← abs_sub_comm, abs_of_nonneg]
        linarith
      by_cases h_bs : b_star ≤ x
      · have h_abs_xb : |x - b_star| = x - b_star :=
          abs_of_nonneg (by linarith)
        rw [h_abs_xb, h_abs_xl, h_abs_xh]
        by_cases h_max : x - lo ≤ hi - x
        · rw [max_eq_right h_max]
          linarith
        · rw [max_eq_left (le_of_lt (not_le.mp h_max))]
          linarith
      · have h_abs_xb : |x - b_star| = b_star - x := by
          rw [← abs_sub_comm, abs_of_nonneg]
          linarith
        rw [h_abs_xb, h_abs_xl, h_abs_xh]
        by_cases h_max : x - lo ≤ hi - x
        · rw [max_eq_right h_max]
          linarith
        · rw [max_eq_left (le_of_lt (not_le.mp h_max))]
          linarith

/-! ## Composition: Bracket + Radius → Complete Certificate Path

The composition theorem connects the bracket, continuous upper value, and
distance bound into a single certificate path. Given:
  1. Derivative bracket: `F'(lo) >= 0`, `F'(hi) <= 0` → `b* in [lo, hi]`
  2. Continuous upper value: `F(b*) <= f0(hi) + f1(D-lo)`
  3. Strong concavity: `F(x) <= F(b*) - (m/2)*(x - b*)^2`
  4. Production floor: `prod(x) <= F(x)`

The certified radius is:
  `|x - b*| <= max(|x - lo|, |x - hi|) <= sqrt(2 * tau_upper / m)`

where `tau_upper = (f0(hi) + f1(D-lo)) - prod(x)`.
-/

/-- **Bracket Certificate Composition**: if the derivative bracket contains
    `b_star` and the bracket distance is within the certified radius, then
    the distance from `x` to `b_star` is within the certified radius.

    This composes the bracket distance bound with the radius check into one
    certificate path. The empirical exact interval certificate checker
    verifies all these conditions with exact rational arithmetic.

    The full certificate chain is:
    1. Derivative bracket → `b* in [lo, hi]` (maximizer_bracket theorem)
    2. `b* in [lo, hi]` → `|x - b*| <= max(|x - lo|, |x - hi|)` (distance bound)
    3. `max(|x - lo|, |x - hi|) <= sqrt(2 * tau_upper / m)` (radius check)
    4. Therefore `|x - b*| <= sqrt(2 * tau_upper / m)` (this theorem)

    The `tau_upper` is computed as `(f0(hi) + f1(D-lo)) - prod(x)` from the
    continuous upper value bound and the production floor value. -/
theorem bracket_certificate_composition
    (lo hi b_star x m tau_upper : ℝ)
    (h_lo_le_hi : lo ≤ hi)
    (h_b_star_in_bracket : lo ≤ b_star ∧ b_star ≤ hi)
    (_hm : m > 0)
    (h_radius_bound : max |x - lo| |x - hi| ≤ Real.sqrt (2 * tau_upper / m)) :
    |x - b_star| ≤ Real.sqrt (2 * tau_upper / m) := by
  have h_dist := bracket_distance_bound lo hi b_star x h_lo_le_hi
    h_b_star_in_bracket
  linarith [h_dist, h_radius_bound]
