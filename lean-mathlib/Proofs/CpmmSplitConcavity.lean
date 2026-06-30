/-
# CPMM Split Function: Negative Second Forward Difference (Continuous)

This file proves that the continuous CPMM split output function has a
strictly negative second forward difference under valid-domain hypotheses.

## Theorem (Proven Here)

The CPMM exact-in output function (continuous, no floor rounding) is:
  `out(x) = K * x / (M + x)`

where K = R_out, M = R_in, x = c * a (effective input after fee).

The split function is:
  `F(a) = out_0(c0 * a) + out_1(c1 * (D - a))`

The checked theorem `splitFunctionCont_concave` proves:
  `F(a+2h) - 2*F(a+h) + F(a) < 0`
for all `a, h > 0` satisfying the valid-domain hypotheses
(positive reserves, positive effective input, non-negative remainder).

## Key Algebraic Identity

For `f(x) = K * x / (M + x)` with `K, M > 0`:

  `Δ²f = f(x+2h) - 2*f(x+h) + f(x) = -2*K*M*h² / ((M+x+h)*(M+x)*(M+x+2h))`

This is strictly negative when `K, M > 0`, `h > 0`, `M + x > 0`.

## Scope and Non-Claims

- This proves the second forward difference is negative (continuous, no
  floor rounding, under valid-domain hypotheses)
- This does NOT prove maximum existence, uniqueness on the closed interval,
  or an algorithm theorem (ternary search correctness)
- The discrete (floor-rounded) version is NOT universally discretely concave
  (empirically verified: floor rounding causes local non-concavities)
- The connection to ternary search (unimodality, narrowing) is in
  TernarySearchExactness.lean and TernarySearchAlgorithm.lean, which prove
  their own one-step properties under their own hypotheses

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/CpmmSplitConcavity.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic

/-- The CPMM output function (continuous, no floor rounding).
    `f(x) = K * x / (M + x)` where K = R_out, M = R_in, x = c * a. -/
noncomputable def cpmmOutputCont (K M x : ℝ) : ℝ := K * x / (M + x)

/-- The second forward difference of f at x with step h.
    Δ²f = f(x+2h) - 2*f(x+h) + f(x) -/
def secondDiff (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + 2*h) - 2 * f (x + h) + f x

/-- The CPMM split function with effective input scaling.
    F(a) = K0 * (c0 * a) / (M0 + c0 * a) + K1 * (c1 * (D - a)) / (M1 + c1 * (D - a))
    where Ki = R_i_out, Mi = R_i_in, ci = (1 - fee_i). -/
noncomputable def splitFunctionCont
    (K0 M0 c0 K1 M1 c1 D a : ℝ) : ℝ :=
  cpmmOutputCont K0 M0 (c0 * a) + cpmmOutputCont K1 M1 (c1 * (D - a))

/-- **Key Lemma**: Second forward difference of K*x/(M+x).
    For K, M, x, h with K > 0, M > 0, h > 0, M + x > 0:
    Δ²f = -2*K*M*h² / ((M+x+h)*(M+x)*(M+x+2h))

    Proof: Use the identity f(x) = K - K*M/(M+x), then:
    Δ²f = -K*M * [1/(M+x+2h) - 2/(M+x+h) + 1/(M+x)]
    The bracket equals -2*h² / ((M+x+h)*(M+x)*(M+x+2h)) by partial fractions. -/
lemma cpmmOutputCont_secondDiff_formula
    (K M x h : ℝ)
    (hK : K > 0) (_hM : M > 0) (hh : h > 0) (hMx : M + x > 0)
    : secondDiff (cpmmOutputCont K M) x h =
      -2 * K * M * h^2 / ((M + x + h) * (M + x) * (M + x + 2*h)) := by
  -- Strategy: substitute f(x) = K - K*M/(M+x), then use field_simp
  -- to clear denominators and ring to verify the polynomial identity.
  unfold secondDiff cpmmOutputCont
  -- Key identity: K * x / (M + x) = K - K * M / (M + x)
  -- Proof: K * x = K * (M + x) - K * M, so K * x / (M + x) = K - K * M / (M + x)
  -- We work with the rewritten form to simplify the algebra.
  have hMxh : M + x + h > 0 := by linarith
  have hMx2h : M + x + 2*h > 0 := by linarith
  have hMx_ne : M + x ≠ 0 := ne_of_gt hMx
  have hMxh_ne : M + x + h ≠ 0 := ne_of_gt hMxh
  have hMx2h_ne : M + x + 2*h ≠ 0 := ne_of_gt hMx2h
  -- Prove the identity for each term
  have h_rewrite : ∀ y : ℝ, M + y ≠ 0 → K * y / (M + y) = K - K * M / (M + y) := by
    intro y hy
    field_simp
    ring
  -- Rewrite the three terms in the second difference
  have hMxh_ne' : M + (x + h) ≠ 0 := by
    have : M + (x + h) = M + x + h := by ring
    rw [this]; exact hMxh_ne
  have hMx2h_ne' : M + (x + 2*h) ≠ 0 := by
    have : M + (x + 2*h) = M + x + 2*h := by ring
    rw [this]; exact hMx2h_ne
  rw [h_rewrite _ hMx2h_ne', h_rewrite _ hMxh_ne', h_rewrite _ hMx_ne]
  -- Now we need to show:
  -- (K - KM/(M+x+2h)) - 2*(K - KM/(M+x+h)) + (K - KM/(M+x))
  -- = -2*K*M*h² / ((M+x+h)*(M+x)*(M+x+2h))
  -- The K terms cancel: K - 2K + K = 0
  -- So we need: -KM/(M+x+2h) + 2KM/(M+x+h) - KM/(M+x)
  --            = -2*K*M*h² / ((M+x+h)*(M+x)*(M+x+2h))
  -- Factor out -KM: -KM * [1/(M+x+2h) - 2/(M+x+h) + 1/(M+x)]
  -- Need: [1/(M+x+2h) - 2/(M+x+h) + 1/(M+x)] = 2*h² / ((M+x+h)*(M+x)*(M+x+2h))
  have h_prod_ne : (M + x + h) * (M + x) * (M + x + 2*h) ≠ 0 := by
    have h_p1 : (M + x + h) * (M + x) ≠ 0 := mul_ne_zero hMxh_ne hMx_ne
    exact mul_ne_zero h_p1 hMx2h_ne
  -- Clear all denominators with field_simp, then verify with ring
  field_simp
  ring

/-- The second forward difference of the CPMM output is strictly negative. -/
theorem cpmmOutputCont_secondDiff_neg
    (K M x h : ℝ)
    (hK : K > 0) (hM : M > 0) (hh : h > 0) (hMx : M + x > 0)
    : secondDiff (cpmmOutputCont K M) x h < 0 := by
  rw [cpmmOutputCont_secondDiff_formula K M x h hK hM hh hMx]
  have hMxh : M + x + h > 0 := by linarith
  have hMx2h : M + x + 2*h > 0 := by linarith
  have h_h2_pos : h^2 > 0 := pow_pos hh 2
  have h_KM_pos : K * M > 0 := mul_pos hK hM
  have h_num_pos : 2 * K * M * h^2 > 0 := by
    have h_2KM_pos : 2 * (K * M) > 0 := by linarith
    have : 2 * (K * M) * h^2 > 0 := mul_pos h_2KM_pos h_h2_pos
    linarith
  have h_denom_pos : (M + x + h) * (M + x) * (M + x + 2*h) > 0 := by
    have h_p1 : (M + x + h) * (M + x) > 0 := mul_pos hMxh hMx
    exact mul_pos h_p1 hMx2h
  -- -2*K*M*h^2 / denom < 0 because numerator < 0 and denominator > 0
  have h_neg_num : -2 * K * M * h^2 < 0 := by linarith
  exact div_neg_of_neg_of_pos h_neg_num h_denom_pos

/-- **Main Theorem**: The CPMM split function has a strictly negative second
    forward difference under valid-domain hypotheses.

    The second forward difference is strictly negative for all valid parameters.
    This proves the function is strictly concave (in the second-difference sense).
    It does NOT prove maximum existence, uniqueness, or ternary search correctness
    (those require additional theorems in other files).

    Parameters:
    - K0, K1: pool output reserves (R_out) > 0
    - M0, M1: pool input reserves (R_in) > 0
    - c0, c1: effective input coefficients (1 - fee) > 0
    - D: total input > 0
    - a: split point, 0 < a < D
    - h: step size > 0
    - D - a - 2*h ≥ 0: ensures pool 1's input is non-negative at all evaluation points -/
theorem splitFunctionCont_concave
    (K0 M0 c0 K1 M1 c1 D a h : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (_hD : D > 0) (_ha : a > 0) (_hDa : D - a > 0) (hh : h > 0)
    (hDa2h : D - a - 2*h ≥ 0)
    (h_denom0 : M0 + c0 * a > 0)
    (_h_denom1 : M1 + c1 * (D - a) > 0)
    : secondDiff (splitFunctionCont K0 M0 c0 K1 M1 c1 D) a h < 0 := by
  -- F(a) = f_0(c0*a) + f_1(c1*(D-a))
  -- Δ²F = Δ²[f_0(c0*a)] + Δ²[f_1(c1*(D-a))]
  --
  -- Pool 0: secondDiff (cpmmOutputCont K0 M0) (c0*a) (c0*h) < 0
  -- Pool 1: secondDiff (cpmmOutputCont K1 M1) (c1*(D-a-2h)) (c1*h) < 0
  --         (because g(a) = f_1(c1*(D-a)), Δ²g = secondDiff f_1 (c1*(D-a-2h)) (c1*h))

  -- Pool 0 second difference
  have h_pool0 : secondDiff (cpmmOutputCont K0 M0) (c0 * a) (c0 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK0
    · exact hM0
    · exact mul_pos hc0 hh
    · exact h_denom0

  -- Pool 1 second difference
  have h_c1_nn : c1 ≥ 0 := le_of_lt hc1
  have h_x1_nn : c1 * (D - a - 2*h) ≥ 0 := mul_nonneg h_c1_nn hDa2h
  have h_denom1_base : M1 + c1 * (D - a - 2*h) > 0 := by
    have : c1 * (D - a - 2*h) ≤ c1 * (D - a) := mul_le_mul_of_nonneg_left (by linarith) h_c1_nn
    linarith
  have h_pool1 : secondDiff (cpmmOutputCont K1 M1) (c1 * (D - a - 2*h)) (c1 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK1
    · exact hM1
    · exact mul_pos hc1 hh
    · exact h_denom1_base

  -- Show the total second difference equals the sum of the two pool second differences
  have h_eq : secondDiff (cpmmOutputCont K0 M0) (c0 * a) (c0 * h)
              + secondDiff (cpmmOutputCont K1 M1) (c1 * (D - a - 2*h)) (c1 * h)
              = secondDiff (splitFunctionCont K0 M0 c0 K1 M1 c1 D) a h := by
    unfold secondDiff splitFunctionCont cpmmOutputCont
    ring

  -- h_pool0 < 0 and h_pool1 < 0, so their sum < 0
  -- By h_eq, the sum equals the goal expression
  rw [← h_eq]
  exact add_neg h_pool0 h_pool1

/-! ## Strong Concavity Lower Bound From Pool Parameters

For the CPMM split function `F(a) = f0(c0*a) + f1(c1*(D-a))`, the second
derivative is `F''(a) = -T0(a) - T1(a)` where:
  `T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3`  (decreasing in a)
  `T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3`  (increasing in a)

The strong concavity parameter `m = inf_a |F''(a)|` satisfies:
  `m >= T0(D) + T1(0) = 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3`

This removes the external hypothesis on `m`: the window bound
`sqrt(2*eps/m)` is now fully determined by pool parameters.

Key lemma: `inf(f+g) >= inf(f) + inf(g)` for non-negative functions.
Applied here: T0(a) >= T0(D) and T1(a) >= T1(0) for a in [0, D].
-/

/-- Helper: for positive x, y with `x <= y` and `c >= 0`, `c/x^3 >= c/y^3`.
    The reciprocal cube is decreasing on positive reals. -/
lemma inv_cube_antitone_mul (x y c : ℝ) (hx : 0 < x) (hy : 0 < y) (hc : c ≥ 0)
    (hxy : x ≤ y) : c / x^3 ≥ c / y^3 := by
  have hx3 : 0 < x^3 := pow_pos hx 3
  have hy3 : 0 < y^3 := pow_pos hy 3
  have hx3_le_hy3 : x^3 ≤ y^3 := by
    have h1 : x^2 ≤ y^2 := by nlinarith [sq_nonneg (y - x), hxy]
    nlinarith [sq_nonneg (y - x), hxy, h1]
  -- c/y^3 <= c/x^3 since x^3 <= y^3
  have h_key : c / y^3 ≤ c / x^3 := by
    rw [div_le_div_iff₀ hy3 hx3]
    exact mul_le_mul_of_nonneg_left hx3_le_hy3 hc
  exact h_key

/-- **T0 monotonicity**: `T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3` is decreasing in a.
    For `a <= D`, `T0(a) >= T0(D)`. -/
lemma T0_decreasing_bound
    (K0 M0 c0 a D : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    : 2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3 ≥
      2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 := by
  have hM0ca : 0 < M0 + c0 * a := by nlinarith
  have hM0cD : 0 < M0 + c0 * D := by nlinarith
  have h_ca_le_cD : c0 * a ≤ c0 * D :=
    mul_le_mul_of_nonneg_left ha_le_D hc0
  have h_denom_le : M0 + c0 * a ≤ M0 + c0 * D := by linarith
  have h_coeff_nn : 0 ≤ 2 * c0^2 * K0 * M0 := by
    have h_c0sq : 0 ≤ c0^2 := sq_nonneg c0
    have h_2 : (0 : ℝ) ≤ 2 := by norm_num
    have h_2c0sq : 0 ≤ 2 * c0^2 := mul_nonneg h_2 h_c0sq
    have h_2c0sqK0 : 0 ≤ 2 * c0^2 * K0 := mul_nonneg h_2c0sq (le_of_lt hK0)
    exact mul_nonneg h_2c0sqK0 (le_of_lt hM0)
  exact inv_cube_antitone_mul (M0 + c0 * a) (M0 + c0 * D) (2 * c0^2 * K0 * M0)
    hM0ca hM0cD h_coeff_nn h_denom_le

/-- **T1 monotonicity**: `T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3` is increasing in a.
    For `a >= 0`, `T1(a) >= T1(0)` (since `D-a <= D`). -/
lemma T1_increasing_bound
    (K1 M1 c1 a D : ℝ)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    : 2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3 ≥
      2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3 := by
  have h_Da_le_D : D - a ≤ D := by nlinarith
  have hM1cDa : 0 < M1 + c1 * (D - a) := by nlinarith
  have hM1cD : 0 < M1 + c1 * D := by nlinarith
  have h_cDa_le_cD : c1 * (D - a) ≤ c1 * D :=
    mul_le_mul_of_nonneg_left h_Da_le_D hc1
  have h_denom_le : M1 + c1 * (D - a) ≤ M1 + c1 * D := by linarith
  have h_coeff_nn : 0 ≤ 2 * c1^2 * K1 * M1 := by
    have h_c1sq : 0 ≤ c1^2 := sq_nonneg c1
    have h_2 : (0 : ℝ) ≤ 2 := by norm_num
    have h_2c1sq : 0 ≤ 2 * c1^2 := mul_nonneg h_2 h_c1sq
    have h_2c1sqK1 : 0 ≤ 2 * c1^2 * K1 := mul_nonneg h_2c1sq (le_of_lt hK1)
    exact mul_nonneg h_2c1sqK1 (le_of_lt hM1)
  exact inv_cube_antitone_mul (M1 + c1 * (D - a)) (M1 + c1 * D) (2 * c1^2 * K1 * M1)
    hM1cDa hM1cD h_coeff_nn h_denom_le

/-- **Strong Concavity Lower Bound**: For the CPMM split function
    `F(a) = f0(c0*a) + f1(c1*(D-a))`, the strong concavity parameter m
    satisfies:

    `m >= 2*c0^2*K0*M0/(M0+c0*D)^3 + 2*c1^2*K1*M1/(M1+c1*D)^3`

    This is derived from:
    - `|F''(a)| = T0(a) + T1(a)` (second derivative formula, external)
    - `T0(a) >= T0(D)` for `a in [0, D]` (T0 decreasing, proven here)
    - `T1(a) >= T1(0)` for `a in [0, D]` (T1 increasing, proven here)

    Non-claims:
    - The second derivative formula `F''(a) = -T0(a) - T1(a)` is external.
    - This is a lower bound on m, not the exact m.
    - The bound degenerates when `D >> M` (m -> 0), which is correct.
    - The exact m is `inf(T0+T1) >= inf T0 + inf T1`. -/
theorem strong_concavity_lower_bound
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (_hD : D ≥ 0) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    : 2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3 ≥
      2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3 := by
  have h0 := T0_decreasing_bound K0 M0 c0 a D hK0 hM0 hc0 ha_nn ha_le_D
  have h1 := T1_increasing_bound K1 M1 c1 a D hK1 hM1 hc1 ha_nn ha_le_D
  linarith

/-- **Witness**: Concrete case showing the lower bound is non-vacuous and
    strictly positive. K0=1000, M0=1000, c0=0.99, K1=2000, M1=1000,
    c1=0.99, D=100, a=50. -/
theorem witness_strong_concavity_bound :
    (0 : ℝ) < 2 * (0.99)^2 * 1000 * 1000 / (1000 + 0.99 * 100)^3 +
            2 * (0.99)^2 * 2000 * 1000 / (1000 + 0.99 * 100)^3 := by
  norm_num
