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

/-! ## Curvature-Term Lower Bound From Pool Parameters

For the CPMM split function `F(a) = f0(c0*a) + f1(c1*(D-a))`, the second
derivative is `F''(a) = -T0(a) - T1(a)` where:
  `T0(a) = 2*c0^2*K0*M0/(M0+c0*a)^3`  (decreasing in a)
  `T1(a) = 2*c1^2*K1*M1/(M1+c1*(D-a))^3`  (increasing in a)

This section proves the arithmetic lower-bound component:
  `T0(a) + T1(a) >= T0(D) + T1(0)`.

Combined with an external second-derivative bridge establishing
`|F''(a)| = T0(a) + T1(a)` on `[0,D]`, this gives a pool-parameter lower
bound for a valid strong-concavity parameter. The second-derivative bridge is
not proved in this file.

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

/-- **Curvature-Term Lower Bound**: For the CPMM split curvature terms
    associated with `F(a) = f0(c0*a) + f1(c1*(D-a))`,

    `T0(a) + T1(a) >= 2*c0^2*K0*M0/(M0+c0*D)^3
                  + 2*c1^2*K1*M1/(M1+c1*D)^3`

    This is derived from:
    - `|F''(a)| = T0(a) + T1(a)` (second derivative formula, external)
    - `T0(a) >= T0(D)` for `a in [0, D]` (T0 decreasing, proven here)
    - `T1(a) >= T1(0)` for `a in [0, D]` (T1 increasing, proven here)

    Non-claims:
    - The second derivative formula `F''(a) = -T0(a) - T1(a)` is external.
    - This is the arithmetic curvature-term bound. A function-level
      strong-concavity parameter still needs the external second-derivative
      identity and the usual calculus bridge.
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

/-- **Interval Curvature-Term Lower Bound**: for any interval
    `lo <= a <= hi` inside `[0,D]`, the split curvature terms satisfy

    `T0(a) + T1(a) >= T0(hi) + T1(lo)`.

    This is the proof-facing bridge for rational interval certificates. A
    runtime checker can cover `[0,D]` by finitely many intervals and compute
    the minimum of these exact endpoint floors. -/
theorem strong_concavity_interval_lower_bound
    (K0 M0 c0 K1 M1 c1 D lo hi a : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hlo_nn : 0 ≤ lo) (hlo_le_a : lo ≤ a) (ha_le_hi : a ≤ hi)
    (hhi_le_D : hi ≤ D) :
    2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3 ≥
    2 * c0^2 * K0 * M0 / (M0 + c0 * hi)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3 := by
  have ha_nn : 0 ≤ a := by linarith
  have h0 := T0_decreasing_bound K0 M0 c0 a hi hK0 hM0 hc0 ha_nn ha_le_hi
  have h_a_sub_lo_nn : 0 ≤ a - lo := by linarith
  have h_a_sub_lo_le : a - lo ≤ D - lo := by linarith
  have h1_shift := T1_increasing_bound
    K1 M1 c1 (a - lo) (D - lo) hK1 hM1 hc1 h_a_sub_lo_nn h_a_sub_lo_le
  have hleft :
      M1 + c1 * ((D - lo) - (a - lo)) = M1 + c1 * (D - a) := by ring
  have hright : M1 + c1 * (D - lo) = M1 + c1 * (D - lo) := by rfl
  have h1 :
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3 ≥
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3 := by
    simpa [hleft, hright] using h1_shift
  linarith

/-- **Interval Floor Refinement Monotonicity**: splitting an interval cannot
    lower the certified interval floor.

    The parent interval `[lo, hi]` has floor `T0(hi)+T1(lo)`. Splitting at
    `mid` gives child floors `T0(mid)+T1(lo)` and `T0(hi)+T1(mid)`. Since
    `T0` decreases and `T1` increases, both child floors are at least the
    parent floor. This is the proof-facing invariant behind adaptive rational
    interval certificates. -/
theorem strong_concavity_interval_floor_refinement
    (K0 M0 c0 K1 M1 c1 D lo mid hi : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hlo_nn : 0 ≤ lo) (hlo_le_mid : lo ≤ mid) (hmid_le_hi : mid ≤ hi)
    (hhi_le_D : hi ≤ D) :
    2 * c0^2 * K0 * M0 / (M0 + c0 * hi)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3 ≤
    2 * c0^2 * K0 * M0 / (M0 + c0 * mid)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3
    ∧
    2 * c0^2 * K0 * M0 / (M0 + c0 * hi)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3 ≤
    2 * c0^2 * K0 * M0 / (M0 + c0 * hi)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * (D - mid))^3 := by
  have hmid_nn : 0 ≤ mid := by linarith
  have h0 := T0_decreasing_bound K0 M0 c0 mid hi hK0 hM0 hc0 hmid_nn hmid_le_hi
  constructor
  · linarith
  · have h_mid_sub_lo_nn : 0 ≤ mid - lo := by linarith
    have h_mid_sub_lo_le : mid - lo ≤ D - lo := by linarith
    have h1_shift := T1_increasing_bound
      K1 M1 c1 (mid - lo) (D - lo) hK1 hM1 hc1 h_mid_sub_lo_nn h_mid_sub_lo_le
    have hleft :
        M1 + c1 * ((D - lo) - (mid - lo)) = M1 + c1 * (D - mid) := by ring
    have h1 :
        2 * c1^2 * K1 * M1 / (M1 + c1 * (D - mid))^3 ≥
        2 * c1^2 * K1 * M1 / (M1 + c1 * (D - lo))^3 := by
      simpa [hleft] using h1_shift
    linarith

/-- **Inverse-Cube Pair Lower Bound**: for positive denominators with fixed
    sum, the sum of inverse cubes is minimized when the denominators are equal.

    This algebraic inequality is the proof kernel for the symmetric-pool exact
    curvature minimizer. The non-negative gap factors as

    `(x-y)^2 * (x^4 + 5*x^3*y + 12*x^2*y^2 + 5*x*y^3 + y^4)`

    over the positive denominator `x^3*y^3*(x+y)^3`. -/
theorem inv_cube_pair_lower_bound
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    16 / (x + y)^3 ≤ 1 / x^3 + 1 / y^3 := by
  have hsum : 0 < x + y := by positivity
  have hden : 0 < x^3 * y^3 * (x + y)^3 := by positivity
  have hgap :
      1 / x^3 + 1 / y^3 - 16 / (x + y)^3 =
        ((x - y)^2 *
          (x^4 + 5*x^3*y + 12*x^2*y^2 + 5*x*y^3 + y^4)) /
        (x^3 * y^3 * (x + y)^3) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hsum]
    ring
  have hpoly : 0 ≤ x^4 + 5*x^3*y + 12*x^2*y^2 + 5*x*y^3 + y^4 := by
    positivity
  have hnum :
      0 ≤ (x - y)^2 *
        (x^4 + 5*x^3*y + 12*x^2*y^2 + 5*x*y^3 + y^4) := by
    exact mul_nonneg (sq_nonneg (x - y)) hpoly
  have hfrac :
      0 ≤
        ((x - y)^2 *
          (x^4 + 5*x^3*y + 12*x^2*y^2 + 5*x*y^3 + y^4)) /
        (x^3 * y^3 * (x + y)^3) :=
    div_nonneg hnum (le_of_lt hden)
  have hdiff : 0 ≤ 1 / x^3 + 1 / y^3 - 16 / (x + y)^3 := by
    rw [hgap]
    exact hfrac
  linarith

/-- **Inverse-Cube Tangent Lower Bound**: the convex kernel `1/t^3` lies
    above its tangent at `t = 1`.

    This is the algebraic proof kernel for the asymmetric stationary curvature
    certificate. The non-negative gap factors as

    `(t-1)^2 * (3*t^2 + 2*t + 1) / t^3`. -/
theorem inv_cube_tangent_lower_bound
    (t : ℝ) (ht : 0 < t) :
    4 - 3 * t ≤ 1 / t^3 := by
  have ht3 : 0 < t^3 := pow_pos ht 3
  have hgap :
      1 / t^3 - (4 - 3 * t) =
        ((t - 1)^2 * (3*t^2 + 2*t + 1)) / t^3 := by
    field_simp [ne_of_gt ht]
    ring
  have hpoly : 0 ≤ 3*t^2 + 2*t + 1 := by
    positivity
  have hnum : 0 ≤ (t - 1)^2 * (3*t^2 + 2*t + 1) := by
    exact mul_nonneg (sq_nonneg (t - 1)) hpoly
  have hfrac : 0 ≤ ((t - 1)^2 * (3*t^2 + 2*t + 1)) / t^3 :=
    div_nonneg hnum (le_of_lt ht3)
  have hdiff : 0 ≤ 1 / t^3 - (4 - 3 * t) := by
    rw [hgap]
    exact hfrac
  linarith

/-- **Weighted Inverse-Cube Stationary Lower Bound**: if positive normalized
    denominators `u` and `v` preserve the affine weighted average
    `q*u + v = q + 1`, then the weighted inverse-cube sum is minimized at
    `u = v = 1`.

    This is the normalized shape of the two-pool asymmetric curvature
    minimizer after substituting the exact stationary split. -/
theorem weighted_inv_cube_stationary_lower_bound
    (q u v : ℝ)
    (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (havg : q * u + v = q + 1) :
    q + 1 ≤ q / u^3 + 1 / v^3 := by
  have hu_tangent := inv_cube_tangent_lower_bound u hu
  have hv_tangent := inv_cube_tangent_lower_bound v hv
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hqu :
      q * (4 - 3 * u) ≤ q * (1 / u^3) :=
    mul_le_mul_of_nonneg_left hu_tangent hq_nonneg
  have hsum :
      q * (4 - 3 * u) + (4 - 3 * v) ≤
        q * (1 / u^3) + 1 / v^3 :=
    add_le_add hqu hv_tangent
  have hleft : q * (4 - 3 * u) + (4 - 3 * v) = q + 1 := by
    nlinarith [havg]
  have hright : q * (1 / u^3) + 1 / v^3 = q / u^3 + 1 / v^3 := by
    ring
  rwa [hleft, hright] at hsum

/-- **Normalized Asymmetric Split Curvature Stationary Certificate**: once an
    exact stationary split has normalized denominators `u = x/x*`,
    `v = y/y*`, exchange weight `q`, and scale `S`, every feasible split has
    curvature at least the stationary value.

    This theorem is intentionally certificate-shaped. A checker can verify the
    affine relation `q*u + v = q + 1` and the exact stationarity relation that
    reduces the original asymmetric CPMM curvature objective to this normalized
    form. -/
theorem normalized_asymmetric_split_curvature_stationary_min
    (S q u v : ℝ)
    (hS : 0 ≤ S) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (havg : q * u + v = q + 1) :
    S * (1 + 1 / q) ≤ S * (1 / u^3 + 1 / (q * v^3)) := by
  have hbase := weighted_inv_cube_stationary_lower_bound q u v hq hu hv havg
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hdiv :
      (q + 1) / q ≤ (q / u^3 + 1 / v^3) / q :=
    div_le_div_of_nonneg_right hbase hq_nonneg
  have hleft : (q + 1) / q = 1 + 1 / q := by
    field_simp [ne_of_gt hq]
  have hright :
      (q / u^3 + 1 / v^3) / q =
        1 / u^3 + 1 / (q * v^3) := by
    field_simp [ne_of_gt hq, ne_of_gt hu, ne_of_gt hv]
  rw [hleft, hright] at hdiv
  exact mul_le_mul_of_nonneg_left hdiv hS

/-- **Symmetric Split Exact Curvature Minimizer**: when the two CPMM pools have
    identical reserves and fee multipliers, the split-curvature sum is minimized
    at the midpoint `D/2`.

    This proves the exact minimizer formula for the symmetric subfamily:

    `H(a) = 2*c^2*K*M/(M+c*a)^3
          + 2*c^2*K*M/(M+c*(D-a))^3`

    satisfies `H(a) >= H(D/2)` for every `0 <= a <= D`. The arbitrary
    asymmetric closed-form minimizer remains a separate open proof obligation. -/
theorem symmetric_split_curvature_min_at_half
    (K M c D a : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hc : 0 < c)
    (hD : 0 ≤ D) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D) :
    4 * c^2 * K * M / (M + c * (D / 2))^3 ≤
      2 * c^2 * K * M / (M + c * a)^3 +
      2 * c^2 * K * M / (M + c * (D - a))^3 := by
  have hDa_nn : 0 ≤ D - a := by linarith
  have hx : 0 < M + c * a := by positivity
  have hy : 0 < M + c * (D - a) := by positivity
  have hmid : 0 < M + c * (D / 2) := by positivity
  have hsum : 0 < (M + c * a) + (M + c * (D - a)) := by positivity
  have hcoeff : 0 ≤ 2 * c^2 * K * M := by positivity
  have h_inv := inv_cube_pair_lower_bound
    (M + c * a) (M + c * (D - a)) hx hy
  have h_scaled := mul_le_mul_of_nonneg_left h_inv hcoeff
  have hleft :
      (2 * c^2 * K * M) *
        (16 / ((M + c * a) + (M + c * (D - a)))^3) =
      4 * c^2 * K * M / (M + c * (D / 2))^3 := by
    field_simp [ne_of_gt hsum, ne_of_gt hmid]
    ring
  have hright :
      (2 * c^2 * K * M) *
        (1 / (M + c * a)^3 + 1 / (M + c * (D - a))^3) =
      2 * c^2 * K * M / (M + c * a)^3 +
      2 * c^2 * K * M / (M + c * (D - a))^3 := by
    ring
  rw [hleft, hright] at h_scaled
  exact h_scaled

/-! ## Asymmetric Split Curvature Minimizer Reduction

The `normalized_asymmetric_split_curvature_stationary_min` theorem above
proves the core inequality in normalized form: if `q*u + v = q + 1`,
then `S*(1 + 1/q) ≤ S*(1/u³ + 1/(q*v³))`.

The reduction from concrete CPMM parameters to this normalized form
requires:
1. Setting `u = x/x*`, `v = y/y*` where `x* = M0 + c0*a*`,
   `y* = M1 + c1*(D - a*)` are the stationary denominators.
2. Setting `q = c1*x*/(c0*y*)` and `S = 2*c0²*K0*M0/x*³`.
3. Proving the affine constraint `q*u + v = q + 1` holds for ALL `a`
   (the `a*` terms cancel — pure linear arithmetic).
4. Proving the curvature decomposition
   `H(a) = S*(1/u³ + 1/(q*v³))` using the stationarity condition
   `(x*/y*)⁴ = (c0³*K0*M0)/(c1³*K1*M1)`.
5. Proving `H(a*) = S*(1 + 1/q)` (substitution at `u = v = 1`).

The stationarity condition ensures that `q` from the affine constraint
matches `q` from the curvature decomposition. This is the key insight
that makes the reduction work.
-/

/-- **Asymmetric Split Curvature Minimizer Reduction**: given CPMM
    parameters and a stationary split `a_star` with denominators
    `x_star = M0 + c0*a_star`, `y_star = M1 + c1*(D - a_star)`
    satisfying the stationarity condition
    `(x_star/y_star)^4 = (c0^3*K0*M0)/(c1^3*K1*M1)`,
    the curvature at any `a` is at least the curvature at `a_star`.

    This closes the open proof obligation noted in
    `symmetric_split_curvature_min_at_half`. The proof reduces to the
    existing `normalized_asymmetric_split_curvature_stationary_min`
    theorem via the normalization described above.

    Non-claims:
    - The stationarity condition is a checked hypothesis, not derived
      here. It corresponds to `dH/da = 0` at `a_star`.
    - The theorem proves the curvature minimum, not the split function
      maximum. The split function maximum follows from the
      strong-concavity chain (P2 bridge + P1/P3 argmax proximity).
    - The `a_star` need not be in `[0, D]` for the algebra to work,
      but the curvature bound is meaningful only when both `a` and
      `a_star` are in the valid domain. -/
theorem asymmetric_split_curvature_min_at_stationary
    (K0 M0 c0 K1 M1 c1 D a a_star : ℝ)
    (hK0 : 0 < K0) (hM0 : 0 < M0) (hc0 : 0 < c0)
    (_hK1 : 0 < K1) (hM1 : 0 < M1) (hc1 : 0 < c1)
    (_hD : 0 ≤ D) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    (h_star_nn : 0 ≤ a_star) (h_star_le_D : a_star ≤ D)
    (h_stationarity :
      (M0 + c0 * a_star) ^ 4 * (c1 ^ 3 * K1 * M1) =
      (M1 + c1 * (D - a_star)) ^ 4 * (c0 ^ 3 * K0 * M0)) :
    2 * c0 ^ 2 * K0 * M0 / (M0 + c0 * a_star) ^ 3 +
    2 * c1 ^ 2 * K1 * M1 / (M1 + c1 * (D - a_star)) ^ 3 ≤
    2 * c0 ^ 2 * K0 * M0 / (M0 + c0 * a) ^ 3 +
    2 * c1 ^ 2 * K1 * M1 / (M1 + c1 * (D - a)) ^ 3 := by
  -- Generalize denominators to opaque variables so field_simp won't unfold them
  generalize hxa : M0 + c0 * a = x
  generalize hya : M1 + c1 * (D - a) = y
  generalize hxa' : M0 + c0 * a_star = x_star
  generalize hya' : M1 + c1 * (D - a_star) = y_star
  -- Positivity (prove in original form, then convert via generalize hypotheses)
  have hx : 0 < x := by
    have : 0 < M0 + c0 * a := by positivity
    rw [hxa] at this; exact this
  have hy : 0 < y := by
    have hDa_nn : 0 ≤ D - a := by linarith
    have : 0 < M1 + c1 * (D - a) := by positivity
    rw [hya] at this; exact this
  have hx_star : 0 < x_star := by
    have : 0 < M0 + c0 * a_star := by positivity
    rw [hxa'] at this; exact this
  have hy_star : 0 < y_star := by
    have hDstar_nn : 0 ≤ D - a_star := by linarith
    have : 0 < M1 + c1 * (D - a_star) := by positivity
    rw [hya'] at this; exact this
  -- Stationarity in generalized form
  have h_stat : x_star ^ 4 * (c1 ^ 3 * K1 * M1) =
      y_star ^ 4 * (c0 ^ 3 * K0 * M0) := by
    rw [← hxa', ← hya']; exact h_stationarity
  -- Normalization variable values (no set/let to avoid field_simp unfolding)
  -- u = x / x_star, v = y / y_star, q = c1*x_star/(c0*y_star), S = 2*c0^2*K0*M0/x_star^3
  -- Positivity of normalization variables
  have hu : 0 < x / x_star := div_pos hx hx_star
  have hv : 0 < y / y_star := div_pos hy hy_star
  have hq : 0 < c1 * x_star / (c0 * y_star) := by
    have hc1s : 0 < c1 * x_star := mul_pos hc1 hx_star
    exact div_pos hc1s (mul_pos hc0 hy_star)
  have hS : 0 ≤ 2 * c0 ^ 2 * K0 * M0 / x_star ^ 3 := by
    have hnum : 0 < 2 * c0 ^ 2 * K0 * M0 := by positivity
    have hden : 0 < x_star ^ 3 := pow_pos hx_star 3
    exact le_of_lt (div_pos hnum hden)
  -- Affine constraint: q*u + v = q + 1
  have h_sum_eq : c1 * x + c0 * y = c1 * x_star + c0 * y_star := by
    rw [← hxa, ← hya, ← hxa', ← hya']; ring
  have h_affine :
      (c1 * x_star / (c0 * y_star)) * (x / x_star) + y / y_star =
      c1 * x_star / (c0 * y_star) + 1 := by
    have hcz : c0 * y_star ≠ 0 := mul_ne_zero (ne_of_gt hc0) (ne_of_gt hy_star)
    have hxz : x_star ≠ 0 := ne_of_gt hx_star
    have hyz : y_star ≠ 0 := ne_of_gt hy_star
    field_simp
    linear_combination h_sum_eq
  -- Term 1: S / u^3 = 2*c0^2*K0*M0 / x^3
  have h_term1 :
      (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) / (x / x_star) ^ 3 =
      2 * c0 ^ 2 * K0 * M0 / x ^ 3 := by
    have hxz : x_star ≠ 0 := ne_of_gt hx_star
    field_simp
  -- Term 2: S / (q * v^3) = 2*c1^2*K1*M1 / y^3
  have h_term2 :
      (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) /
      ((c1 * x_star / (c0 * y_star)) * (y / y_star) ^ 3) =
      2 * c1 ^ 2 * K1 * M1 / y ^ 3 := by
    have hcz : c0 * y_star ≠ 0 := mul_ne_zero (ne_of_gt hc0) (ne_of_gt hy_star)
    have hxz : x_star ≠ 0 := ne_of_gt hx_star
    have hyz : y_star ≠ 0 := ne_of_gt hy_star
    field_simp
    linear_combination (-1 : ℝ) * h_stat
  -- Full decomposition: H(a) = S*(1/u^3 + 1/(q*v^3))
  have h_decomp :
      (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) *
        (1 / (x / x_star) ^ 3 + 1 / ((c1 * x_star / (c0 * y_star)) * (y / y_star) ^ 3)) =
      2 * c0 ^ 2 * K0 * M0 / x ^ 3 +
      2 * c1 ^ 2 * K1 * M1 / y ^ 3 := by
    have h_split :
        (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) *
          (1 / (x / x_star) ^ 3 + 1 / ((c1 * x_star / (c0 * y_star)) * (y / y_star) ^ 3)) =
        (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) / (x / x_star) ^ 3 +
        (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) /
        ((c1 * x_star / (c0 * y_star)) * (y / y_star) ^ 3) := by
      rw [div_eq_inv_mul, div_eq_inv_mul]; ring
    rw [h_split, h_term1, h_term2]
  -- Star term 2: S / q = 2*c1^2*K1*M1 / y_star^3
  have h_star_term2 :
      (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) / (c1 * x_star / (c0 * y_star)) =
      2 * c1 ^ 2 * K1 * M1 / y_star ^ 3 := by
    have hcz : c0 * y_star ≠ 0 := mul_ne_zero (ne_of_gt hc0) (ne_of_gt hy_star)
    have hxz : x_star ≠ 0 := ne_of_gt hx_star
    have hyz : y_star ≠ 0 := ne_of_gt hy_star
    field_simp
    linear_combination (-1 : ℝ) * h_stat
  -- Star decomposition: H(a*) = S*(1 + 1/q)
  have h_star_decomp :
      (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) * (1 + 1 / (c1 * x_star / (c0 * y_star))) =
      2 * c0 ^ 2 * K0 * M0 / x_star ^ 3 +
      2 * c1 ^ 2 * K1 * M1 / y_star ^ 3 := by
    have h_split :
        (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) * (1 + 1 / (c1 * x_star / (c0 * y_star))) =
        2 * c0 ^ 2 * K0 * M0 / x_star ^ 3 +
        (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3) / (c1 * x_star / (c0 * y_star)) := by
      rw [div_eq_inv_mul]; ring
    rw [h_split, h_star_term2]
  -- Apply the normalized theorem with explicit values
  have h_norm := normalized_asymmetric_split_curvature_stationary_min
    (2 * c0 ^ 2 * K0 * M0 / x_star ^ 3)   -- S
    (c1 * x_star / (c0 * y_star))          -- q
    (x / x_star)                           -- u
    (y / y_star)                           -- v
    hS hq hu hv h_affine
  -- Combine: rewrite goal using decompositions
  rw [← h_star_decomp, ← h_decomp]
  exact h_norm

/-- **Witness**: Concrete case showing the lower bound is non-vacuous and
    strictly positive. K0=1000, M0=1000, c0=0.99, K1=2000, M1=1000,
    c1=0.99, D=100, a=50. -/
theorem witness_strong_concavity_bound :
    (0 : ℝ) < 2 * (0.99)^2 * 1000 * 1000 / (1000 + 0.99 * 100)^3 +
            2 * (0.99)^2 * 2000 * 1000 / (1000 + 0.99 * 100)^3 := by
  norm_num

/-- The endpoint curvature lower bound is positive under positive reserves,
    positive fee multipliers, and non-negative total input. -/
theorem split_curvature_endpoint_lower_bound_pos
    (K0 M0 c0 K1 M1 c1 D : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (hD : D ≥ 0) :
    (0 : ℝ) <
      2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 +
      2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3 := by
  have hM0cD : 0 < M0 + c0 * D := by positivity
  have hM1cD : 0 < M1 + c1 * D := by positivity
  have hden0 : 0 < (M0 + c0 * D)^3 := pow_pos hM0cD 3
  have hden1 : 0 < (M1 + c1 * D)^3 := pow_pos hM1cD 3
  have hnum0 : 0 < 2 * c0^2 * K0 * M0 := by positivity
  have hnum1 : 0 < 2 * c1^2 * K1 * M1 := by positivity
  have hterm0 : 0 < 2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 :=
    div_pos hnum0 hden0
  have hterm1 : 0 < 2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3 :=
    div_pos hnum1 hden1
  positivity

/-! ## P7: Conditional Second-Derivative Identity Bridge

This section turns external calculus obligations into explicit hypotheses.
Given the single-pool second-derivative formulas and the split chain-rule
identity, Lean checks the algebraic substitution into
`F''(a) = -T0(a) - T1(a)`.

The arithmetic curvature lower bound above is fully proved in this file. The
calculus facts needed to interpret those curvature terms as a function-level
strong-concavity parameter remain explicit inputs to the theorems below.
-/

/-- **Conditional Second-Derivative Identity**: if the two single-pool
    derivative formulas and the split chain-rule formula are supplied, then
    the CPMM split second derivative is `-T0(a) - T1(a)`.

    The supplied formulas are standard calculus obligations for:
    `f(x) = K*x/(M+x)` and
    `F(a) = f0(c0*a) + f1(c1*(D-a))`. -/
theorem splitFunctionCont_second_deriv_identity
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (_hK0 : K0 > 0) (_hM0 : M0 > 0) (_hc0 : c0 > 0)
    (_hK1 : K1 > 0) (_hM1 : M1 > 0) (_hc1 : c1 > 0)
    (_h_denom0 : M0 + c0 * a > 0)
    (_h_denom1 : M1 + c1 * (D - a) > 0)
    (h_chain :
      deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
        c0^2 * deriv (deriv (cpmmOutputCont K0 M0)) (c0 * a) +
        c1^2 * deriv (deriv (cpmmOutputCont K1 M1)) (c1 * (D - a)))
    (h_pool0 :
      deriv (deriv (cpmmOutputCont K0 M0)) (c0 * a) =
        -2 * K0 * M0 / (M0 + c0 * a)^3)
    (h_pool1 :
      deriv (deriv (cpmmOutputCont K1 M1)) (c1 * (D - a)) =
        -2 * K1 * M1 / (M1 + c1 * (D - a))^3) :
    deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
      -(2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3) -
      (2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3) := by
  rw [h_chain, h_pool0, h_pool1]
  ring

/-- **Conditional Function-Level Strong Concavity**: if the second-derivative
    identity is supplied for `a`, the proved arithmetic lower bound gives
    `F''(a) <= -m`, where
    `m = T0(D) + T1(0)`.

    This theorem is proof-facing glue. It does not discharge the calculus facts
    or the Taylor-remainder bridge used by window-bound arguments. -/
theorem splitFunctionCont_strong_concavity
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (hD : D ≥ 0) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    (h_identity :
      deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
        -(2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3) -
        (2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)) :
    deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a ≤
      -(2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 +
        2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3) := by
  have h_arith := strong_concavity_lower_bound
    K0 M0 c0 K1 M1 c1 D a hK0 hM0 (le_of_lt hc0) hK1 hM1 (le_of_lt hc1)
    hD ha_nn ha_le_D
  rw [h_identity]
  linarith

/-- **Curvature-Floor Certificate Soundness**: if an external checker supplies
    a positive `m` that is a lower bound for the local curvature terms at `a`,
    and the local second-derivative identity is supplied for `a`, then `m` is a
    valid pointwise strong-concavity certificate at `a`.

    This theorem is the Lean consumer for sharper certificates such as exact
    minimizers or interval arithmetic floors. It does not prove any particular
    minimizer formula; that proof remains a separate obligation. -/
theorem splitFunctionCont_strong_concavity_from_curvature_floor
    (K0 M0 c0 K1 M1 c1 D a m : ℝ)
    (_hm_pos : 0 < m)
    (hm_floor :
      m ≤
        2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3 +
        2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)
    (h_identity :
      deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
        -(2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3) -
        (2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)) :
    deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a ≤ -m := by
  rw [h_identity]
  linarith

/-- **Pool-Parameter m Certificate Soundness**: if an external checker supplies
    a positive `m` that does not exceed the endpoint curvature lower bound, and
    the local second-derivative identity is supplied for `a`, then `m` is a
    valid strong-concavity certificate at `a`.

    This theorem is the Lean side of the research certificate checker. It
    verifies the arithmetic handoff from pool parameters to the `m` consumed by
    argmax-radius theorems. It still treats the calculus identity and the
    Taylor-remainder bridge as explicit external obligations. -/
theorem splitFunctionCont_strong_concavity_from_m_certificate
    (K0 M0 c0 K1 M1 c1 D a m : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (hD : D ≥ 0) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    (_hm_pos : 0 < m)
    (hm_le :
      m ≤
        2 * c0^2 * K0 * M0 / (M0 + c0 * D)^3 +
        2 * c1^2 * K1 * M1 / (M1 + c1 * D)^3)
    (h_identity :
      deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
        -(2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3) -
        (2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)) :
    deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a ≤ -m := by
  have h_endpoint := splitFunctionCont_strong_concavity
    K0 M0 c0 K1 M1 c1 D a hK0 hM0 hc0 hK1 hM1 hc1 hD ha_nn ha_le_D
    h_identity
  linarith

/-! ## P2 Extension: Taylor-Remainder Quadratic Growth Bridge

The argmax proximity chain (in `DiscreteArgmaxProximity.lean`) consumes a
quadratic growth hypothesis:

  `h_quadratic_growth : ∀ x, f_cont x ≤ f_cont b_star - (m/2) * (x - b_star)^2`

The theorems above prove that `F''(a) ≤ -m` pointwise under calculus
hypotheses. The bridge from pointwise second-derivative bounds to
quadratic growth is a standard Taylor-remainder argument.

The Lagrange form of the Taylor remainder gives: for `f` twice
differentiable, there exists `ξ` between `b*` and `x` such that

  `f(x) = f(b*) + f'(b*)*(x - b*) + f''(ξ)*(x - b*)^2 / 2`

When `f'(b*) = 0` and `f''(ξ) ≤ -m`, this simplifies to

  `f(x) ≤ f(b*) - (m/2)*(x - b*)^2`

This section provides the bridge as a conditional theorem. The Lagrange
remainder existence is supplied as an explicit hypothesis, matching the
codebase pattern of treating calculus obligations as checked inputs.

Prior art: Lemma 1 from arXiv 1312.7463 (Taylor's Theorem for Loss
Functions) gives the general quadratic upper bound
`f(y) ≤ f(x) + f'(x)*(y-x) + (M/2)*(y-x)^2` where `M = sup f''`.
Our theorem is the special case with `f'(b*) = 0` and `-m` as a valid
upper bound on `f''`; using `sup f'' ≤ -m` and nonnegativity of
`(x - b*)^2` gives the same quadratic growth conclusion.
-/

/-- **Taylor-remainder quadratic growth bridge (Lagrange form)**: if
    there exists `ξ` between `b_star` and `x` such that
    `f(x) = f(b_star) + f'(b_star)*(x - b_star) + f''(ξ)*(x - b_star)^2 / 2`,
    and `f'(b_star) = 0`, and `f''(ξ) ≤ -m`, then
    `f(x) ≤ f(b_star) - (m/2) * (x - b_star)^2`.

    This is the bridge from pointwise strong concavity to the quadratic
    growth hypothesis consumed by the argmax proximity chain.

    The Lagrange remainder existence is a checked hypothesis. The proof
    is pure algebra: substitute `f'(b*) = 0` and `f''(ξ) ≤ -m` into the
    Taylor expansion and simplify.

    Non-claims:
    - The Lagrange remainder existence is a checked input, not derived here.
    - The theorem is abstract: it applies to any twice-differentiable
      function, not just the CPMM split function.
    - The `m > 0` hypothesis ensures the bound is non-trivial.
    - The `ξ` is existentially quantified: the caller must supply both
      the witness and the Taylor expansion at that witness. -/
theorem taylor_remainder_quadratic_growth_bridge
    (f : ℝ → ℝ) (m b_star x ξ : ℝ)
    (_hm : 0 < m)
    (h_taylor_lagrange :
      f x = f b_star + deriv f b_star * (x - b_star)
        + deriv (deriv f) ξ * (x - b_star) ^ 2 / 2)
    (h_first_deriv_zero : deriv f b_star = 0)
    (h_second_deriv_bound : deriv (deriv f) ξ ≤ -m) :
    f x ≤ f b_star - (m / 2) * (x - b_star) ^ 2 := by
  rw [h_taylor_lagrange, h_first_deriv_zero, zero_mul, add_zero]
  have h_sq_nn : 0 ≤ (x - b_star) ^ 2 := sq_nonneg _
  have h_prod_le : deriv (deriv f) ξ * (x - b_star) ^ 2 ≤
      (-m) * (x - b_star) ^ 2 :=
    mul_le_mul_of_nonneg_right h_second_deriv_bound h_sq_nn
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_term_bound : deriv (deriv f) ξ * (x - b_star) ^ 2 / 2 ≤
      (-m) * (x - b_star) ^ 2 / 2 := by
    rw [le_div_iff₀ h_two_pos]
    linarith
  linarith

/-- **Order-free forwarding theorem**: This is an alias for
    `taylor_remainder_quadratic_growth_bridge` with identical
    hypotheses and conclusion. The main theorem already has no ordering
    assumption on `b_star` vs `x`; the Lagrange remainder hypothesis is
    symmetric in the ordering. This alias is provided for call-site
    clarity when the caller's context has `x ≤ b_star`. -/
theorem taylor_remainder_quadratic_growth_bridge_symmetric
    (f : ℝ → ℝ) (m b_star x ξ : ℝ)
    (hm : 0 < m)
    (h_taylor_lagrange :
      f x = f b_star + deriv f b_star * (x - b_star)
        + deriv (deriv f) ξ * (x - b_star) ^ 2 / 2)
    (h_first_deriv_zero : deriv f b_star = 0)
    (h_second_deriv_bound : deriv (deriv f) ξ ≤ -m) :
    f x ≤ f b_star - (m / 2) * (x - b_star) ^ 2 := by
  exact taylor_remainder_quadratic_growth_bridge f m b_star x ξ hm
    h_taylor_lagrange h_first_deriv_zero h_second_deriv_bound

/-- **Universal quadratic growth from pointwise strong concavity**: if
    the Lagrange remainder exists for every `x` (with some `ξ` depending
    on `x`), `f'(b_star) = 0`, and `f''(t) ≤ -m` for all `t`, then
    `f(x) ≤ f(b_star) - (m/2) * (x - b_star)^2` for all `x`.

    This is the universal form of the quadratic growth bound, suitable
    as a direct drop-in for the `h_quadratic_growth` hypothesis of the
    argmax proximity theorems.

    The hypotheses `h_second_deriv_bound` and `h_lagrange` are globally
    quantified over all `ℝ`. In practice, the CPMM curvature theorems
    above are domain-scoped (e.g., `0 ≤ a ≤ D`), so applying this
    theorem to the CPMM split function requires either a global
    extension of the curvature bound or restricting the conclusion to
    the domain interval. The Lagrange remainder existence for every `x`
    is a checked hypothesis; for the CPMM split function, it follows
    from twice continuous differentiability on an interval containing
    both `b_star` and the queried `x`. -/
theorem universal_quadratic_growth_from_strong_concavity
    (f : ℝ → ℝ) (m b_star : ℝ)
    (hm : 0 < m)
    (h_first_deriv_zero : deriv f b_star = 0)
    (h_second_deriv_bound : ∀ t : ℝ, deriv (deriv f) t ≤ -m)
    (h_lagrange : ∀ x : ℝ, ∃ ξ : ℝ,
      f x = f b_star + deriv f b_star * (x - b_star)
        + deriv (deriv f) ξ * (x - b_star) ^ 2 / 2) :
    ∀ x : ℝ, f x ≤ f b_star - (m / 2) * (x - b_star) ^ 2 := by
  intro x
  obtain ⟨ξ, h_taylor⟩ := h_lagrange x
  exact taylor_remainder_quadratic_growth_bridge f m b_star x ξ hm
    h_taylor h_first_deriv_zero (h_second_deriv_bound ξ)
