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
