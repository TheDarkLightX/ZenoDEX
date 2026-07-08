/-
# Exact Interval Certificate Path Theorem

This file composes the maximizer bracket (P9), continuous upper value bound
(P9), and strong concavity (P2) into the complete exact interval certificate
path theorem. The theorem proves that if the derivative bracket contains the
maximizer, the curvature lower bound is positive, strong concavity holds, and
the production floor is below the continuous value, then the distance from the
production argmax to the continuous maximizer is bounded by the certified
radius.

## Certificate Chain

The exact interval certificate checker (empirical) verifies:

```text
0 <= lo <= hi <= D
derivative(lo) >= 0 and derivative(hi) <= 0
m = endpoint_m(p0, p1, D) > 0
cont_star_upper = f0(hi) + f1(D - lo)
tau_upper = cont_star_upper - prod(argmax)
radius_sq = 2 * tau_upper / m
distance_sq_upper = max((argmax - lo)^2, (argmax - hi)^2)
distance_sq_upper <= radius_sq
```

The Lean theorem proves that these conditions imply:

```text
|argmax - b_star| <= sqrt(2 * tau_upper / m)
```

The proof chain is:
1. Derivative bracket + F' strictly decreasing → b* in [lo, hi] (P9)
2. b* in [lo, hi] → F(b*) <= cont_star_upper (P9)
3. F(b*) - prod(argmax) <= cont_star_upper - prod(argmax) = tau_upper (arithmetic)
4. Strong concavity: (m/2)*(argmax - b*)^2 <= F(b*) - prod(argmax) (existing)
5. (m/2)*(argmax - b*)^2 <= tau_upper (transitivity 3, 4)
6. (argmax - b*)^2 <= 2*tau_upper/m (algebra)
7. |argmax - b*| <= sqrt(2*tau_upper/m) (sqrt monotonicity)

## Scope and Non-Claims

- The theorem assumes F' is strictly decreasing (supplied as hypothesis).
- The theorem assumes strong concavity with parameter m (supplied as hypothesis).
- The theorem does not prove the existence or uniqueness of the maximizer.
- The theorem does not grant production, settlement, or consensus authority.
- The empirical checker recomputes all values with exact rational arithmetic;
  this theorem confirms the mathematical soundness of the certificate shape.

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/ExactIntervalCertificatePath.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.MaximizerBracket

set_option linter.unusedVariables false

open Real

/-! ## Exact Interval Certificate Path Theorem

The main theorem composes all pieces into the complete certificate path.
The key insight is that the certificate does not need to know `b_star`
exactly. It uses:
- `cont_star_upper` as an upper bound on `F(b_star)`
- `tau_upper = cont_star_upper - prod(argmax)` as an upper bound on the slack
- `radius_sq = 2 * tau_upper / m` as the squared certified radius
- `distance_sq_upper = max((argmax-lo)^2, (argmax-hi)^2)` as an upper bound
  on `(argmax - b_star)^2`

The check `distance_sq_upper <= radius_sq` then guarantees
`|argmax - b_star| <= sqrt(2 * tau_upper / m)`.
-/

/-- **Exact Interval Certificate Path**: if the derivative bracket contains
    the continuous maximizer `b_star`, the curvature lower bound `m` is
    positive, strong concavity holds, and the production value at `argmax`
    is below the continuous value, then the distance from `argmax` to
    `b_star` is bounded by the certified radius `sqrt(2 * tau_upper / m)`.

    This is the Lean foundation for the exact interval certificate checker's
    complete verification path. The empirical checker verifies all
    conditions with exact rational arithmetic; this theorem confirms that
    accepted conditions imply the distance bound.

    The `tau_upper` is computed as `cont_star_upper - prod_value`, where
    `cont_star_upper = f0(hi) + f1(D - lo)` is the conservative continuous
    upper value from the bracket, and `prod_value` is the recomputed
    production value at `argmax`.

    The proof composes:
    1. `splitFunctionCont_maximizer_bracket` (P9): bracket → `b* in [lo, hi]`
    2. `splitFunctionCont_cont_upper_bound` (P9): `b* in [lo, hi]` → `F(b*) <= cont_star_upper`
    3. `abstract_oracle_perturbed_argmax_distance` (P8): strong concavity + prod ≤ cont → distance bound
    4. Transitivity: `F(b*) - prod <= tau_upper` → distance ≤ `sqrt(2 * tau_upper / m)` -/
theorem exact_interval_certificate_path
    (K0 M0 c0 K1 M1 c1 D lo hi b_star argmax m tau_upper cont_star_upper prod_value : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0)
    (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_argmax_nn : 0 ≤ argmax) (h_argmax_le_D : argmax ≤ D)
    -- Derivative bracket conditions
    (h_deriv_strict_decreasing :
      ∀ x y : ℝ, x < y →
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) x >
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) y)
    (h_deriv_lo : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) lo ≥ 0)
    (h_deriv_hi : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) hi ≤ 0)
    -- Maximality of b_star
    (h_b_star_max : ∀ x : ℝ, 0 ≤ x → x ≤ D →
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    -- Curvature lower bound
    (hm : m > 0)
    -- Strong concavity
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    -- Continuous upper value (recomputed by checker)
    (h_cont_star_upper :
      cont_star_upper =
        cpmmOutputCont K0 M0 (c0 * hi) + cpmmOutputCont K1 M1 (c1 * (D - lo)))
    -- Production value at argmax (recomputed by checker)
    (h_prod_value :
      prod_value ≤ splitFunctionCont K0 M0 c0 K1 M1 c1 D argmax)
    -- Certificate slack
    (h_tau_upper : tau_upper = cont_star_upper - prod_value)
    -- Radius check: distance_sq_upper <= radius_sq
    (h_radius_check :
      max ((argmax - lo)^2) ((argmax - hi)^2) ≤ 2 * tau_upper / m) :
    |argmax - b_star| ≤ Real.sqrt (2 * tau_upper / m) := by
  -- Step 1: Derivative bracket → b* in [lo, hi]
  have h_bracket :=
    splitFunctionCont_maximizer_bracket
      (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
      lo hi b_star D
      h_lo_nn h_hi_le_D h_lo_le_hi
      h_b_star_nn h_b_star_le_D
      h_deriv_strict_decreasing h_deriv_lo h_deriv_hi
      h_b_star_max
  -- Step 2: b* in [lo, hi] → F(b*) <= cont_star_upper
  have h_cont_upper :=
    splitFunctionCont_cont_upper_bound
      K0 M0 c0 K1 M1 c1 D lo hi b_star
      hK0 hM0 hc0 hK1 hM1 hc1
      (le_of_lt hD) h_lo_nn h_hi_le_D h_lo_le_hi
      h_b_star_nn h_b_star_le_D h_bracket
  -- Step 3: F(b*) - prod_value <= cont_star_upper - prod_value = tau_upper
  have h_slack_bound :
    splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - prod_value ≤ tau_upper := by
    rw [h_tau_upper]
    linarith [h_cont_upper, h_cont_star_upper]
  -- Step 4: Apply oracle-tight distance bound
  -- |argmax - b_star| <= sqrt(2 * (F(b*) - prod_value) / m)
  -- We need prod_value as a function of argmax for the oracle theorem.
  -- Instead, use the abstract version directly.
  have h_sc_argmax := h_strong_concave argmax
  -- (m/2) * (argmax - b_star)^2 <= F(b*) - prod_value
  have h_quad_bound :
    (m / 2) * (argmax - b_star)^2 ≤
    splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - prod_value := by
    linarith [h_prod_value, h_sc_argmax]
  -- (m/2) * (argmax - b_star)^2 <= tau_upper
  have h_quad_le_tau : (m / 2) * (argmax - b_star)^2 ≤ tau_upper :=
    le_trans h_quad_bound h_slack_bound
  -- (argmax - b_star)^2 <= 2 * tau_upper / m
  have h_sq_le_radius_sq : (argmax - b_star)^2 ≤ 2 * tau_upper / m := by
    rw [le_div_iff₀ hm]
    have h_2m : 2 * (m / 2 : ℝ) = m := by ring
    nlinarith [h_quad_le_tau, hm, h_2m]
  -- |argmax - b_star| <= sqrt(2 * tau_upper / m)
  have h_abs_sq : |argmax - b_star|^2 = (argmax - b_star)^2 :=
    sq_abs (argmax - b_star)
  have h_abs_nn : 0 ≤ |argmax - b_star| :=
    abs_nonneg (argmax - b_star)
  have h_abs_eq_sqrt : |argmax - b_star| = Real.sqrt (|argmax - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_abs_sq]
  exact Real.sqrt_le_sqrt h_sq_le_radius_sq

/-! ## Squared Distance Variant

The empirical checker uses squared distances to avoid floating-point sqrt.
This variant proves the squared form directly.
-/

/-- **Exact Interval Certificate Path (Squared)**: same conditions as
    `exact_interval_certificate_path`, but the conclusion is in squared form:

    `(argmax - b_star)^2 <= 2 * tau_upper / m`

    This is the Lean foundation for the checker's `distance_sq_upper <=
    radius_sq` check. The checker computes `distance_sq_upper = max((argmax -
    lo)^2, (argmax - hi)^2)` and `radius_sq = 2 * tau_upper / m` with exact
    rational arithmetic, then verifies `distance_sq_upper <= radius_sq`.

    By the bracket distance bound (P9), `(argmax - b_star)^2 <=
    distance_sq_upper`, so the checker's acceptance implies this theorem's
    conclusion. -/
theorem exact_interval_certificate_path_squared
    (K0 M0 c0 K1 M1 c1 D lo hi b_star argmax m tau_upper cont_star_upper prod_value : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0)
    (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_argmax_nn : 0 ≤ argmax) (h_argmax_le_D : argmax ≤ D)
    (h_deriv_strict_decreasing :
      ∀ x y : ℝ, x < y →
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) x >
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) y)
    (h_deriv_lo : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) lo ≥ 0)
    (h_deriv_hi : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) hi ≤ 0)
    (h_b_star_max : ∀ x : ℝ, 0 ≤ x → x ≤ D →
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    (hm : m > 0)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    (h_cont_star_upper :
      cont_star_upper =
        cpmmOutputCont K0 M0 (c0 * hi) + cpmmOutputCont K1 M1 (c1 * (D - lo)))
    (h_prod_value :
      prod_value ≤ splitFunctionCont K0 M0 c0 K1 M1 c1 D argmax)
    (h_tau_upper : tau_upper = cont_star_upper - prod_value) :
    (argmax - b_star)^2 ≤ 2 * tau_upper / m := by
  -- Same proof as above, stopping before the sqrt step
  have h_bracket :=
    splitFunctionCont_maximizer_bracket
      (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
      lo hi b_star D
      h_lo_nn h_hi_le_D h_lo_le_hi
      h_b_star_nn h_b_star_le_D
      h_deriv_strict_decreasing h_deriv_lo h_deriv_hi
      h_b_star_max
  have h_cont_upper :=
    splitFunctionCont_cont_upper_bound
      K0 M0 c0 K1 M1 c1 D lo hi b_star
      hK0 hM0 hc0 hK1 hM1 hc1
      (le_of_lt hD) h_lo_nn h_hi_le_D h_lo_le_hi
      h_b_star_nn h_b_star_le_D h_bracket
  have h_slack_bound :
    splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - prod_value ≤ tau_upper := by
    rw [h_tau_upper]
    linarith [h_cont_upper, h_cont_star_upper]
  have h_sc_argmax := h_strong_concave argmax
  have h_quad_bound :
    (m / 2) * (argmax - b_star)^2 ≤
    splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - prod_value := by
    linarith [h_prod_value, h_sc_argmax]
  have h_quad_le_tau : (m / 2) * (argmax - b_star)^2 ≤ tau_upper :=
    le_trans h_quad_bound h_slack_bound
  rw [le_div_iff₀ hm]
  have h_2m : 2 * (m / 2 : ℝ) = m := by ring
  nlinarith [h_quad_le_tau, hm, h_2m]

/-! ## Checker Acceptance Implies Distance Bound

The empirical checker accepts when `distance_sq_upper <= radius_sq`. This
theorem confirms that acceptance implies the actual distance bound, using
the bracket distance bound from P9.
-/

/-- **Checker Acceptance Implies Distance Bound**: if the checker accepts
    (i.e., `distance_sq_upper <= radius_sq`), and the bracket contains
    `b_star`, then `(argmax - b_star)^2 <= distance_sq_upper <= radius_sq`.

    This composes the bracket distance bound (P9) with the checker's
    acceptance condition. The checker does not know `b_star`, but the
    bracket distance bound guarantees that the actual squared distance is
    at most `distance_sq_upper`, which the checker verifies is at most
    `radius_sq`. -/
theorem checker_acceptance_implies_distance_bound
    (lo hi b_star argmax radius_sq distance_sq_upper : ℝ)
    (h_lo_le_hi : lo ≤ hi)
    (h_b_star_in_bracket : lo ≤ b_star ∧ b_star ≤ hi)
    (h_distance_sq_upper :
      distance_sq_upper = max ((argmax - lo)^2) ((argmax - hi)^2))
    (h_checker_accept : distance_sq_upper ≤ radius_sq) :
    (argmax - b_star)^2 ≤ radius_sq := by
  -- |argmax - b_star| <= max(|argmax - lo|, |argmax - hi|) (P9)
  have h_dist :=
    bracket_distance_bound lo hi b_star argmax h_lo_le_hi h_b_star_in_bracket
  -- (argmax - b_star)^2 = |argmax - b_star|^2, etc.
  have h_sq_abs_b : (argmax - b_star)^2 = |argmax - b_star|^2 := (sq_abs _).symm
  have h_sq_abs_l : (argmax - lo)^2 = |argmax - lo|^2 := (sq_abs _).symm
  have h_sq_abs_h : (argmax - hi)^2 = |argmax - hi|^2 := (sq_abs _).symm
  have h_bstar_nn : 0 ≤ |argmax - b_star| := abs_nonneg _
  have h_lo_nn : 0 ≤ |argmax - lo| := abs_nonneg _
  have h_hi_nn : 0 ≤ |argmax - hi| := abs_nonneg _
  -- First prove: (argmax - b_star)^2 <= distance_sq_upper
  have h_le_dist_sq : (argmax - b_star)^2 ≤ distance_sq_upper := by
    rw [h_distance_sq_upper, h_sq_abs_b, h_sq_abs_l, h_sq_abs_h]
    -- Goal: |argmax - b_star|^2 <= max (|argmax - lo|^2) (|argmax - hi|^2)
    -- h_dist: |argmax - b_star| <= max |argmax - lo| |argmax - hi|
    by_cases h_max : |argmax - lo| ≤ |argmax - hi|
    · -- Rewrite max in h_dist to |argmax - hi|
      rw [max_eq_right h_max] at h_dist
      -- |argmax - lo|^2 <= |argmax - hi|^2, so max = |argmax - hi|^2
      have h_sq_max : |argmax - lo|^2 ≤ |argmax - hi|^2 := by
        nlinarith [h_max, h_lo_nn, h_hi_nn]
      rw [max_eq_right h_sq_max]
      -- Goal: |argmax - b_star|^2 <= |argmax - hi|^2
      -- h_dist now: |argmax - b_star| <= |argmax - hi|
      nlinarith [h_dist, h_bstar_nn, h_hi_nn]
    · -- |argmax - hi| < |argmax - lo|
      have h_lt : |argmax - hi| < |argmax - lo| := not_le.mp h_max
      have h_le_lo : |argmax - lo| ≤ |argmax - lo| := le_rfl
      -- Rewrite max in h_dist to |argmax - lo|
      rw [max_eq_left (le_of_lt h_lt)] at h_dist
      -- |argmax - hi|^2 <= |argmax - lo|^2, so max = |argmax - lo|^2
      have h_sq_max : |argmax - hi|^2 ≤ |argmax - lo|^2 := by
        nlinarith [h_lt, h_lo_nn, h_hi_nn]
      rw [max_eq_left h_sq_max]
      -- Goal: |argmax - b_star|^2 <= |argmax - lo|^2
      -- h_dist now: |argmax - b_star| <= |argmax - lo|
      nlinarith [h_dist, h_bstar_nn, h_lo_nn]
  exact le_trans h_le_dist_sq h_checker_accept

/-! ## Complete Certificate Soundness

The complete soundness theorem: if the checker accepts the certificate
(derivative bracket valid, m positive, all values recomputed, distance_sq_upper
<= radius_sq), then the actual distance from argmax to b_star is bounded by
the certified radius.

This is the composition of:
1. `exact_interval_certificate_path_squared` (steps 1-4 of the chain)
2. `checker_acceptance_implies_distance_bound` (bracket distance + acceptance)

Together they give: (argmax - b_star)^2 <= radius_sq = 2 * tau_upper / m.
-/

/-- **Complete Certificate Soundness**: if all certificate conditions hold
    (derivative bracket, strong concavity, recomputed values, radius check),
    then `|argmax - b_star| <= sqrt(2 * tau_upper / m)`.

    This is the main soundness theorem for the exact interval certificate
    checker. It composes the derivative bracket theorem (P9), continuous
    upper value bound (P9), strong concavity (P2), and the bracket distance
    bound (P9) into a single result confirming the checker's acceptance
    implies the distance bound. -/
theorem complete_certificate_soundness
    (K0 M0 c0 K1 M1 c1 D lo hi b_star argmax m tau_upper cont_star_upper prod_value : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0)
    (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_argmax_nn : 0 ≤ argmax) (h_argmax_le_D : argmax ≤ D)
    (h_deriv_strict_decreasing :
      ∀ x y : ℝ, x < y →
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) x >
        deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) y)
    (h_deriv_lo : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) lo ≥ 0)
    (h_deriv_hi : deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D) hi ≤ 0)
    (h_b_star_max : ∀ x : ℝ, 0 ≤ x → x ≤ D →
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    (hm : m > 0)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    (h_cont_star_upper :
      cont_star_upper =
        cpmmOutputCont K0 M0 (c0 * hi) + cpmmOutputCont K1 M1 (c1 * (D - lo)))
    (h_prod_value :
      prod_value ≤ splitFunctionCont K0 M0 c0 K1 M1 c1 D argmax)
    (h_tau_upper : tau_upper = cont_star_upper - prod_value)
    (h_radius_check :
      max ((argmax - lo)^2) ((argmax - hi)^2) ≤ 2 * tau_upper / m) :
    |argmax - b_star| ≤ Real.sqrt (2 * tau_upper / m) := by
  -- Method 1: Direct from exact_interval_certificate_path
  -- This already gives the bound without needing the radius_check
  -- (the radius_check is the checker's acceptance condition, which is
  -- stronger than needed because it uses the conservative distance_sq_upper
  -- rather than the actual distance)
  exact exact_interval_certificate_path
    K0 M0 c0 K1 M1 c1 D lo hi b_star argmax m tau_upper cont_star_upper prod_value
    hK0 hM0 hc0 hK1 hM1 hc1 hD
    h_lo_nn h_hi_le_D h_lo_le_hi
    h_b_star_nn h_b_star_le_D
    h_argmax_nn h_argmax_le_D
    h_deriv_strict_decreasing h_deriv_lo h_deriv_hi
    h_b_star_max
    hm h_strong_concave
    h_cont_star_upper h_prod_value h_tau_upper h_radius_check
