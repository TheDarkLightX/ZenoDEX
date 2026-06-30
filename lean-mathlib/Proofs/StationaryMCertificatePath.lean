/-
# Stationary m Certificate Path

This file composes the stationary curvature minimizer theorems (P2) with the
exact interval certificate path (P10) and interval curvature cover (P11),
giving the tightest possible certified radius when a stationary witness is
representable.

## Certificate Hierarchy

The three m sources form a dominance chain:

```text
m_endpoint <= m_interval <= m_stationary = m_exact
```

This gives a corresponding radius shrinkage chain:

```text
R_endpoint >= R_interval >= R_stationary = R_exact
```

where `R = sqrt(2 * tau_upper / m)`.

## Stationary Certificate

The stationary certificate gives the exact curvature minimum `m_exact =
min_{a in [0,D]} H(a)`. Two subfamilies are Lean-proven:

1. **Symmetric** (`symmetric_split_curvature_min_at_half`): for identical
   pools, `m_exact = H(D/2) = 4*c^2*K*M/(M+c*D/2)^3`.

2. **Asymmetric normalized** (`normalized_asymmetric_split_curvature_stationary_min`):
   for arbitrary pools with a representable stationary witness, the
   normalized certificate gives `m_exact = S*(1 + 1/q)` after the checker
   validates the affine normalization and stationarity relations.

## Composition

This file proves:

1. The symmetric stationary m is a valid universal curvature floor.
2. The symmetric stationary m dominates the endpoint m.
3. The asymmetric stationary m certificate path (general m parameter).
4. The symmetric stationary m certificate path (delegates to asymmetric).
5. The stationary radius dominates the interval and endpoint radii.

## Scope and Non-Claims

- The stationary witness existence is supplied as a hypothesis (the empirical
  checker validates it with exact rational arithmetic).
- The second derivative identity is supplied as a hypothesis.
- The Taylor remainder bridge is supplied as a hypothesis.
- The asymmetric closed-form fourth-root minimizer remains outside Lean.
- The theorem grants no production, settlement, or consensus authority.

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/StationaryMCertificatePath.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.MaximizerBracket
import Proofs.ExactIntervalCertificatePath
import Proofs.IntervalCurvatureCover

set_option linter.unusedVariables false

open Real

/-! ## Asymmetric Stationary m Certificate Path

For asymmetric pools with a representable stationary witness, the normalized
certificate gives the exact curvature minimum. The checker validates the
affine normalization and stationarity relations; Lean confirms the
normalized form is a valid universal floor.

This section comes first so the symmetric certificate path can delegate
to the asymmetric path theorem.
-/

/-- **Asymmetric Stationary m Soundness**: if a checker supplies a positive
    `m` that is a valid lower bound for the curvature sum `H(a)` at every
    point in `[0,D]` (via the normalized stationary certificate), and the
    second derivative identity holds at `a`, then `F''(a) <= -m`.

    This is a restatement of `splitFunctionCont_strong_concavity_from_curvature_floor`
    with the asymmetric stationary certificate as the floor source. The
    checker validates:
    - The affine normalization `q*u + v = q + 1`
    - The exact stationarity relation
    - The reduction of the original curvature to the normalized form

    This theorem confirms that the certified `m` is a valid strong
    concavity parameter. -/
theorem asymmetric_stationary_m_soundness
    (K0 M0 c0 K1 M1 c1 D a m : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (hD : D ≥ 0) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    (hm_pos : 0 < m)
    (hm_floor :
      m ≤
        2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3 +
        2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)
    (h_identity :
      deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a =
        -(2 * c0^2 * K0 * M0 / (M0 + c0 * a)^3) -
        (2 * c1^2 * K1 * M1 / (M1 + c1 * (D - a))^3)) :
    deriv (deriv (splitFunctionCont K0 M0 c0 K1 M1 c1 D)) a ≤ -m := by
  exact splitFunctionCont_strong_concavity_from_curvature_floor
    K0 M0 c0 K1 M1 c1 D a m hm_pos hm_floor h_identity

/-- **Asymmetric Stationary m Certificate Path**: if the asymmetric
    stationary certificate gives a valid `m` (validated by the checker
    via affine normalization and stationarity), and the derivative
    bracket contains `b*`, and the continuous upper value and production
    value are recomputed, then
    `|argmax - b*| <= sqrt(2 * tau_upper / m_stationary)`.

    This is the tightest certified radius for the asymmetric subfamily
    with a representable stationary witness. -/
theorem asymmetric_stationary_m_certificate_path
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
    |argmax - b_star| ≤ Real.sqrt (2 * tau_upper / m) := by
  -- Same proof as interval_m_certificate_path (P11) and exact_interval_certificate_path (P10)
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
  have h_sq_le_radius_sq : (argmax - b_star)^2 ≤ 2 * tau_upper / m := by
    have h_half_m_pos : 0 < m / 2 := by linarith
    have h_step1 : (argmax - b_star)^2 ≤ tau_upper / (m / 2) := by
      rw [le_div_iff₀ h_half_m_pos, mul_comm]
      exact h_quad_le_tau
    have h_step2 : tau_upper / (m / 2) = 2 * tau_upper / m := by
      field_simp
    linarith [h_step1, h_step2]
  have h_abs_sq : |argmax - b_star|^2 = (argmax - b_star)^2 :=
    sq_abs (argmax - b_star)
  have h_abs_nn : 0 ≤ |argmax - b_star| :=
    abs_nonneg (argmax - b_star)
  have h_abs_eq_sqrt : |argmax - b_star| = Real.sqrt (|argmax - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_abs_sq]
  exact Real.sqrt_le_sqrt h_sq_le_radius_sq

/-! ## Symmetric Stationary m Certificate

For identical pools (`K0=K1=K`, `M0=M1=M`, `c0=c1=c`), the exact curvature
minimum is at `a = D/2`, giving `m_symmetric = H(D/2)`.
-/

/-- **Symmetric Stationary m Universal Floor**: for identical pools, the
    curvature sum `H(a) >= H(D/2)` for all `a in [0,D]`.

    This is a direct application of `symmetric_split_curvature_min_at_half`,
    restated in the `m <= H(a)` form needed for certificate composition. -/
theorem symmetric_stationary_m_universal_floor
    (K M c D a : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hc : 0 < c)
    (hD : 0 ≤ D) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D) :
    4 * c^2 * K * M / (M + c * (D / 2))^3 ≤
      2 * c^2 * K * M / (M + c * a)^3 +
      2 * c^2 * K * M / (M + c * (D - a))^3 := by
  exact symmetric_split_curvature_min_at_half K M c D a hK hM hc hD ha_nn ha_le_D

/-- **Symmetric Stationary m Value**: the exact curvature minimum for
    identical pools is `m_sym = 4*c^2*K*M/(M+c*D/2)^3`.

    This is `H(D/2)`, the value of the curvature sum at the midpoint. -/
noncomputable def symmetric_stationary_m (K M c D : ℝ) : ℝ :=
  4 * c^2 * K * M / (M + c * (D / 2))^3

/-- **Symmetric Stationary m Soundness**: for identical pools, the
    symmetric stationary m is a valid strong concavity parameter:
    `F''(a) <= -m_sym` for all `a in [0,D]`, given the second
    derivative identity.

    Composes `symmetric_stationary_m_universal_floor` with
    `splitFunctionCont_strong_concavity_from_curvature_floor`. -/
theorem symmetric_stationary_m_soundness
    (K M c D a : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hc : 0 < c)
    (hD : 0 ≤ D) (ha_nn : 0 ≤ a) (ha_le_D : a ≤ D)
    (h_identity :
      deriv (deriv (splitFunctionCont K M c K M c D)) a =
        -(2 * c^2 * K * M / (M + c * a)^3) -
        (2 * c^2 * K * M / (M + c * (D - a))^3)) :
    deriv (deriv (splitFunctionCont K M c K M c D)) a ≤
      -(symmetric_stationary_m K M c D) := by
  have h_floor := symmetric_stationary_m_universal_floor
    K M c D a hK hM hc hD ha_nn ha_le_D
  rw [h_identity]
  unfold symmetric_stationary_m at h_floor ⊢
  linarith

/-! ## Symmetric Stationary m Dominance

The symmetric stationary m dominates the endpoint m for identical pools.
-/

/-- **Symmetric Stationary m Dominates Endpoint m**: for identical pools,
    `m_endpoint <= m_symmetric`.

    The endpoint m is `H(D) = H(0) = 4*c^2*K*M/(M+c*D)^3` (by symmetry).
    The stationary m is `H(D/2) = 4*c^2*K*M/(M+c*D/2)^3`.
    Since `M+c*D/2 < M+c*D` (for `D > 0`), the denominator is smaller,
    so the fraction is larger.

    This gives `R_symmetric <= R_endpoint`, the tightest radius. -/
theorem symmetric_stationary_m_dominates_endpoint
    (K M c D : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hc : 0 < c) (hD : 0 < D) :
    4 * c^2 * K * M / (M + c * D)^3 ≤
      4 * c^2 * K * M / (M + c * (D / 2))^3 := by
  -- Use T0_decreasing_bound: D/2 <= D => T0(D) <= T0(D/2)
  have h_D2_nn : 0 ≤ D / 2 := by linarith
  have h_D2_le_D : D / 2 ≤ D := by linarith
  have h0 := T0_decreasing_bound K M c (D / 2) D hK hM (le_of_lt hc) h_D2_nn h_D2_le_D
  -- h0: T0(D/2) >= T0(D), i.e. T0(D) <= T0(D/2)
  -- Goal: 2*T0(D) <= 2*T0(D/2), which is doubling h0
  have h_den_half_pos : 0 < (M + c * (D / 2))^3 := by positivity
  have h_den_full_pos : 0 < (M + c * D)^3 := by positivity
  -- Cross-multiply h0 to polynomial form, double, then divide back
  have h0_le : 2 * c^2 * K * M / (M + c * D)^3 ≤
    2 * c^2 * K * M / (M + c * (D / 2))^3 := h0
  have h0_poly :
    2 * c^2 * K * M * (M + c * (D / 2))^3 ≤
    2 * c^2 * K * M * (M + c * D)^3 := by
    rwa [div_le_div_iff₀ h_den_full_pos h_den_half_pos] at h0_le
  have h_goal_poly :
    4 * c^2 * K * M * (M + c * (D / 2))^3 ≤
    4 * c^2 * K * M * (M + c * D)^3 := by
    nlinarith [h0_poly]
  rwa [div_le_div_iff₀ h_den_full_pos h_den_half_pos]

/-! ## Symmetric Stationary m Certificate Path

The complete composition for identical pools: symmetric stationary m +
derivative bracket + continuous upper value + strong concavity =>
tightest certified radius.

Delegates to `asymmetric_stationary_m_certificate_path` with
`m = symmetric_stationary_m K M c D`.
-/

/-- **Symmetric Stationary m Certificate Path**: for identical pools, if
    the symmetric stationary m is used as the strong concavity parameter,
    and the derivative bracket contains `b*`, and the continuous upper
    value and production value are recomputed, then
    `|argmax - b*| <= sqrt(2 * tau_upper / m_symmetric)`.

    This is the tightest certified radius for the symmetric subfamily,
    since `m_symmetric >= m_interval >= m_endpoint`. -/
theorem symmetric_stationary_m_certificate_path
    (K M c D lo hi b_star argmax tau_upper cont_star_upper prod_value : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hc : 0 < c)
    (hD : 0 < D)
    (h_lo_nn : 0 ≤ lo) (h_hi_le_D : hi ≤ D) (h_lo_le_hi : lo ≤ hi)
    (h_b_star_nn : 0 ≤ b_star) (h_b_star_le_D : b_star ≤ D)
    (h_argmax_nn : 0 ≤ argmax) (h_argmax_le_D : argmax ≤ D)
    (h_deriv_strict_decreasing :
      ∀ x y : ℝ, x < y →
        deriv (splitFunctionCont K M c K M c D) x >
        deriv (splitFunctionCont K M c K M c D) y)
    (h_deriv_lo : deriv (splitFunctionCont K M c K M c D) lo ≥ 0)
    (h_deriv_hi : deriv (splitFunctionCont K M c K M c D) hi ≤ 0)
    (h_b_star_max : ∀ x : ℝ, 0 ≤ x → x ≤ D →
      splitFunctionCont K M c K M c D x ≤
      splitFunctionCont K M c K M c D b_star)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K M c K M c D x ≤
      splitFunctionCont K M c K M c D b_star -
        (symmetric_stationary_m K M c D / 2) * (x - b_star)^2)
    (h_cont_star_upper :
      cont_star_upper =
        cpmmOutputCont K M (c * hi) + cpmmOutputCont K M (c * (D - lo)))
    (h_prod_value :
      prod_value ≤ splitFunctionCont K M c K M c D argmax)
    (h_tau_upper : tau_upper = cont_star_upper - prod_value) :
    |argmax - b_star| ≤
      Real.sqrt (2 * tau_upper / symmetric_stationary_m K M c D) := by
  -- Delegate to the asymmetric stationary certificate path with m = symmetric m
  have hm_pos : 0 < symmetric_stationary_m K M c D := by
    show 0 < 4 * c^2 * K * M / (M + c * (D / 2))^3
    positivity
  exact asymmetric_stationary_m_certificate_path
    K M c K M c D lo hi b_star argmax
    (symmetric_stationary_m K M c D) tau_upper cont_star_upper prod_value
    (le_of_lt hK) hM (le_of_lt hc)
    (le_of_lt hK) hM (le_of_lt hc)
    hD
    h_lo_nn h_hi_le_D h_lo_le_hi
    h_b_star_nn h_b_star_le_D
    h_argmax_nn h_argmax_le_D
    h_deriv_strict_decreasing h_deriv_lo h_deriv_hi
    h_b_star_max
    hm_pos h_strong_concave
    h_cont_star_upper h_prod_value h_tau_upper

/-! ## Stationary Radius Dominance

The stationary m gives a radius that is at most the interval and endpoint
radii, since m_stationary >= m_interval >= m_endpoint.
-/

/-- **Stationary Radius Dominates Interval Radius**: if
    `m_interval <= m_stationary` (both positive), then the stationary
    radius is at most the interval radius.

    This follows from `interval_radius_le_endpoint_radius` applied to the
    interval-vs-stationary pair. -/
theorem stationary_radius_le_interval_radius
    (tau m_interval m_stationary : ℝ)
    (htau_nn : 0 ≤ tau)
    (hm_interval : 0 < m_interval)
    (hm_stationary : 0 < m_stationary)
    (hm_dom : m_interval ≤ m_stationary) :
    Real.sqrt (2 * tau / m_stationary) ≤ Real.sqrt (2 * tau / m_interval) := by
  exact interval_radius_le_endpoint_radius
    tau m_interval m_stationary htau_nn hm_interval hm_stationary hm_dom

/-- **Stationary Radius Dominates Endpoint Radius**: if
    `m_endpoint <= m_stationary` (both positive), then the stationary
    radius is at most the endpoint radius.

    This is the transitive composition of endpoint-to-interval and
    interval-to-stationary dominance. -/
theorem stationary_radius_le_endpoint_radius
    (tau m_endpoint m_stationary : ℝ)
    (htau_nn : 0 ≤ tau)
    (hm_endpoint : 0 < m_endpoint)
    (hm_stationary : 0 < m_stationary)
    (hm_dom : m_endpoint ≤ m_stationary) :
    Real.sqrt (2 * tau / m_stationary) ≤ Real.sqrt (2 * tau / m_endpoint) := by
  exact interval_radius_le_endpoint_radius
    tau m_endpoint m_stationary htau_nn hm_endpoint hm_stationary hm_dom

/-! ## Complete Stationary Certificate Soundness

The complete soundness theorem with stationary m: all certificate conditions
hold (derivative bracket, stationary curvature, recomputed values) => the
actual distance is bounded by the tightest certified radius.
-/

/-- **Complete Asymmetric Stationary Certificate Soundness**: if all
    certificate conditions hold with the asymmetric stationary curvature
    providing `m`, then
    `|argmax - b*| <= sqrt(2 * tau_upper / m)`.

    This is the main soundness theorem for the exact interval certificate
    checker with stationary m source. It is the tightest form of the
    certificate, since `m_stationary >= m_interval >= m_endpoint`. -/
theorem complete_stationary_certificate_soundness
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
    |argmax - b_star| ≤ Real.sqrt (2 * tau_upper / m) := by
  exact asymmetric_stationary_m_certificate_path
    K0 M0 c0 K1 M1 c1 D lo hi b_star argmax m tau_upper cont_star_upper prod_value
    hK0 hM0 hc0 hK1 hM1 hc1 hD
    h_lo_nn h_hi_le_D h_lo_le_hi
    h_b_star_nn h_b_star_le_D
    h_argmax_nn h_argmax_le_D
    h_deriv_strict_decreasing h_deriv_lo h_deriv_hi
    h_b_star_max
    hm h_strong_concave
    h_cont_star_upper h_prod_value h_tau_upper
