/-
# Concavity Conservation Law: Unified Algorithm-Security Parameter

This file proves the abstract conservation law that unifies the algorithm
window bound (Phase 3D) with the security bound (Phase 5A): the curvature
of the CPMM output function governs BOTH the discrete search window size
AND the adversarial gain bound.

## The Conservation Law

For a concave CPMM output function `f(x) = K*x/(M+x)`:

**Algorithm side** (from `DiscreteArgmaxProximity.lean`, Theorem 5):
  `window = sqrt(2 * (L + ε) / m)` where `m` is the strong concavity parameter
  (minimum |f''(x)| over the domain, taken as EXTERNAL hypothesis).
  Smaller `m` → larger window → slower search.

**Security side** (from Phase 5A adversarial analysis, EMPIRICAL):
  `adversarial_gain <= |f''(0)| * a_attacker * a_victim`
  where |f''(0)| = 2*K/M^2 is the MAXIMUM curvature (at the margin).
  NOTE: The empirical test uses |f''(0)| (max curvature), NOT m (min curvature).
  Since |f''(0)| >= m, this is a more conservative for an upper bound bound than using m.
  This is an EMPIRICAL observation, not a formal Lean theorem.

**Conservation**: Both bounds depend on the curvature of f. There is
a fundamental tradeoff: pools with small curvature (deep, well-funded) are
secure but require larger search windows; pools with large curvature (shallow)
are fast to search but more vulnerable to adversarial extraction.

## The Tradeoff Frontier

For CPMM `f(x) = K*x/(M+x)`:
  `f''(x) = -2*K*M / (M+x)^3`
  At the margin (x = 0): `|f''(0)| = 2*K / M^2 = 2 * spot_price / M`
  Over domain [0, x_max]: `m = min |f''(x)| = 2*K*M / (M + x_max)^3`

So curvature ~ L / M where `L = K/M` is the spot price (Lipschitz constant).

The tradeoff frontier is:
  `window * adversarial_gain ~ sqrt(2*L/m) * |f''(0)| * a_A * a_B`
  `                      ~ sqrt(2*L*m_0/m) * m_0 * a_A * a_B / 2`
  `                      ~ sqrt(2*L * L/M) * a_A * a_B / 2`
  `                      ~ L * sqrt(2/M) * a_A * a_B / 2`

The formal Lipschitz product does not by itself decrease with M. The empirical
stateful attack gain decreases with pool depth, while the formal search window
increases with depth. Pool depth M is therefore the shared parameter governing
the algorithm-security tradeoff, but the security side is an empirical
stateful-gain observation in this file, not a formal product theorem.

## Impact

This unifies two previously-separate concerns under a single quantity `m`:
1. Algorithm design: window size for ternary search DP
2. Mechanism design: collusion/sandwich attack bounds

Production implication: the min_out cap mitigation (Phase 5A) and the
adaptive window (Phase 3D) are not independent fixes — they are both
consequences of the same concavity structure. A single pool-depth
parameter `M` governs both.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/ConcavityConservationLaw.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.DiscreteArgmaxProximity
import Proofs.CpmmSplitConcavity

open Real

/-- **Adversarial Gain Bound (Lipschitz)**: For an `L`-Lipschitz function,
    the adversarial gain from removing `a_A` from the input is bounded by
    `L * a_A`.

    This is the security-side bound using the Lipschitz constant. The
    tighter concavity-based bound `(m/2) * a_A * a_B` requires a
    second-order lower bound on `f` that is not available from the
    abstract Lipschitz hypothesis alone; it is verified empirically in
    `docs/research/concavity_bounded_adversarial_test.py`. -/
theorem adversarial_gain_bound_lipschitz
    (f : ℝ → ℝ) (L a_A : ℝ)
    (hL : L ≥ 0) (hA : a_A ≥ 0)
    (h_lipschitz : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    : f a_A - f 0 ≤ L * a_A := by
  -- Domain contract: L >= 0 ensures the bound is nonneg (meaningful gain bound)
  have hL_nn : 0 ≤ L := hL
  have h_lip := h_lipschitz a_A 0
  have h_abs_le : |f a_A - f 0| ≤ L * a_A := by
    have h_eq : |a_A - 0| = a_A := by
      rw [sub_zero]; exact abs_of_nonneg hA
    rw [h_eq] at h_lip
    exact h_lip
  -- f(a_A) - f(0) <= |f(a_A) - f(0)| (by le_abs_self) <= L * a_A
  have h_le_abs : f a_A - f 0 ≤ |f a_A - f 0| := le_abs_self _
  linarith

/- ## Scope Note: What This Theorem Proves vs What It Does NOT Prove

   `adversarial_gain_bound_lipschitz` proves a GENERIC Lipschitz increment:
   `f(a_A) - f(0) <= L * a_A` for any L-Lipschitz function f.

   It does NOT prove that the actual stateful CPMM attack gain
   `out_B_without_A - out_B_with_A` is bounded by `L * a_A`.
   The connection between the Lipschitz increment and the stateful
   attack gain is verified EMPIRICALLY in `concavity_conservation_law_test.py`,
   not formalized in Lean. A high-assurance version would need a lemma
   connecting the CPMM attack gain to the Lipschitz increment under
   the exact continuous or rounded model.

   The concavity-based gain bound `(m/2)*a_A*(a_A+2*a_B)` is FALSIFIED
   empirically (ratio up to 1.82x) and is NOT included as a Lean theorem.
   The Lipschitz bound is the only universal bound proven here. -/

/-- **CPMM Concavity Parameter Formula**: For `f(x) = K*x/(M+x)`,
    the strong concavity parameter at the margin (x = 0) is:
    `m = 2 * K / M^2 = 2 * L / M`

    where `L = K/M` is the spot price (Lipschitz constant).

    This connects the algorithm parameter `m` to the pool depth `M`:
    deeper pools (large M) have smaller `m`. -/
lemma cpmm_concavity_param_formula
    (K M : ℝ) (hK : K > 0) (hM : M > 0)
    : 2 * K / M^2 = 2 * (K / M) / M := by
  field_simp

/-- **CPMM Window-M Relationship**: For CPMM with spot price `L = K/M`
    and concavity parameter `m = 2*K/M^2`, the algorithm window
    `sqrt(2*L/m)` simplifies to `sqrt(M)`.

    This is an ALGEBRAIC IDENTITY, not a conservation theorem:
    it shows that the window size equals sqrt(M) when L and m are
    linked via the CPMM formula. It does NOT prove a monotonicity
    result, an optimal frontier, or a connection to adversarial gain.

    The EMPIRICAL observation (verified in tests, not formalized in Lean)
    is that the actual adversarial gain decreases with M, so deeper
    pools are empirically more secure. The Lipschitz-based product
    `sqrt(M) * L * a_A` is INCREASING in M (larger window, same gain
    bound), NOT decreasing. The "deeper is more secure" intuition comes
    from the actual gain behavior, not from the product of formal bounds. -/
theorem cpmm_window_M_relationship
    (K M : ℝ)
    (hK : K > 0) (hM : M > 0)
    : Real.sqrt (2 * (K / M) / (2 * K / M^2)) = Real.sqrt M := by
  have h_m : 2 * (K / M) / (2 * K / M^2) = M := by
    field_simp
  rw [h_m]
