/-
# CPMM Window Algebra and Generic Lipschitz Increment

This file proves two algebraic identities and one generic Lipschitz increment.
It does NOT prove a conservation law, a product frontier, a monotonicity
result, or any theorem connecting the Lipschitz increment to the stateful
CPMM attack gain. The stateful attack side is empirical only and lives in
the Python test suite.

## What Is Proven Here

1. `cpmm_concavity_param_formula`: algebraic identity `2*K/M^2 = 2*(K/M)/M`.
2. `cpmm_window_M_relationship`: algebraic identity `sqrt(2*L/m) = sqrt(M)`
   when `L = K/M` and `m = 2*K/M^2`. This is the epsilon=0 case. The
   production argmax window is `sqrt(2*(L+ε)/m)` (see DiscreteArgmaxProximity),
   which is strictly larger when ε > 0.
3. `lipschitz_increment_bound`: for any L-Lipschitz function f,
   `f(a_A) - f(0) <= L * a_A`. This is a generic single-input increment
   theorem. It does NOT bound the stateful CPMM attack gain
   `out_B_without_A - out_B_with_A`, which involves a pool state change
   (M -> M + a_A*gamma) and is a different quantity.

## What Is NOT Proven Here

- No conservation law: there is no theorem linking the window size to the
  adversarial gain via a shared product or frontier.
- No monotonicity: no theorem states that gain decreases with M.
- No stateful attack bound: the Lipschitz increment `f(a_A)-f(0)` is a
  different quantity from the stateful attack gain. The empirical test
  suite checks `simulate_sacrifice_gain <= L*a_A` on a seeded corpus, but
  this is empirical replay, not a Lean-proven theorem.
- The second-order concavity approximation `(m/2)*a_A*(a_A+2*a_B)` is
  FALSIFIED empirically and is NOT included as a theorem.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/ConcavityConservationLaw.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.DiscreteArgmaxProximity
import Proofs.CpmmSplitConcavity

open Real

/-- **Lipschitz Increment Bound**: For an `L`-Lipschitz function, the
    single-input increment from `0` to `a_A` is bounded by `L * a_A`.

    This is a generic single-input increment theorem. It does NOT bound the
    stateful CPMM attack gain `out_B_without_A - out_B_with_A`, which involves
    a pool state change and is a different quantity. The empirical test suite
    checks the stateful gain against `L*a_A` on a seeded corpus, but that
    bridge is empirical, not formalized here.

    The second-order concavity expression `(m/2) * a_A * (a_A + 2*a_B)` is
    not included as a theorem because the stateful-attack empirical suite
    falsifies it as a universal bound. -/
theorem lipschitz_increment_bound
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

   `lipschitz_increment_bound` proves a GENERIC Lipschitz increment:
   `f(a_A) - f(0) <= L * a_A` for any L-Lipschitz function f.

   It does NOT prove that the actual stateful CPMM attack gain
   `out_B_without_A - out_B_with_A` is bounded by `L * a_A`.
   The connection between the Lipschitz increment and the stateful
   attack gain is verified EMPIRICALLY in `concavity_conservation_law_test.py`,
   not formalized in Lean.

   The concavity-based gain bound `(m/2)*a_A*(a_A+2*a_B)` is FALSIFIED
   empirically (ratio up to 1.82x) and is NOT included as a Lean theorem. -/

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

/-- **CPMM Window-M Relationship (epsilon=0 case)**: For CPMM with spot
    price `L = K/M` and concavity parameter `m = 2*K/M^2`, the window
    `sqrt(2*L/m)` simplifies to `sqrt(M)`.

    This is the epsilon=0 algebraic identity. The production argmax window
    from `DiscreteArgmaxProximity` is `sqrt(2*(L+ε)/m)`, which is strictly
    larger when ε > 0. This theorem proves only the epsilon=0 case.

    This is an ALGEBRAIC IDENTITY, not a conservation theorem. It does NOT
    prove a monotonicity result, an optimal frontier, or a connection to
    adversarial gain. The Lipschitz product `sqrt(M) * L * a_A` is
    INCREASING in M, NOT decreasing. The empirical observation that actual
    stateful gain decreases with M is not formalized here. -/
theorem cpmm_window_M_relationship
    (K M : ℝ)
    (hK : K > 0) (hM : M > 0)
    : Real.sqrt (2 * (K / M) / (2 * K / M^2)) = Real.sqrt M := by
  have h_m : 2 * (K / M) / (2 * K / M^2) = M := by
    field_simp
  rw [h_m]
