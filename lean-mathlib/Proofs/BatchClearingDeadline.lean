import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Batch Clearing Deadline Scheduling: Formal Proofs

This file formalizes key properties of the deadline scheduling reformulation
for CPMM batch clearing A-optimization.

## Key Insight

For a CPMM pool with reserves (R_in, R_out) and a SWAP_EXACT_IN intent with
`amount_in` and `min_amount_out`, under the constant-k approximation
(k = R_in * R_out = k_0), the swap has a closed-form **deadline**: the maximum
cumulative gross_in of preceding swaps before the intent's output drops below
its effective minimum output.

## Main Theorems

1. `deadline_discriminant_positive`: The discriminant of the deadline quadratic
   is strictly positive when all inputs are positive, guaranteeing a unique
   positive root.

2. `deadline_quadratic_negative_at_zero`: The deadline quadratic is negative at
   x=0. Under the continuous approximation, this is one side of the root
   argument for the deadline boundary.

3. `constant_k_monotone`: Adding input to R_in (before removing output) increases
   the product R_in * R_out, supporting the conservativeness of the constant-k
   approximation.

4. `effective_min_at_least_one`: The effective minimum output is at least 1,
   capturing the CPMM kernel's zero-output rejection (NK-001).

## Notation

- `R_in₀`, `R_out₀`: initial reserves
- `k₀ = R_in₀ * R_out₀`: initial constant product
- `net_in`: effective input after fee = amount_in - fee
- `m`: effective min_amount_out = max(min_amount_out, 1)
-/

namespace TauSwap.BatchDeadline

/-- The constant product k₀ = R_in₀ * R_out₀ -/
abbrev K0 (R_in₀ R_out₀ : ℕ) : ℕ := R_in₀ * R_out₀

/-- The discriminant of the deadline quadratic: (net_in * m)² + 4 * m * net_in * k₀ -/
def discriminant (net_in m k₀ : ℕ) : ℕ :=
  (net_in * m) * (net_in * m) + 4 * m * net_in * k₀

/-- The deadline quadratic evaluated at x:
    m * x² + net_in * m * x - net_in * k₀ -/
def deadline_quadratic (net_in m k₀ x : ℤ) : ℤ :=
  m * x * x + net_in * m * x - net_in * k₀

/-- The discriminant is non-negative (sum of non-negative terms). -/
theorem discriminant_nonneg (net_in m k₀ : ℕ) :
    0 ≤ (discriminant net_in m k₀ : ℤ) := by
  unfold discriminant
  positivity

/-- The discriminant is strictly positive when net_in, m, and k₀ are all positive.

    This guarantees the deadline quadratic has two distinct real roots.
    Since the product of roots is -net_in * k₀ / m < 0, exactly one root is
    positive, giving a unique deadline.
-/
theorem deadline_discriminant_positive
    (net_in m k₀ : ℕ) (h_net : net_in > 0) (h_m : m > 0) (h_k : k₀ > 0) :
    0 < (discriminant net_in m k₀ : ℤ) := by
  unfold discriminant
  positivity

/-- The deadline quadratic is negative at x = 0.

    q(0) = m * 0 + net_in * m * 0 - net_in * k₀ = -net_in * k₀ < 0

    Under the continuous approximation, the swap produces enough output at
    R_in' = 0. The positive root is where feasibility flips to infeasibility.
-/
theorem deadline_quadratic_negative_at_zero
    (net_in m k₀ : ℕ) (h_net : net_in > 0) (h_k : k₀ > 0) :
    deadline_quadratic net_in m k₀ 0 < 0 := by
  unfold deadline_quadratic
  have : (net_in * k₀ : ℤ) > 0 := by positivity
  linarith

/-- Adding input to R_in (before removing output) increases R_in * R_out.

    This supports the conservativeness of the constant-k approximation:
    in the actual CPMM, fees stay in the pool, so k_after >= k_before.
    The full post-swap invariant (k_after >= k_before after output removal)
    is enforced by the kernel (`cpmm_swap_v8.py` raises if k_after < k_before).
    Here we prove the simpler pre-output-removal monotonicity.
-/
theorem constant_k_monotone
    (R_in R_out amount_in : ℕ) (_h_Rout : R_out > 0) (h_amount : amount_in > 0) :
    R_in * R_out ≤ (R_in + amount_in) * R_out := by
  have : R_in ≤ R_in + amount_in := by omega
  nlinarith [h_amount, this]

/-- The effective minimum output is at least 1.

    The CPMM kernel rejects amount_out <= 0 with ValueError, so the effective
    minimum output is max(min_amount_out, 1), not min_amount_out.
    This is the key insight from NK-001.
-/
theorem effective_min_at_least_one (min_amount_out : ℕ) :
    max min_amount_out 1 ≥ 1 := by
  exact le_max_right _ _

/-- If min_amount_out = 0, the effective minimum is 1 (not 0).

    This captures the CPMM kernel's zero-output rejection (NK-001).
-/
theorem effective_min_of_zero :
    max (0 : ℕ) 1 = 1 := by
  simp

end TauSwap.BatchDeadline
