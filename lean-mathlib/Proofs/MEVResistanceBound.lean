import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Batch-Size Dilution Arithmetic Envelope

This file packages arithmetic facts about the toy dilution family

  profit(n) = base_profit / n
  reduction(n) = 1 - 1/n

It does **not** derive this family from the DEX batch-clearing semantics,
intent structure, or clearing-price proofs. It is an arithmetic sidecar only.

Within that toy model:
- n=1: 0% reduction (single intent, fully sandwichable)
- n=2: 50% reduction
- n=10: 90% reduction
- n=100: 99% reduction

## Mathematical Model

We work with integer fractions to avoid rationals, always on positive
batch sizes `n > 0`:
- `profit(1)` = the single-intent MEV (denominator: 1)
- `profit(n)` = profit(1) / n (attacker's advantage diluted)
- `reduction(n) = (n - 1) / n` (fraction of MEV eliminated)

Key properties:
1. reduction is monotonically increasing in n
2. reduction(1) = 0 (no protection for single intent)
3. the rational-style reduction fraction `(n - 1) / n` is always strictly below 1
   at the numerator/denominator level; this does not prevent floor-rounded
   modeled profit from reaching 0 on small `base_profit`
4. For n₁ ≤ n₂: reduction(n₁) ≤ reduction(n₂)
-/

namespace Proofs
namespace MEVResistanceBound

/-! ## Reduction function and basic properties -/

/-- MEV reduction numerator: n - 1 out of n is eliminated. -/
def reductionNum (n : ℕ) : ℕ := n - 1

/-- MEV reduction is 0 for a single intent (no batch protection). -/
theorem reduction_single : reductionNum 1 = 0 := by
  simp [reductionNum]

/-- MEV reduction numerator is strictly less than n (never 100%). -/
theorem reduction_lt_denom (n : ℕ) (hn : 0 < n) : reductionNum n < n := by
  simp [reductionNum]
  omega

/-- Larger batches have higher reduction numerators. -/
theorem reduction_mono (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) (hn₁ : 0 < n₁) :
    reductionNum n₁ * n₂ ≤ reductionNum n₂ * n₁ := by
  simp only [reductionNum]
  -- Need: (n₁ - 1) * n₂ ≤ (n₂ - 1) * n₁
  -- Eliminate ℕ subtraction by case-splitting on successors
  cases n₁ with
  | zero => omega
  | succ a =>
    cases n₂ with
    | zero => omega
    | succ b =>
      -- Goal: a * (b + 1) ≤ b * (a + 1), i.e., a ≤ b
      simp only [Nat.succ_sub_one]
      nlinarith

/-! ## Toy profit bound -/

/-- In the toy dilution family `profit(n) = base_profit / n`,
    floor division implies `n * profit(n) ≤ base_profit` for `n > 0`. -/
theorem modeled_profit_dilution (base_profit n : ℕ) (_hn : 0 < n) :
    (base_profit / n) * n ≤ base_profit :=
  Nat.div_mul_le_self base_profit n

/-- Cross-multiplied elimination bound inside the same toy family:
    `(base_profit - profit(n)) * n ≥ base_profit * (n - 1)`. -/
theorem modeled_eliminated_profit_cross (base_profit n : ℕ) (hn : 0 < n) :
    (base_profit - base_profit / n) * n ≥ base_profit * (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    have h1 := Nat.div_mul_le_self base_profit (m + 1)
    have h2 : base_profit / (m + 1) ≤ base_profit := Nat.div_le_self base_profit (m + 1)
    have h3 : (base_profit - base_profit / (m + 1)) * (m + 1) +
              base_profit / (m + 1) * (m + 1) = base_profit * (m + 1) := by
      rw [← add_mul, Nat.sub_add_cancel h2]
    show (base_profit - base_profit / (m + 1)) * (m + 1) ≥ base_profit * m
    have h4 : base_profit * (m + 1) = base_profit * m + base_profit := by ring
    rw [h4] at h3
    omega

/-! ## Composition inside the toy family -/

/-- Doubling the batch size halves the remaining modeled profit up to floor rounding.
    Specifically, `2 * profit(2n) ≤ profit(n)` for all `n > 0`. -/
theorem double_batch_halves_modeled_profit (base_profit n : ℕ) (hn : 0 < n) :
    2 * (base_profit / (2 * n)) ≤ base_profit / n := by
  rw [Nat.le_div_iff_mul_le hn]
  have hmul : (base_profit / (2 * n)) * (2 * n) ≤ base_profit :=
    Nat.div_mul_le_self base_profit (2 * n)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- The reduction fraction (n-1)/n is always ≤ 1. -/
theorem reduction_bounded (n : ℕ) (_hn : 0 < n) :
    reductionNum n ≤ n := by
  simp [reductionNum]

/-- Reduction numerator is positive for n ≥ 2 (batch provides some protection). -/
theorem reduction_positive (n : ℕ) (hn : 2 ≤ n) :
    0 < reductionNum n := by
  simp [reductionNum]; omega

/-! ## Threshold theorems -/

/-- Witness: the reduction numerator at batch size 10 is 9, i.e. reduction(10) = 9/10. -/
theorem witness_reductionNum_10_eq_9 : reductionNum 10 = 9 := by
  simp [reductionNum]

/-- Witness: the reduction numerator at batch size 100 is 99, i.e. reduction(100) = 99/100. -/
theorem witness_reductionNum_100_eq_99 : reductionNum 100 = 99 := by
  simp [reductionNum]

/-- For any target reduction t/d (where t < d), batch size d is sufficient.
    This is only a sufficiency statement; smaller batch sizes may also work.
    Because reductionNum(d) = d - 1 ≥ t when d - 1 ≥ t, i.e., d > t. -/
theorem target_batch_size_sufficient (t d : ℕ) (ht : t < d) :
    reductionNum d * d ≥ t * d := by
  simp [reductionNum]
  -- (d - 1) * d ≥ t * d ← d - 1 ≥ t ← d > t ✓
  have : d - 1 ≥ t := by omega
  nlinarith

/-! ## Non-vacuity witnesses -/

/-- Concrete: batch of 5, base profit 1000.
    Attacker gets at most 200, reduction eliminates ≥ 800. -/
theorem witness_batch5 :
    1000 / 5 = 200 ∧ 1000 - 1000 / 5 = 800 ∧ reductionNum 5 = 4 := by
  simp [reductionNum]

/-- Concrete: batch of 1, full extraction (no protection). -/
theorem witness_single_no_protection :
    1000 / 1 = 1000 ∧ 1000 - 1000 / 1 = 0 ∧ reductionNum 1 = 0 := by
  simp [reductionNum]

/-- Concrete: monotonicity check — batch 10 is better than batch 5.
    reduction(5) = 4/5, reduction(10) = 9/10.
    Cross-multiply: 4 * 10 = 40 ≤ 9 * 5 = 45. -/
theorem witness_mono_5_10 :
    reductionNum 5 * 10 ≤ reductionNum 10 * 5 := by
  simp [reductionNum]

/-- Concrete halving witness inside the toy family: doubling batch size from 5 to 10
    cuts the integer remaining-profit bound by at least half. -/
theorem witness_double_batch_halves :
    2 * (1000 / (2 * 5)) ≤ 1000 / 5 := by
  native_decide

/-- Counterexample to any necessity reading of `target_batch_size_sufficient`:
    target 1/3 is already met by batch size 2 since 1/2 ≥ 1/3. -/
theorem witness_target_size_not_necessary :
    reductionNum 2 * 3 ≥ 1 * 2 := by
  simp [reductionNum]

/-- Arithmetic identity for the reduction numerator: `reductionNum n + 1 = n`
    on positive batch sizes. -/
theorem witness_reduction_identity :
    ∀ n : ℕ, 1 ≤ n → reductionNum n + 1 = n := by
  intro n hn
  simp [reductionNum]
  omega

/-- Floor division can eliminate the modeled profit completely on low-profit batches.
    This is why this file only packages the arithmetic toy family and does not claim
    a protocol-level "never fully eliminated" result. -/
theorem witness_modeled_profit_can_floor_to_zero :
    1 / 2 = 0 := by
  native_decide

end MEVResistanceBound
end Proofs
