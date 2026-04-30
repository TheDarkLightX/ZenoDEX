import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# MEV Resistance Bound for Batch Clearing

Quantifies the integer-safe consequences of a sealed-batch dilution model.

Model boundary:
- `base_profit` is the single-intent extractable value.
- batch profit is modeled as `base_profit / n`.
- the file proves the arithmetic reduction consequences of that model.

It does not prove that every concrete auction or deployment realizes the
`1 / n` information-dilution premise; that remains a runtime/mechanism
instantiation obligation.
-/

namespace Proofs
namespace MEVResistanceBound

/-! ## Reduction function and basic properties -/

/-- MEV reduction numerator: n - 1 out of n is eliminated. -/
def reductionNum (n : Nat) : Nat := n - 1

/-- MEV reduction is 0 for a single intent. -/
theorem reduction_single : reductionNum 1 = 0 := by
  simp [reductionNum]

/-- MEV reduction numerator is strictly less than n, so finite batches never eliminate 100%. -/
theorem reduction_lt_denom (n : Nat) (hn : 0 < n) : reductionNum n < n := by
  simp [reductionNum]
  omega

/-- Larger batches have higher reduction fractions, encoded by cross multiplication. -/
theorem reduction_mono (n₁ n₂ : Nat) (h : n₁ <= n₂) (hn₁ : 0 < n₁) :
    reductionNum n₁ * n₂ <= reductionNum n₂ * n₁ := by
  simp only [reductionNum]
  cases n₁ with
  | zero => omega
  | succ a =>
    cases n₂ with
    | zero => omega
    | succ b =>
      simp only [Nat.succ_sub_one]
      nlinarith

/-! ## Sandwich profit bound under the dilution model -/

/-- Batch-mode attacker profit is diluted by batch size: profit(n) = floor(base_profit / n).
    Equivalently, `n * profit_n <= base_profit`. -/
theorem profit_dilution (base_profit n : Nat) :
    (base_profit / n) * n <= base_profit :=
  Nat.div_mul_le_self base_profit n

/-- Cross-multiplied MEV elimination bound:
    `(base_profit - attacker_profit) * n >= base_profit * (n - 1)`.
    This is the integer-safe form of elimination rate at least `(n - 1) / n`. -/
theorem eliminated_mev_cross (base_profit n : Nat) (hn : 0 < n) :
    (base_profit - base_profit / n) * n >= base_profit * (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    have h1 := Nat.div_mul_le_self base_profit (m + 1)
    have h2 : base_profit / (m + 1) <= base_profit := Nat.div_le_self base_profit (m + 1)
    have h3 : (base_profit - base_profit / (m + 1)) * (m + 1) +
              base_profit / (m + 1) * (m + 1) = base_profit * (m + 1) := by
      rw [← add_mul, Nat.sub_add_cancel h2]
    show (base_profit - base_profit / (m + 1)) * (m + 1) >= base_profit * m
    have h4 : base_profit * (m + 1) = base_profit * m + base_profit := by ring
    rw [h4] at h3
    omega

/-! ## Composition: batch size determines protection level -/

/-- Doubling the batch size does not increase the remaining modeled MEV. -/
theorem double_batch_does_not_increase_mev (base_profit n : Nat) (_hn : 0 < n) :
    base_profit / (2 * n) <= base_profit / n := by
  apply Nat.div_le_div_left
  · omega
  · omega

/-- The reduction numerator is always bounded by the denominator. -/
theorem reduction_bounded (n : Nat) (_hn : 0 < n) :
    reductionNum n <= n := by
  simp [reductionNum]

/-- Reduction numerator is positive for batches with at least two intents. -/
theorem reduction_positive (n : Nat) (hn : 2 <= n) :
    0 < reductionNum n := by
  simp [reductionNum]
  omega

/-! ## Threshold theorems -/

/-- Batch size 10 has reduction numerator 9, i.e. a 9/10 reduction in the model. -/
theorem threshold_90pct : reductionNum 10 = 9 := by
  simp [reductionNum]

/-- Batch size 100 has reduction numerator 99, i.e. a 99/100 reduction in the model. -/
theorem threshold_99pct : reductionNum 100 = 99 := by
  simp [reductionNum]

/-- For target numerator `t` over denominator `d`, if `t < d`, batch size `d`
    achieves at least that numerator under cross multiplication. -/
theorem target_batch_size (t d : Nat) (ht : t < d) :
    reductionNum d * d >= t * d := by
  simp [reductionNum]
  have : d - 1 >= t := by omega
  nlinarith

/-! ## Non-vacuity witnesses -/

/-- Concrete: batch of 5, base profit 1000.
    Attacker gets at most 200; reduction eliminates at least 800. -/
theorem witness_batch5 :
    1000 / 5 = 200 /\ 1000 - 1000 / 5 = 800 /\ reductionNum 5 = 4 := by
  simp [reductionNum]

/-- Concrete: batch of 1 has no modeled protection. -/
theorem witness_single_no_protection :
    1000 / 1 = 1000 /\ 1000 - 1000 / 1 = 0 /\ reductionNum 1 = 0 := by
  simp [reductionNum]

/-- Concrete: batch 10 has a stronger modeled reduction fraction than batch 5. -/
theorem witness_mono_5_10 :
    reductionNum 5 * 10 <= reductionNum 10 * 5 := by
  simp [reductionNum]

/-- The reduction numerator identity for nonzero batch sizes. -/
theorem witness_reduction_num_identity :
    forall n : Nat, 1 <= n -> reductionNum n + 1 = n := by
  intro n hn
  simp [reductionNum]
  omega

end MEVResistanceBound
end Proofs
