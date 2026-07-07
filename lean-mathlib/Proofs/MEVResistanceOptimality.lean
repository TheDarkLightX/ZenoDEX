import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# MEV Quota Arithmetic Tightness

This file proves the arithmetic core of a `1/n` MEV quota model:
`floor(base_profit / n)` is the largest natural number whose n-fold quota does
not exceed `base_profit`.

It does not prove a mechanism-wide optimality theorem for sealed-bid batch
auctions. A separate game model must first prove the obligation
`attacker_profit * n ≤ base_profit`; then this file turns that obligation into
the tight natural-number floor bound.

## Main Results

1. **Quota Witness** (`quota_floor_witness`): `floor(base_profit / n)` fits
   under the n-fold quota, while the next integer does not.

2. **Quota Upper Bound** (`quota_upper_bound_from_mul_le`): Any natural number
   satisfying `p * n ≤ base_profit` is at most `base_profit / n`.

3. **Tightness** (`quota_floor_bound_is_tight`): The fitting quota is exactly
   the floor quotient.

4. **No Smaller Quota Bound** (`no_quota_bound_below_floor`): Any claimed
   bound below the floor quotient is refuted by the floor witness.

5. **Residual Arithmetic** (`quota_elimination_floor_residual_nontrivial`):
   The eliminated amount and residual floor quotient satisfy the expected
   cross-multiplied arithmetic relation.

6. **Minimum Denominator** (`quota_min_batch_for_exact_fraction_target`):
   The cross-multiplied target `(n-1)/n ≥ (d-1)/d` fails for `n < d`.

This file is proof evidence for quota arithmetic only. It should not be cited
as evidence that every DEX mechanism has a universal `1/n` MEV lower bound.
-/

namespace Proofs
namespace MEVResistanceOptimality

/-! ## Section 1: Quota Witness -/

/-- The natural-number floor quotient is the exact quota witness. -/
theorem quota_floor_witness (base_profit n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p = base_profit / n ∧
      p * n ≤ base_profit ∧
      (p + 1) * n > base_profit := by
  use base_profit / n
  constructor
  · rfl
  constructor
  · exact Nat.div_mul_le_self base_profit n
  have hmod : base_profit % n < n := Nat.mod_lt base_profit hn
  have hdiv : n * (base_profit / n) + base_profit % n = base_profit :=
    Nat.div_add_mod base_profit n
  have hdiv' : base_profit / n * n + base_profit % n = base_profit := by
    rw [mul_comm]; exact hdiv
  calc (base_profit / n + 1) * n
      = base_profit / n * n + n := by ring
    _ > base_profit / n * n + base_profit % n := by omega
    _ = base_profit := hdiv'

/-! ## Section 2: Quota Upper Bound -/

/-- Any `p` whose n-fold quota fits under `base_profit` is at most the floor
    quotient. -/
theorem quota_upper_bound_from_mul_le (base_profit n p : ℕ) (hn : 0 < n) :
    p * n ≤ base_profit →
    p ≤ base_profit / n := by
  intro h_bound
  exact (Nat.le_div_iff_mul_le hn).mpr h_bound

/-! ## Section 3: Tightness — The Bounds Match -/

/-- The floor quotient fits, the next integer does not, and every fitting quota
    is below it. -/
theorem quota_floor_bound_is_tight (base_profit n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p = base_profit / n ∧
      p * n ≤ base_profit ∧
      (p + 1) * n > base_profit ∧
      ∀ q : ℕ, q * n ≤ base_profit → q ≤ p := by
  use base_profit / n
  constructor
  · rfl
  constructor
  · exact Nat.div_mul_le_self base_profit n
  constructor
  · have hmod : base_profit % n < n := Nat.mod_lt base_profit hn
    have hdiv : n * (base_profit / n) + base_profit % n = base_profit :=
      Nat.div_add_mod base_profit n
    have hdiv' : base_profit / n * n + base_profit % n = base_profit := by
      rw [mul_comm]; exact hdiv
    calc (base_profit / n + 1) * n
        = base_profit / n * n + n := by ring
      _ > base_profit / n * n + base_profit % n := by omega
      _ = base_profit := hdiv'
  · intro q hq
    exact (Nat.le_div_iff_mul_le hn).mpr hq

/-! ## Section 4: No Smaller Quota Bound -/

/-- Any claimed quota cap below the floor quotient is refuted by the floor
    witness. -/
theorem no_quota_bound_below_floor (base_profit n q : ℕ) (_hn : 0 < n)
    (h_q_below : q < base_profit / n) :
    ∃ attacker_profit : ℕ,
      attacker_profit = base_profit / n ∧
      attacker_profit > q ∧
      attacker_profit * n ≤ base_profit := by
  refine ⟨base_profit / n, rfl, h_q_below, Nat.div_mul_le_self base_profit n⟩

/-! ## Section 5: Residual Arithmetic -/

/-- Arithmetic residual property for the nontrivial floor quotient case. -/
theorem quota_elimination_floor_residual_nontrivial (base_profit n : ℕ)
    (_hn : 0 < n) (h_base : n ≤ base_profit) :
    (base_profit - base_profit / n) * n ≥ base_profit * (n - 1) ∧
    ∀ (eliminated : ℕ),
      eliminated ≤ base_profit →
      eliminated > base_profit - base_profit / n →
      base_profit - eliminated < base_profit / n := by
  constructor
  · cases n with
    | zero => omega
    | succ m =>
      have h1 := Nat.div_mul_le_self base_profit (m + 1)
      have h2 : base_profit / (m + 1) ≤ base_profit :=
        Nat.div_le_self base_profit (m + 1)
      have h3 : (base_profit - base_profit / (m + 1)) * (m + 1) +
                base_profit / (m + 1) * (m + 1) = base_profit * (m + 1) := by
        rw [← add_mul, Nat.sub_add_cancel h2]
      show (base_profit - base_profit / (m + 1)) * (m + 1) ≥ base_profit * m
      have h4 : base_profit * (m + 1) = base_profit * m + base_profit := by ring
      rw [h4] at h3
      omega
  · intro eliminated h_elim_le h_elim
    have h_bpn_le : base_profit / n ≤ base_profit := Nat.div_le_self base_profit n
    have h_sub : base_profit - (base_profit - base_profit / n) = base_profit / n := by
      rw [Nat.sub_sub_self h_bpn_le]
    have h_elim_lt : base_profit - eliminated < base_profit - (base_profit - base_profit / n) := by
      omega
    calc base_profit - eliminated
      < base_profit - (base_profit - base_profit / n) := h_elim_lt
    _ = base_profit / n := h_sub

/-! ## Section 6: Concrete Witnesses

Concrete numerical witnesses for quota arithmetic.
-/

/-- Witness: denominator 10, base value 1000. -/
theorem witness_optimality_batch10 :
    1000 / 10 = 100 ∧
    1000 - 1000 / 10 = 900 ∧
    (100 + 1) * 10 > 1000 ∧
    ∀ q, q * 10 ≤ 1000 → q ≤ 100 := by
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · intro q hq
    have : q ≤ 1000 / 10 := (Nat.le_div_iff_mul_le (by omega : 0 < 10)).mpr hq
    omega

/-- Witness: denominator 100, base value 10000. -/
theorem witness_optimality_batch100 :
    10000 / 100 = 100 ∧
    10000 - 10000 / 100 = 9900 ∧
    (100 + 1) * 100 > 10000 ∧
    ∀ q, q * 100 ≤ 10000 → q ≤ 100 := by
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · intro q hq
    have : q ≤ 10000 / 100 := (Nat.le_div_iff_mul_le (by omega : 0 < 100)).mpr hq
    omega

/-- Witness: denominator 2, base value 100. -/
theorem witness_optimality_batch2 :
    100 / 2 = 50 ∧
    100 - 100 / 2 = 50 ∧
    (50 + 1) * 2 > 100 ∧
    ∀ q, q * 2 ≤ 100 → q ≤ 50 := by
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · intro q hq
    have : q ≤ 100 / 2 := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr hq
    omega

/-! ## Section 7: Asymptotic Optimality

As denominator n grows, the arithmetic residual `base_profit / n` decreases.
-/

/-- The floor residual decreases as the denominator grows. -/
theorem residual_mev_decreases (base_profit n₁ n₂ : ℕ)
    (_h_base : 0 < base_profit) (h₁ : 0 < n₁) (_h₂ : 0 < n₂) (h : n₁ ≤ n₂) :
    base_profit / n₂ ≤ base_profit / n₁ := by
  have h_bound : base_profit / n₂ * n₁ ≤ base_profit := by
    calc base_profit / n₂ * n₁
        ≤ base_profit / n₂ * n₂ := Nat.mul_le_mul_left _ h
      _ ≤ base_profit := Nat.div_mul_le_self base_profit n₂
  exact (Nat.le_div_iff_mul_le h₁).mpr h_bound

/-- Elementary denominator identity for `(n-1)/n`. -/
theorem reduction_approaches_one (n : ℕ) (_hn : 0 < n) :
    n - 1 < n ∧
    n - (n - 1) = 1 := by
  constructor
  · omega
  · omega

/-- Cross-multiplied denominator target: `(n-1)/n ≥ (d-1)/d` implies
    `n ≥ d`, so any `n < d` fails the target. -/
theorem quota_min_batch_for_exact_fraction_target (d : ℕ) (_hd : 0 < d) :
    (d - 1) * d ≥ (d - 1) * d ∧
    ∀ n : ℕ, 0 < n → n < d → (n - 1) * d < (d - 1) * n := by
  constructor
  · exact le_rfl
  intro n hn_pos hn
  cases n with
  | zero => omega
  | succ a =>
    cases d with
    | zero => omega
    | succ b =>
      simp only [Nat.succ_sub_one]
      have : a < b := by omega
      nlinarith

end MEVResistanceOptimality
end Proofs
