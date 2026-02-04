import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Proofs.PerpFundingRateSafety

/-!
# Integer-rational bridge for perpetual computations

## Main results

* `int_emod_bounded`: Integer remainder: 0 ≤ a % d < d for d > 0.
* `int_div_conservative`: For a ≥ 0, d > 0: (a / d) * d ≤ a (floor rounds down).
* `int_single_div_gap`: For d > 0: a - (a / d) * d < d (error < divisor).
* `int_symmetric_div_gap`: |a / d + (-a) / d| ≤ 1 (budget-balance gap bounded).

## Key insight

The production kernel uses bounded integer arithmetic while Lean proofs work over ℚ.
Floor division in ℤ creates a gap of at most 1 unit compared to exact ℚ
division. For non-negative quantities, integer division is conservative
(rounds down), providing a built-in safety margin.
-/

namespace Proofs

namespace PerpIntegerBridge

/-- Integer remainder bounded: 0 ≤ a % d < d for d > 0.
    This is the fundamental bound that drives all gap estimates. -/
theorem int_emod_bounded (a d : ℤ) (hd : 0 < d) :
    0 ≤ a % d ∧ a % d < d :=
  ⟨Int.emod_nonneg a (ne_of_gt hd), Int.emod_lt_of_pos a hd⟩

/-- Integer division is conservative for non-negative values:
    (a / d) * d ≤ a when a ≥ 0 and d > 0. Floor division rounds down. -/
theorem int_div_conservative (a d : ℤ) (_ha : 0 ≤ a) (hd : 0 < d) :
    a / d * d ≤ a := by
  have h := Int.mul_ediv_add_emod a d
  have hmod := (int_emod_bounded a d hd).1
  nlinarith

/-- Single-division gap: a - (a / d) * d < d for d > 0.
    The error of one integer division operation is strictly less than d. -/
theorem int_single_div_gap (a d : ℤ) (hd : 0 < d) :
    a - a / d * d < d := by
  have h := Int.mul_ediv_add_emod a d
  have hmod := (int_emod_bounded a d hd).2
  nlinarith

/-- Symmetric division gap: |a / d + (-a) / d| ≤ 1 for d > 0.
    This bounds the budget-balance violation when computing symmetric
    funding payments via integer division. -/
theorem int_symmetric_div_gap (a d : ℤ) (hd : 0 < d) :
    |a / d + (-a) / d| ≤ 1 := by
  have := PerpFundingRateSafety.int_fdiv_neg_gap a d hd
  rcases this with h | h <;> simp [h]

/-! ## Non-vacuity witnesses -/

/-- Witness: integer remainder bounded (7 % 3 = 1, and 0 ≤ 1 < 3). -/
theorem witness_emod :
    0 ≤ (7 : ℤ) % 3 ∧ (7 : ℤ) % 3 < 3 := by native_decide

/-- Witness: integer division is conservative (7/3*3 = 6 ≤ 7). -/
theorem witness_conservative :
    (7 : ℤ) / 3 * 3 ≤ 7 := by native_decide

/-- Witness: single-division gap < d (7 - 7/3*3 = 1 < 3). -/
theorem witness_gap :
    (7 : ℤ) - 7 / 3 * 3 < 3 := by native_decide

/-- Witness: symmetric gap is exactly -1 when not divisible (7/3 + (-7)/3 = -1). -/
theorem witness_symmetric_gap :
    (7 : ℤ) / 3 + (-7) / 3 = -1 := by native_decide

/-- Witness: symmetric gap is 0 when divisible (9/3 + (-9)/3 = 0). -/
theorem witness_exact_division :
    (9 : ℤ) / 3 + (-9) / 3 = 0 := by native_decide

end PerpIntegerBridge

end Proofs
