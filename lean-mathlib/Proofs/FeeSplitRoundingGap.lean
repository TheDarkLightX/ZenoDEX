import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Fee Split Rounding Gap

For fee component `floor(amount * feeBps / 10000)`, splitting one order into two
orders cannot increase total fees, and can reduce total fees by at most 1 unit.

These lemmas make the batching/splitting rounding effect explicit and bounded.
-/

namespace Proofs
namespace FeeSplitRoundingGap

def feeComponent (amount feeBps : Nat) : Nat :=
  (amount * feeBps) / 10000

theorem split_fee_le_merged_fee (a b feeBps : Nat) :
    feeComponent a feeBps + feeComponent b feeBps ≤ feeComponent (a + b) feeBps := by
  unfold feeComponent
  have hmul : (a + b) * feeBps = a * feeBps + b * feeBps := by
    simpa using (Nat.add_mul a b feeBps)
  calc
    (a * feeBps) / 10000 + (b * feeBps) / 10000 ≤ (a * feeBps + b * feeBps) / 10000 := by
      exact Nat.add_div_le_add_div (a * feeBps) (b * feeBps) 10000
    _ = ((a + b) * feeBps) / 10000 := by
      rw [← hmul]

theorem merged_fee_le_split_fee_plus_one (a b feeBps : Nat) :
    feeComponent (a + b) feeBps ≤ feeComponent a feeBps + feeComponent b feeBps + 1 := by
  unfold feeComponent
  have hmul : (a + b) * feeBps = a * feeBps + b * feeBps := by
    simpa using (Nat.add_mul a b feeBps)
  rw [hmul]
  have hD : 0 < (10000 : Nat) := by decide
  rw [Nat.add_div hD]
  split_ifs <;> omega

theorem merged_split_gap_at_most_one (a b feeBps : Nat) :
    feeComponent (a + b) feeBps - (feeComponent a feeBps + feeComponent b feeBps) ≤ 1 := by
  have hLower := split_fee_le_merged_fee a b feeBps
  have hUpper := merged_fee_le_split_fee_plus_one a b feeBps
  omega

theorem witness_gap_one :
    feeComponent (1 + 1) 5000 - (feeComponent 1 5000 + feeComponent 1 5000) = 1 := by
  native_decide

theorem witness_gap_zero :
    feeComponent (4 + 8) 2500 - (feeComponent 4 2500 + feeComponent 8 2500) = 0 := by
  native_decide

end FeeSplitRoundingGap
end Proofs
