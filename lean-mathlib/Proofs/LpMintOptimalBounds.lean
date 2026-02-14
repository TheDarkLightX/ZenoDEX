import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# LP Mint Optimal Bounds

Simple arithmetic contracts for LP-mint style updates:
- minted amount is nonnegative
- bounded by available input
- reserve update preserves upper cap under guard assumptions
-/

namespace Proofs
namespace LpMintOptimalBounds

def mintedAmount (input fee : Nat) : Nat := input - fee

def nextReserve (reserve minted : Nat) : Nat := reserve + minted

theorem minted_nonneg (input fee : Nat) : 0 ≤ mintedAmount input fee := by
  exact Nat.zero_le _

theorem minted_le_input (input fee : Nat) : mintedAmount input fee ≤ input := by
  unfold mintedAmount
  exact Nat.sub_le _ _

theorem minted_add_fee_eq_input
    {input fee : Nat} (hFee : fee ≤ input) :
    mintedAmount input fee + fee = input := by
  unfold mintedAmount
  exact Nat.sub_add_cancel hFee

theorem next_reserve_le_cap
    {reserve input fee cap : Nat}
    (hCap : reserve + (input - fee) ≤ cap) :
    nextReserve reserve (mintedAmount input fee) ≤ cap := by
  unfold nextReserve mintedAmount
  simpa using hCap

theorem witness_minted_basic : mintedAmount 10 3 = 7 := by
  native_decide

theorem witness_next_reserve : nextReserve 100 (mintedAmount 10 3) = 107 := by
  native_decide

end LpMintOptimalBounds
end Proofs
