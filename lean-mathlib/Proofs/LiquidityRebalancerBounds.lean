import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Liquidity Rebalancer Bounds

Arithmetic contracts for rebalance steps:
- transfer preserves total inventory
- post-transfer balances remain within [0, cap] under guard assumptions
-/

namespace Proofs
namespace LiquidityRebalancerBounds

def nextA (a transfer : Int) : Int := a - transfer

def nextB (b transfer : Int) : Int := b + transfer

theorem total_preserved {a b transfer : Int} :
    nextA a transfer + nextB b transfer = a + b := by
  simp [nextA, nextB]

theorem nextA_nonneg
    {a transfer : Int}
    (h : transfer ≤ a) :
    0 ≤ nextA a transfer := by
  unfold nextA
  linarith

theorem nextB_nonneg
    {b transfer : Int}
    (h : -b ≤ transfer) :
    0 ≤ nextB b transfer := by
  unfold nextB
  linarith

theorem nextA_le_cap
    {a transfer cap : Int}
    (hA : a ≤ cap)
    (hT : 0 ≤ transfer) :
    nextA a transfer ≤ cap := by
  unfold nextA
  linarith

theorem nextB_le_cap
    {b transfer cap : Int}
    (hB : b + transfer ≤ cap) :
    nextB b transfer ≤ cap := by
  unfold nextB
  simpa using hB

theorem witness_transfer_total :
    nextA 100 15 + nextB 20 15 = 120 := by
  native_decide

theorem witness_bounds :
    nextA 50 10 = 40 ∧ nextB 30 10 = 40 := by
  native_decide

end LiquidityRebalancerBounds
end Proofs
