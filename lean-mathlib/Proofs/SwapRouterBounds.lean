import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Swap Router Bound Preservation

Arithmetic obligations for route updates:
- `routing_success_count` update (`count := count + 1`) must stay within `[0, 1_000_000]`.
- `total_savings` update (`total := total + savings`) must stay within `[0, 100_000_000]`.

These lemmas capture exactly the guard shape used in the repaired router kernels.
-/

namespace Proofs
namespace SwapRouterBounds

def nextRoutingCount (count : Nat) : Nat := count + 1

def nextTotalSavings (total savings : Nat) : Nat := total + savings

theorem next_routing_count_nonneg (count : Nat) :
    0 ≤ nextRoutingCount count := by
  exact Nat.zero_le _

theorem next_routing_count_le_cap
    {count : Nat}
    (hCount : count < 1000000) :
    nextRoutingCount count ≤ 1000000 := by
  unfold nextRoutingCount
  omega

theorem next_total_savings_nonneg (total savings : Nat) :
    0 ≤ nextTotalSavings total savings := by
  exact Nat.zero_le _

theorem next_total_savings_le_cap
    {total savings : Nat}
    (hBound : total + savings ≤ 100000000) :
    nextTotalSavings total savings ≤ 100000000 := by
  simpa [nextTotalSavings] using hBound

theorem route_step_preserves_bounds
    {count total savings : Nat}
    (hCount : count < 1000000)
    (hBound : total + savings ≤ 100000000) :
    nextRoutingCount count ≤ 1000000 ∧ nextTotalSavings total savings ≤ 100000000 := by
  exact ⟨next_routing_count_le_cap hCount, next_total_savings_le_cap hBound⟩

theorem witness_edge_count :
    nextRoutingCount 999999 = 1000000 := by
  native_decide

theorem witness_edge_total :
    nextTotalSavings 90000000 10000000 = 100000000 := by
  native_decide

end SwapRouterBounds
end Proofs
