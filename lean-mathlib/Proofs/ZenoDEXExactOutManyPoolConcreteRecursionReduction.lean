import Proofs.ZenoDEXExactOutManyPoolResidualAllocation
import Proofs.ZenoDEXExactOutManyPoolRemainingCapacityTopSum

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolConcreteRecursionReduction

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolRemainingCapacityTopSum
open ExactOutManyPoolResidualAllocation

/-!
# Exact-Out Many-Pool Concrete Recursion Reduction

This file packages the checked induction step for the selected-domain builder.

For a feasible support presentation `head :: tail`, the already-proved concrete
range theorem shows the Python branch can choose `head.2`, and the residual
allocation theorem shows the remaining work is exactly the tail support
presentation for target `Q - head.2`.

What remains open after this file is still the actual recursive coverage proof
for the concrete enumerator and the quote-success side condition.
-/

/-- One-step reduction of a feasible support presentation into the exact
recursive obligations of the Python selected-domain builder. -/
theorem feasible_support_cons_reduces_to_concrete_residual
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    let residual := residualAlloc alloc head.1
    max 1 (Q - remainingCapacityTopSum cap head.1 tail.length) ≤ head.2 ∧
      head.2 ≤ min (cap head.1) Q ∧
      supportLegs residual = tail ∧
      FeasibleFor cap (Q - head.2) tail.length residual := by
  dsimp
  rcases feasible_support_cons_head_within_top_sum_range
      (hFeas := hFeas) (hLegs := hLegs) (hSlots := le_rfl) with
    ⟨hLower, hUpper⟩
  rcases feasible_support_cons_residual_alloc_packet
      (hFeas := hFeas) (hLegs := hLegs) with
    ⟨hResidualLegs, hResidualFeas⟩
  exact ⟨hLower, hUpper, hResidualLegs, hResidualFeas⟩

end ExactOutManyPoolConcreteRecursionReduction
end ZenoDEX
end TauSwap
