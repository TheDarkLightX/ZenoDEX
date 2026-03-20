import Proofs.ZenoDEXExactOutManyPoolRemainingCapacityTopSum

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolConcreteRecursionBranch

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion
open ExactOutManyPoolRemainingCapacityTopSum

/-!
# Exact-Out Many-Pool Concrete Recursion Branch

This file still does not prove full selected-domain generator completeness.
Instead, it packages the next concrete bridge needed for that induction:

- a feasible audited support presentation `head :: tail` satisfies the exact
  branch bounds used by the Python `recurse` loop,
- the residual support facts needed by the recursive call are preserved, and
- the singleton-support base case really forces `amount_out = remaining_out`.

This is the closest local theorem surface to the concrete builder without yet
formalizing the whole recursive enumerator.
-/

/-- A feasible support presentation `head :: tail` satisfies the concrete
Python recursion branch obligations:

- `head.2` is the emitted amount at `head.1`,
- it is positive and within the branch cap,
- the residual output `Q - head.2` is covered by the concrete
  `remainingCapacityTopSum` over the suffix after `head.1`,
- and the tail remains a sorted positive capacity-bounded residual support
  presentation for the recursive call. -/
theorem feasible_support_cons_concrete_recurse_obligations
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    head.2 = (alloc head.1 : ℕ) ∧
      0 < head.2 ∧
      head.2 ≤ min (cap head.1) Q ∧
      Q - head.2 ≤ remainingCapacityTopSum cap head.1 tail.length ∧
      (Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) = Q - head.2) ∧
      (tail.map Prod.fst).SortedLT ∧
      (tail.map Prod.fst).Nodup ∧
      tail.length + 1 ≤ maxLegs ∧
      (∀ leg ∈ tail, head.1 < leg.1 ∧ 0 < leg.2 ∧ leg.2 ≤ cap leg.1) := by
  rcases feasible_support_cons_residual_obligations (hFeas := hFeas) (hLegs := hLegs) with
    ⟨hHeadEq, hHeadPos, _hHeadCap, hTailSorted, hTailNodup, hTailLen,
      hResidual, hTailGt, hTailPos, hTailCap⟩
  rcases feasible_support_cons_head_within_top_sum_range
      (hFeas := hFeas) (hLegs := hLegs) (hSlots := le_rfl) with
    ⟨hLower, hUpper⟩
  have hResidualCovered : Q - head.2 ≤ remainingCapacityTopSum cap head.1 tail.length := by
    omega
  have hTailPacket : ∀ leg ∈ tail, head.1 < leg.1 ∧ 0 < leg.2 ∧ leg.2 ≤ cap leg.1 := by
    intro leg hMem
    exact ⟨hTailGt leg hMem, hTailPos leg hMem, hTailCap leg hMem⟩
  refine ⟨hHeadEq, hHeadPos, hUpper, hResidualCovered, hResidual,
    hTailSorted, hTailNodup, hTailLen, hTailPacket⟩

/-- Singleton feasible support is the concrete recursion base case:
if only one positive leg remains, its emitted output must equal the full
remaining target `Q`. This matches the Python branch
`if legs_left == 1 then min_amount_out = remaining_out`. -/
theorem feasible_support_singleton_head_eq_total
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = [head]) :
    head.2 = Q := by
  rcases feasible_support_cons_concrete_recurse_obligations
      (hFeas := hFeas)
      (head := head)
      (tail := [])
      (hLegs := by simpa using hLegs)
    with
    ⟨_hEq, hPos, hUpper, hCovered, _hResidual, _hSorted, _hNodup, _hLen, _hTail⟩
  have hTopZero : remainingCapacityTopSum cap head.1 0 = 0 := by
    simp [remainingCapacityTopSum]
  have hResidualZero : Q - head.2 = 0 := by
    simpa [hTopZero] using hCovered
  have hGeQ : Q ≤ head.2 := by
    omega
  have hLeQ : head.2 ≤ Q := le_trans hUpper (min_le_right _ _)
  exact le_antisymm hLeQ hGeQ

end ExactOutManyPoolConcreteRecursionBranch
end ZenoDEX
end TauSwap
