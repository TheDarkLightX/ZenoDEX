import Proofs.ZenoDEXExactOutManyPoolConcreteRecursionReduction
import Proofs.ZenoDEXExactOutManyPoolReindexedResidualAllocation

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolStructuralRecursionReachability

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolConcreteRecursionReduction
open ExactOutManyPoolReindexedResidualAllocation

/-!
# Exact-Out Many-Pool Structural Recursion Reachability

This file stops one step short of full concrete generator completeness.

It proves the strongest honest statement available without formalizing the
`quote_in` success side condition: every feasible bounded support presentation
is structurally reachable by the concrete Python recursion ranges.

In other words, the current head-range bounds and residual reindexing are now
strong enough to show that the recursion *shape* can follow any feasible
support split. What remains open is that the concrete runtime quote oracle
returns `some amount_in` for each chosen amount, and that the emitted candidate
stream includes the resulting quote packet.
-/

/-- Support list is structurally reachable by the concrete selected-domain
recursion ranges if it can be built by repeatedly choosing a head leg inside the
exact Python branch interval and recursing on the residual target. -/
inductive StructurallyReachable {n : ℕ} (cap : Fin n → ℕ) : ℕ → List (Fin n × ℕ) → Prop where
  | nil :
      StructurallyReachable cap 0 []
  | cons
      {Q : ℕ}
      {head : Fin n × ℕ}
      {tail : List (Fin n × ℕ)}
      (hLower : max 1 (Q - ExactOutManyPoolRemainingCapacityTopSum.remainingCapacityTopSum cap head.1 tail.length) ≤ head.2)
      (hUpper : head.2 ≤ min (cap head.1) Q)
      (hTail : StructurallyReachable cap (Q - head.2) tail) :
      StructurallyReachable cap Q (head :: tail)

theorem target_zero_of_supportLegs_nil
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = []) :
    Q = 0 := by
  rcases hFeas with ⟨_hCap, hSum, _hLegs⟩
  have hSupportEmpty : supportSet alloc = ∅ := by
    ext i
    constructor
    · intro hi
      have hPos : 0 < (alloc i : ℕ) := (mem_supportSet_iff).1 hi
      have hMem : (i, (alloc i : ℕ)) ∈ supportLegs alloc := by
        exact (supportLeg_mem_iff).2 ⟨rfl, hPos⟩
      rw [hLegs] at hMem
      simp at hMem
    · intro hi
      cases hi
  have hSupportSum : Finset.sum (supportSet alloc) (fun i => (alloc i : ℕ)) = Q := by
    simpa [supportSet_sum_eq_total] using hSum
  have hZero : 0 = Q := by
    simpa [hSupportEmpty] using hSupportSum
  exact hZero.symm

/-- Every feasible bounded support presentation is structurally reachable by the
concrete recursion ranges. This is a support-shape coverage theorem, not yet a
full emitted-candidate completeness theorem. -/
theorem structurallyReachable_of_feasible_presentation
    {n : ℕ} {cap : Fin n → ℕ} :
    ∀ {legs : List (Fin n × ℕ)} {Q maxLegs : ℕ} {alloc : Alloc n Q},
      supportLegs alloc = legs →
      Feasible cap maxLegs alloc →
      StructurallyReachable cap Q legs
  | [], Q, maxLegs, alloc, hLegs, hFeas => by
      have hQZero : Q = 0 := target_zero_of_supportLegs_nil (hFeas := hFeas) hLegs
      simpa [hQZero] using (StructurallyReachable.nil (cap := cap))
  | head :: tail, Q, maxLegs, alloc, hLegs, hFeas => by
      rcases feasible_support_cons_reduces_to_concrete_residual
          (hFeas := hFeas) (hLegs := hLegs) with
        ⟨hLower, hUpper, _hResidualLegsAmbient, _hResidualFeasAmbient⟩
      let residual :=
        reindexedResidualAlloc (hFeas := hFeas) (hLegs := hLegs)
      have hResidualPacket :
          supportLegs residual = tail ∧
            Feasible cap tail.length residual :=
        feasible_support_cons_reindexed_residual_packet
          (hFeas := hFeas) (hLegs := hLegs)
      rcases hResidualPacket with ⟨hResidualLegs, hResidualFeas⟩
      exact StructurallyReachable.cons hLower hUpper
        (structurallyReachable_of_feasible_presentation
          (legs := tail)
          (alloc := residual)
          hResidualLegs
          hResidualFeas)

theorem feasible_supportLegs_structurallyReachable
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc) :
    StructurallyReachable cap Q (supportLegs alloc) :=
  structurallyReachable_of_feasible_presentation (cap := cap) rfl hFeas

end ExactOutManyPoolStructuralRecursionReachability
end ZenoDEX
end TauSwap
