import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Proofs.ZenoDEXExactOutManyPoolSupportHeadBounds

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolRemainingCapacityEnvelope

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion
open ExactOutManyPoolSupportHeadBounds

/-- Indices strictly after the current head index in the audited canonical pool
order. This matches the concrete generator's suffix scan after fixing the head
leg. -/
def suffixSet {n : ℕ} (headIdx : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => headIdx < i

/-- Maximal audited output capacity obtainable from any suffix subset using at
most `slots` legs. This is a finite-set envelope version of the concrete
generator's `remaining_capacity` objective. -/
def remainingCapacityEnvelope {n : ℕ}
    (cap : Fin n → ℕ)
    (headIdx : Fin n)
    (slots : ℕ) : ℕ :=
  (((suffixSet headIdx).powerset.filter fun s => s.card ≤ slots).sup fun s => Finset.sum s cap)

/-- Any feasible residual support after fixing the head leg is bounded by the
finite top-`slots` suffix-capacity envelope, provided `slots` is at least the
actual tail length. -/
theorem residualSupportCap_le_remainingCapacityEnvelope
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    {slots : ℕ}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail)
    (hSlots : tail.length ≤ slots) :
    residualSupportCap cap alloc head.1 ≤
      remainingCapacityEnvelope cap head.1 slots := by
  rcases feasible_support_cons_residual_obligations (hFeas := hFeas) (hLegs := hLegs) with
    ⟨hHeadEq, hHeadPos, _hHeadCap, _hTailSorted, _hTailNodup, _hTailLen,
      _hResidual, hTailGt, _hTailPos, _hTailCap⟩
  have hHeadInSupport : head.1 ∈ supportSet alloc := by
    exact (mem_supportSet_iff).2 (by simpa [hHeadEq] using hHeadPos)
  have hFst : head.1 :: tail.map Prod.fst = supportIndices alloc := by
    simpa [hLegs] using supportLegs_fst alloc
  have hSupportCard : (supportSet alloc).card = tail.length + 1 := by
    calc
      (supportSet alloc).card = (supportIndices alloc).length := by
        simpa [supportSet, usedLegCount] using (supportIndices_length alloc).symm
      _ = tail.length + 1 := by
        rw [← hFst]
        simp
  have hResidualCard : ((supportSet alloc).erase head.1).card = tail.length := by
    rw [Finset.card_erase_of_mem hHeadInSupport, hSupportCard]
    omega
  have hResidualSubset : (supportSet alloc).erase head.1 ⊆ suffixSet head.1 := by
    intro i hi
    have hPos : 0 < (alloc i : ℕ) := (mem_supportSet_iff).1 ((Finset.mem_erase.mp hi).2)
    have hLegMemAll : (i, (alloc i : ℕ)) ∈ supportLegs alloc := by
      exact (supportLeg_mem_iff).2 ⟨rfl, hPos⟩
    have hLegMemTail : (i, (alloc i : ℕ)) ∈ tail := by
      rw [hLegs] at hLegMemAll
      rcases List.mem_cons.1 hLegMemAll with hHead | hTail
      · exfalso
        have : i = head.1 := by
          simpa using congrArg Prod.fst hHead
        exact (Finset.mem_erase.mp hi).1 this
      · exact hTail
    have hGt : head.1 < i := hTailGt _ hLegMemTail
    simp [suffixSet, hGt]
  have hMemEnvelope : (supportSet alloc).erase head.1 ∈
      (suffixSet head.1).powerset.filter fun s => s.card ≤ slots := by
    simp [Finset.mem_powerset, hResidualSubset, hResidualCard, hSlots]
  simpa [remainingCapacityEnvelope, residualSupportCap] using
    (Finset.le_sup (f := fun s => Finset.sum s cap) hMemEnvelope)

/-- If `futureMax` dominates the finite top-`slots` suffix-capacity envelope,
then the chosen head leg lies inside the same recursive range the concrete
generator uses for that branch. -/
theorem feasible_support_cons_head_within_envelope_range
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    {slots futureMax : ℕ}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail)
    (hSlots : tail.length ≤ slots)
    (hFuture : remainingCapacityEnvelope cap head.1 slots ≤ futureMax) :
    max 1 (Q - futureMax) ≤ head.2 ∧
      head.2 ≤ min (cap head.1) Q := by
  apply feasible_support_cons_head_within_future_range (hFeas := hFeas) (hLegs := hLegs)
  exact le_trans
    (residualSupportCap_le_remainingCapacityEnvelope (hFeas := hFeas) (hLegs := hLegs) hSlots)
    hFuture

end ExactOutManyPoolRemainingCapacityEnvelope
end ZenoDEX
end TauSwap
