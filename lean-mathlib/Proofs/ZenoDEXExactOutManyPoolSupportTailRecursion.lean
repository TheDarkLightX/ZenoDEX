import Proofs.ZenoDEXExactOutManyPoolSupportPresentation

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolSupportTailRecursion

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation

/-- Tail of a strictly increasing list is strictly increasing. -/
theorem tail_sortedLT_of_cons_sortedLT
    {α : Type} [Preorder α] {head : α} {tail : List α}
    (hSorted : (head :: tail).SortedLT) :
    tail.SortedLT := by
  rw [List.sortedLT_iff_getElem_lt_getElem_of_lt]
  intro i j hi hj hij
  have h' := List.sortedLT_iff_getElem_lt_getElem_of_lt.mp hSorted
  simpa using h' (i := i + 1) (j := j + 1)
    (hi := by simpa using Nat.succ_lt_succ hi)
    (hj := by simpa using Nat.succ_lt_succ hj)
    (Nat.succ_lt_succ hij)

/-- In a strictly increasing list, the head is strictly smaller than every tail
element. -/
theorem head_lt_of_mem_tail_of_cons_sortedLT
    {α : Type} [Preorder α] {head x : α} {tail : List α}
    (hSorted : (head :: tail).SortedLT)
    (hx : x ∈ tail) :
    head < x := by
  obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.1 hx
  have h' := List.sortedLT_iff_getElem_lt_getElem_of_lt.mp hSorted
  simpa using h' (i := 0) (j := j + 1)
    (hi := by simp)
    (hj := by exact Nat.succ_lt_succ hj)
    (by omega)

/-- If a feasible bounded audited allocation is presented as a nonempty sorted
support list, then its tail is still a valid residual support presentation for
the remaining output: the tail stays sorted and unique, every tail leg is
positive and capacity-bounded, and the erased support sum is exactly the
residual demand. This is the induction shape needed by the selected-domain
generator recursion. -/
theorem feasible_support_cons_residual_obligations
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    head.2 = (alloc head.1 : ℕ) ∧
      0 < head.2 ∧
      head.2 ≤ cap head.1 ∧
      (tail.map Prod.fst).SortedLT ∧
      (tail.map Prod.fst).Nodup ∧
      tail.length + 1 ≤ maxLegs ∧
      (Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) = Q - head.2) ∧
      (∀ leg ∈ tail, head.1 < leg.1) ∧
      (∀ leg ∈ tail, 0 < leg.2) ∧
      (∀ leg ∈ tail, leg.2 ≤ cap leg.1) := by
  rcases hFeas with ⟨hCap, hSum, hLegCount⟩
  have hHeadMem : head ∈ supportLegs alloc := by
    rw [hLegs]
    simp
  have hHeadData := supportLeg_mem_iff.1 hHeadMem
  have hHeadEq : head.2 = (alloc head.1 : ℕ) := hHeadData.1
  have hHeadPos : 0 < head.2 := by
    simpa [hHeadEq] using hHeadData.2
  have hHeadCap : head.2 ≤ cap head.1 := by
    simpa [hHeadEq] using hCap head.1
  have hFst :
      head.1 :: tail.map Prod.fst = supportIndices alloc := by
    simpa [hLegs] using supportLegs_fst alloc
  have hSortedAll : (head.1 :: tail.map Prod.fst).SortedLT := by
    rw [hFst]
    exact supportIndices_sorted alloc
  have hTailSorted : (tail.map Prod.fst).SortedLT :=
    tail_sortedLT_of_cons_sortedLT hSortedAll
  have hLenAll : (supportLegs alloc).length ≤ maxLegs := by
    simpa [supportLegs_length] using hLegCount
  have hTailLen : tail.length + 1 ≤ maxLegs := by
    simpa [hLegs, Nat.add_comm] using hLenAll
  have hHeadInSupport : head.1 ∈ supportSet alloc := by
    exact (mem_supportSet_iff).2 (by simpa [hHeadEq] using hHeadPos)
  have hSupportTotal :
      Finset.sum (supportSet alloc) (fun i => (alloc i : ℕ)) = Q := by
    simpa [supportSet_sum_eq_total] using hSum
  have hEraseAdd :=
    Finset.sum_erase_add (supportSet alloc) (fun i => (alloc i : ℕ)) hHeadInSupport
  have hResidualAdd :
      Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) + head.2 = Q := by
    calc
      Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) + head.2
          = Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) + (alloc head.1 : ℕ) := by
              rw [hHeadEq]
      _ = Finset.sum (supportSet alloc) (fun i => (alloc i : ℕ)) := hEraseAdd
      _ = Q := hSupportTotal
  have hResidual :
      Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) = Q - head.2 := by
    omega
  have hTailGt : ∀ leg ∈ tail, head.1 < leg.1 := by
    intro leg hMem
    have hMemFst : leg.1 ∈ tail.map Prod.fst := by
      exact List.mem_map.2 ⟨leg, hMem, by simp⟩
    exact head_lt_of_mem_tail_of_cons_sortedLT hSortedAll hMemFst
  have hTailPos : ∀ leg ∈ tail, 0 < leg.2 := by
    intro leg hMem
    have hMemAll : leg ∈ supportLegs alloc := by
      rw [hLegs]
      simp [hMem]
    rcases supportLeg_mem_iff.1 hMemAll with ⟨hEq, hPos⟩
    simpa [hEq] using hPos
  have hTailCap : ∀ leg ∈ tail, leg.2 ≤ cap leg.1 := by
    intro leg hMem
    have hMemAll : leg ∈ supportLegs alloc := by
      rw [hLegs]
      simp [hMem]
    have hEq : leg.2 = (alloc leg.1 : ℕ) := (supportLeg_mem_iff.1 hMemAll).1
    simpa [hEq] using hCap leg.1
  refine ⟨hHeadEq, hHeadPos, hHeadCap, hTailSorted, hTailSorted.nodup, hTailLen,
    hResidual, hTailGt, hTailPos, hTailCap⟩

end ExactOutManyPoolSupportTailRecursion
end ZenoDEX
end TauSwap
