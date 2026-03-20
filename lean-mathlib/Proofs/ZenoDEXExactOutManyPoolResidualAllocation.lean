import Mathlib.Data.Finset.Sort
import Proofs.ZenoDEXExactOutManyPoolSupportTailRecursion

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolResidualAllocation

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolSupportTailRecursion

/-!
# Exact-Out Many-Pool Residual Allocation

This file packages the next induction object for selected-domain generator
completeness.

After fixing the concrete head leg of a feasible support presentation
`head :: tail`, define a residual allocation by zeroing out `head.1` while
keeping every other audited pool amount unchanged. The main theorem shows:

- the residual allocation's support presentation is exactly `tail`, and
- it is feasible for the residual target `Q - head.2` with `tail.length`
  remaining nonzero legs.

This avoids dependent recasting into a smaller ambient `Alloc n (Q - head.2)`
while still giving the recursive object needed for a future coverage induction.
-/

/-- Zero out one chosen head index inside the ambient bounded allocation space. -/
def residualAlloc {n Q : ℕ} (alloc : Alloc n Q) (headIdx : Fin n) : Alloc n Q :=
  fun i => if i = headIdx then 0 else alloc i

/-- Feasibility for an arbitrary residual target inside the same ambient
bounded allocation space. -/
def FeasibleFor {n Q : ℕ}
    (cap : Fin n → ℕ)
    (target maxLegs : ℕ)
    (alloc : Alloc n Q) : Prop :=
  (∀ i, (alloc i : ℕ) ≤ cap i) ∧
    (∑ i, (alloc i : ℕ)) = target ∧
    usedLegCount alloc ≤ maxLegs

theorem supportSet_residualAlloc_eq_erase
    {n Q : ℕ}
    {alloc : Alloc n Q}
    {headIdx : Fin n} :
    supportSet (residualAlloc alloc headIdx) = (supportSet alloc).erase headIdx := by
  ext i
  by_cases h : i = headIdx
  · subst h
    simp [supportSet, residualAlloc]
  · simp [supportSet, residualAlloc, h, Finset.mem_erase]

lemma list_eq_map_fst_of_amount_eq
    {n Q : ℕ}
    {alloc : Alloc n Q} :
    ∀ {legs : List (Fin n × ℕ)},
      (∀ leg ∈ legs, leg.2 = (alloc leg.1 : ℕ)) →
      legs = (legs.map Prod.fst).map (fun i => (i, (alloc i : ℕ)))
  | [], _ => by simp
  | leg :: legs, hAmt => by
      have hHead : leg.2 = (alloc leg.1 : ℕ) := hAmt leg (by simp)
      have hTail : ∀ leg' ∈ legs, leg'.2 = (alloc leg'.1 : ℕ) := by
        intro leg' hMem
        exact hAmt leg' (by simp [hMem])
      cases leg with
      | mk i amt =>
          simp at hHead
          have hRec := list_eq_map_fst_of_amount_eq (alloc := alloc) hTail
          cases hHead
          exact congrArg (List.cons (i, (alloc i : ℕ))) hRec

/-- After fixing the head leg of a feasible support presentation, the residual
allocation obtained by zeroing that head has support presentation exactly
`tail`, and remains feasible for the residual target `Q - head.2`. -/
theorem feasible_support_cons_residual_alloc_packet
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    let residual := residualAlloc alloc head.1
    supportLegs residual = tail ∧
      FeasibleFor cap (Q - head.2) tail.length residual := by
  dsimp
  rcases feasible_support_cons_residual_obligations (hFeas := hFeas) (hLegs := hLegs) with
    ⟨hHeadEq, hHeadPos, _hHeadCap, hTailSorted, _hTailNodup, _hTailLen,
      hResidual, hTailGt, hTailPos, hTailCap⟩
  have hHeadInSupport : head.1 ∈ supportSet alloc := by
    exact (mem_supportSet_iff).2 (by simpa [hHeadEq] using hHeadPos)
  have hFst :
      head.1 :: tail.map Prod.fst = (supportSet alloc).sort := by
    simpa [supportIndices] using (by simpa [hLegs] using supportLegs_fst alloc)
  have hHeadLe :
      ∀ b ∈ (supportSet alloc).erase head.1, head.1 ≤ b := by
    intro b hb
    have hPos : 0 < (alloc b : ℕ) := (mem_supportSet_iff).1 (Finset.mem_of_mem_erase hb)
    have hLegMemAll : (b, (alloc b : ℕ)) ∈ supportLegs alloc := by
      exact (supportLeg_mem_iff).2 ⟨rfl, hPos⟩
    have hLegMemTail : (b, (alloc b : ℕ)) ∈ tail := by
      rw [hLegs] at hLegMemAll
      simp at hLegMemAll
      rcases hLegMemAll with hEqLeg | hMemTail
      · have : b = head.1 := by
          simpa using congrArg Prod.fst hEqLeg
        exact False.elim ((Finset.mem_erase.mp hb).1 this)
      · exact hMemTail
    exact le_of_lt (hTailGt _ hLegMemTail)
  have hSortErase :
      (supportSet alloc).sort = head.1 :: ((supportSet alloc).erase head.1).sort := by
    rw [← Finset.insert_erase hHeadInSupport]
    simpa using
      (Finset.sort_insert (r := fun a b : Fin n => a ≤ b) hHeadLe (Finset.notMem_erase _ _))
  have hTailIndices : ((supportSet alloc).erase head.1).sort = tail.map Prod.fst := by
    have hEq :
        head.1 :: ((supportSet alloc).erase head.1).sort = head.1 :: tail.map Prod.fst := by
      rw [← hSortErase, hFst]
    simpa using congrArg List.tail hEq
  have hResidualIndices :
      supportIndices (residualAlloc alloc head.1) = tail.map Prod.fst := by
    simpa [supportIndices, supportSet_residualAlloc_eq_erase] using hTailIndices
  have hTailResidualAmounts :
      ∀ leg ∈ tail, leg.2 = (residualAlloc alloc head.1 leg.1 : ℕ) := by
    intro leg hMem
    have hAmt : leg.2 = (alloc leg.1 : ℕ) := by
      have hMemAll : leg ∈ supportLegs alloc := by
        rw [hLegs]
        simp [hMem]
      exact (supportLeg_mem_iff.1 hMemAll).1
    have hNe : leg.1 ≠ head.1 := ne_of_gt (hTailGt leg hMem)
    simpa [residualAlloc, hNe] using hAmt
  have hResidualLegs :
      supportLegs (residualAlloc alloc head.1) = tail := by
    calc
      supportLegs (residualAlloc alloc head.1)
          = (tail.map Prod.fst).map (fun i => (i, (residualAlloc alloc head.1 i : ℕ))) := by
              simp [supportLegs, hResidualIndices]
      _ = tail := by
          exact (list_eq_map_fst_of_amount_eq (alloc := residualAlloc alloc head.1)
            hTailResidualAmounts).symm
  have hResidualCap :
      ∀ i, (residualAlloc alloc head.1 i : ℕ) ≤ cap i := by
    intro i
    by_cases h : i = head.1
    · subst h
      simp [residualAlloc]
    · simpa [residualAlloc, h] using hFeas.1 i
  have hResidualSumErase :
      Finset.sum ((supportSet alloc).erase head.1)
        (fun i => (residualAlloc alloc head.1 i : ℕ)) = Q - head.2 := by
    calc
      Finset.sum ((supportSet alloc).erase head.1)
          (fun i => (residualAlloc alloc head.1 i : ℕ))
          = Finset.sum ((supportSet alloc).erase head.1) (fun i => (alloc i : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hNe : i ≠ head.1 := (Finset.mem_erase.mp hi).1
              simp [residualAlloc, hNe]
      _ = Q - head.2 := hResidual
  have hResidualSum :
      (∑ i, (residualAlloc alloc head.1 i : ℕ)) = Q - head.2 := by
    calc
      (∑ i, (residualAlloc alloc head.1 i : ℕ))
          = Finset.sum (supportSet (residualAlloc alloc head.1))
              (fun i => (residualAlloc alloc head.1 i : ℕ)) := by
                symm
                exact supportSet_sum_eq_total (residualAlloc alloc head.1)
      _ = Finset.sum ((supportSet alloc).erase head.1)
            (fun i => (residualAlloc alloc head.1 i : ℕ)) := by
              simp [supportSet_residualAlloc_eq_erase]
      _ = Q - head.2 := hResidualSumErase
  have hResidualLegCount :
      usedLegCount (residualAlloc alloc head.1) = tail.length := by
    rw [← supportLegs_length (alloc := residualAlloc alloc head.1), hResidualLegs]
  exact ⟨hResidualLegs, hResidualCap, hResidualSum, le_of_eq hResidualLegCount⟩

end ExactOutManyPoolResidualAllocation
end ZenoDEX
end TauSwap
