import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCompleteness

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolSupportPresentation

open ExactOutManyPoolSelectedDomainCompleteness

/-- Support set of positive-output audited legs for a bounded allocation. -/
def supportSet {n Q : ℕ} (alloc : Alloc n Q) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < (alloc i : ℕ)

/-- Sorted unique support indices, matching the canonical audited pool order. -/
def supportIndices {n Q : ℕ} (alloc : Alloc n Q) : List (Fin n) :=
  (supportSet alloc).sort

/-- Concrete leg presentation of a bounded allocation: sorted support indices
paired with their positive outputs. -/
def supportLegs {n Q : ℕ} (alloc : Alloc n Q) : List (Fin n × ℕ) :=
  (supportIndices alloc).map fun i => (i, (alloc i : ℕ))

theorem mem_supportSet_iff {n Q : ℕ} {alloc : Alloc n Q} {i : Fin n} :
    i ∈ supportSet alloc ↔ 0 < (alloc i : ℕ) := by
  simp [supportSet]

theorem mem_supportIndices_iff {n Q : ℕ} {alloc : Alloc n Q} {i : Fin n} :
    i ∈ supportIndices alloc ↔ 0 < (alloc i : ℕ) := by
  rw [supportIndices, Finset.mem_sort]
  exact mem_supportSet_iff

theorem supportIndices_nodup {n Q : ℕ} (alloc : Alloc n Q) :
    (supportIndices alloc).Nodup := by
  simp [supportIndices]

theorem supportIndices_sorted {n Q : ℕ} (alloc : Alloc n Q) :
    (supportIndices alloc).SortedLT := by
  simpa [supportIndices] using (supportSet alloc).sortedLT_sort

theorem supportIndices_length {n Q : ℕ} (alloc : Alloc n Q) :
    (supportIndices alloc).length = usedLegCount alloc := by
  simp [supportIndices, supportSet, usedLegCount]

theorem supportLegs_fst {n Q : ℕ} (alloc : Alloc n Q) :
    (supportLegs alloc).map Prod.fst = supportIndices alloc := by
  rw [supportLegs, List.map_map]
  change List.map (fun i => i) (supportIndices alloc) = supportIndices alloc
  simp

theorem supportLegs_length {n Q : ℕ} (alloc : Alloc n Q) :
    (supportLegs alloc).length = usedLegCount alloc := by
  rw [supportLegs, List.length_map, supportIndices_length]

theorem supportSet_sum_eq_total {n Q : ℕ} (alloc : Alloc n Q) :
    Finset.sum (supportSet alloc) (fun i => (alloc i : ℕ)) =
      Finset.sum Finset.univ (fun i => (alloc i : ℕ)) := by
  rw [supportSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < (alloc i : ℕ)
  · simp [h]
  · have hz : (alloc i : ℕ) = 0 := Nat.eq_zero_of_not_pos h
    simp [hz]

theorem supportLeg_mem_iff {n Q : ℕ} {alloc : Alloc n Q} {leg : Fin n × ℕ} :
    leg ∈ supportLegs alloc ↔
      leg.2 = (alloc leg.1 : ℕ) ∧ 0 < (alloc leg.1 : ℕ) := by
  constructor
  · intro hLeg
    have hinj : Function.Injective (fun i : Fin n => (i, (alloc i : ℕ))) := by
      intro i j hij
      simpa using congrArg Prod.fst hij
    rcases List.mem_map.1 hLeg with ⟨i, hi, rfl⟩
    exact ⟨rfl, (mem_supportIndices_iff).1 hi⟩
  · rintro ⟨hAmt, hPos⟩
    rw [supportLegs]
    cases leg with
    | mk i amt =>
        exact List.mem_map.2 ⟨i, (mem_supportIndices_iff).2 hPos,
          by
            simp at hAmt ⊢
            exact hAmt.symm⟩

/-- Every feasible bounded audited allocation has the concrete normal form used
by the selected-domain candidate shell: sorted unique positive legs, bounded by
their audited capacities, with total emitted output exactly `Q`. -/
theorem feasible_has_sorted_support_presentation
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc) :
    (((supportLegs alloc).map Prod.fst).SortedLT) ∧
      ((supportLegs alloc).map Prod.fst).Nodup ∧
      (supportLegs alloc).length ≤ maxLegs ∧
      (Finset.sum (supportSet alloc) (fun i => (alloc i : ℕ)) = Q) ∧
      (∀ leg ∈ supportLegs alloc, 0 < leg.2) ∧
      (∀ leg ∈ supportLegs alloc, leg.2 ≤ cap leg.1) := by
  rcases hFeas with ⟨hCap, hSum, hLegCount⟩
  constructor
  · simpa [supportLegs_fst] using supportIndices_sorted alloc
  constructor
  · simpa [supportLegs_fst] using supportIndices_nodup alloc
  constructor
  · rw [supportLegs_length]
    exact hLegCount
  constructor
  · simpa [supportSet_sum_eq_total] using hSum
  constructor
  · intro leg hMem
    rcases (supportLeg_mem_iff.1 hMem) with ⟨hEq, hPos⟩
    simpa [hEq] using hPos
  · intro leg hMem
    have hEq : leg.2 = (alloc leg.1 : ℕ) := (supportLeg_mem_iff.1 hMem).1
    simpa [hEq] using hCap leg.1

end ExactOutManyPoolSupportPresentation
end ZenoDEX
end TauSwap
