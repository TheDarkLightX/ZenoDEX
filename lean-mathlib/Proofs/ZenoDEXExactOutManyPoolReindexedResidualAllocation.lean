import Proofs.ZenoDEXExactOutManyPoolResidualAllocation

open scoped Classical BigOperators

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolReindexedResidualAllocation

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolResidualAllocation

/-!
# Exact-Out Many-Pool Reindexed Residual Allocation

The previous residual-allocation theorem kept the recursive object in the old
ambient bounded space `Alloc n Q`. This file reindexes such an ambient residual
allocation into the genuine recursive ambient space `Alloc n target`.

That gives the next concrete bridge needed for a full recursion-coverage proof:

- any ambient allocation satisfying `FeasibleFor cap target maxLegs` can be
  recast into an actual `Alloc n target` that is `Feasible cap maxLegs`,
- in particular, the residual allocation after fixing the head leg can be
  reindexed into the exact recursive target `Q - head.2`,
- and its support presentation is still exactly `tail`.
-/

/-- Reindex an ambient bounded allocation into a tighter target bound once every
component is known to be `≤ target`. -/
def reindexAlloc {n Q target : ℕ}
    (alloc : Alloc n Q)
    (hBound : ∀ i, (alloc i : ℕ) ≤ target) : Alloc n target :=
  fun i => ⟨(alloc i : ℕ), Nat.lt_succ_iff.mpr (hBound i)⟩

@[simp] theorem reindexAlloc_val
    {n Q target : ℕ}
    {alloc : Alloc n Q}
    {hBound : ∀ i, (alloc i : ℕ) ≤ target}
    {i : Fin n} :
    ((reindexAlloc alloc hBound i : Fin (target + 1)) : ℕ) = (alloc i : ℕ) := by
  rfl

/-- Any single component is bounded by the declared residual target once the
ambient allocation sums exactly to that target. -/
theorem component_le_target_of_feasibleFor
    {n Q target maxLegs : ℕ}
    {cap : Fin n → ℕ}
    {alloc : Alloc n Q}
    (hFeas : FeasibleFor cap target maxLegs alloc)
    (i : Fin n) :
    (alloc i : ℕ) ≤ target := by
  rcases hFeas with ⟨_hCap, hSum, _hLegs⟩
  have hLeSum : (alloc i : ℕ) ≤ ∑ j, (alloc j : ℕ) := by
    have hAdd :=
      Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin n => (alloc j : ℕ)) (by simp : i ∈ Finset.univ)
    calc
      (alloc i : ℕ) ≤ Finset.sum (Finset.univ.erase i) (fun j => (alloc j : ℕ)) + (alloc i : ℕ) := by
        exact Nat.le_add_left _ _
      _ = ∑ j, (alloc j : ℕ) := by
        simpa using hAdd
  calc
    (alloc i : ℕ) ≤ ∑ j, (alloc j : ℕ) := hLeSum
    _ = target := hSum

theorem supportSet_reindexAlloc_eq
    {n Q target : ℕ}
    {alloc : Alloc n Q}
    {hBound : ∀ i, (alloc i : ℕ) ≤ target} :
    supportSet (reindexAlloc alloc hBound) = supportSet alloc := by
  ext i
  simp [supportSet, reindexAlloc]

theorem supportIndices_reindexAlloc_eq
    {n Q target : ℕ}
    {alloc : Alloc n Q}
    {hBound : ∀ i, (alloc i : ℕ) ≤ target} :
    supportIndices (reindexAlloc alloc hBound) = supportIndices alloc := by
  simp [supportIndices, supportSet_reindexAlloc_eq]

theorem supportLegs_reindexAlloc_eq
    {n Q target : ℕ}
    {alloc : Alloc n Q}
    {hBound : ∀ i, (alloc i : ℕ) ≤ target} :
    supportLegs (reindexAlloc alloc hBound) = supportLegs alloc := by
  simp [supportLegs, supportIndices_reindexAlloc_eq]

theorem feasible_reindexAlloc_of_feasibleFor
    {n Q target maxLegs : ℕ}
    {cap : Fin n → ℕ}
    {alloc : Alloc n Q}
    (hFeas : FeasibleFor cap target maxLegs alloc) :
    Feasible cap maxLegs
      (reindexAlloc alloc (component_le_target_of_feasibleFor hFeas)) := by
  let hBound := component_le_target_of_feasibleFor hFeas
  rcases hFeas with ⟨hCap, hSum, hLegs⟩
  exact ⟨
    (by
      intro i
      simpa [reindexAlloc] using hCap i),
    (by simpa [reindexAlloc] using hSum),
    (by
      rw [← supportLegs_length (alloc := reindexAlloc alloc hBound)]
      rw [supportLegs_reindexAlloc_eq]
      rw [supportLegs_length]
      exact hLegs)
  ⟩

/-- Reindexed recursive object for a feasible support presentation `head :: tail`.
This is the exact residual allocation the future coverage induction can recurse
on inside the smaller target space `Alloc n (Q - head.2)`. -/
def reindexedResidualAlloc
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) : Alloc n (Q - head.2) :=
  let hPacket := feasible_support_cons_residual_alloc_packet
    (hFeas := hFeas) (hLegs := hLegs)
  reindexAlloc (residualAlloc alloc head.1)
    (component_le_target_of_feasibleFor hPacket.2)

theorem feasible_support_cons_reindexed_residual_packet
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    {head : Fin n × ℕ} {tail : List (Fin n × ℕ)}
    (hFeas : Feasible cap maxLegs alloc)
    (hLegs : supportLegs alloc = head :: tail) :
    let residual := reindexedResidualAlloc (hFeas := hFeas) (hLegs := hLegs)
    supportLegs residual = tail ∧
      Feasible cap tail.length residual := by
  dsimp [reindexedResidualAlloc]
  let hPacket := feasible_support_cons_residual_alloc_packet
    (hFeas := hFeas) (hLegs := hLegs)
  rcases hPacket with ⟨hResidualLegs, hResidualFeasFor⟩
  exact ⟨
    (by simpa [supportLegs_reindexAlloc_eq] using hResidualLegs),
    feasible_reindexAlloc_of_feasibleFor hResidualFeasFor
  ⟩

end ExactOutManyPoolReindexedResidualAllocation
end ZenoDEX
end TauSwap
