import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Proofs.ZenoDEXExactOutCanonicalMinimizer

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolSelectedDomainCompleteness

open ExactOutCanonicalMinimizer

noncomputable section

/-!
# Exact-Out Many-Pool Selected-Domain Completeness

This file does **not** claim that the current many-pool selector is globally
complete over all active pools. Instead, it proves the next honest bridge:

- fix a bounded audited pool domain,
- model bounded integer allocations over that domain,
- assume the emitted generator is pointwise complete for that bounded audited
  domain,
- conclude that minimizing over the emitted set is the same as minimizing over
  the full bounded audited domain.

This is the formal shape needed before the repo can attack the harder selector
completeness question.
-/

/-- Bounded exact-out allocation over `n` audited pools for total demand `Q`.
Each component is in `[0, Q]`, so the allocation space is finite. -/
abbrev Alloc (n Q : ℕ) := Fin n → Fin (Q + 1)

/-- Number of nonzero legs used by a bounded allocation. -/
def usedLegCount {n Q : ℕ} (alloc : Alloc n Q) : ℕ :=
  (Finset.univ.filter fun i => (alloc i : ℕ) > 0).card

/-- Feasibility over a fixed audited pool domain:
- each leg respects its audited capacity bound,
- total emitted output is exactly `Q`,
- the number of nonzero legs is bounded by `maxLegs`. -/
def Feasible {n Q : ℕ}
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (alloc : Alloc n Q) : Prop :=
  (∀ i, (alloc i : ℕ) ≤ cap i) ∧
    (∑ i, (alloc i : ℕ)) = Q ∧
    usedLegCount alloc ≤ maxLegs

/-- Finite set of all feasible bounded allocations over the audited domain. -/
def feasibleSet {n Q : ℕ}
    (cap : Fin n → ℕ)
    (maxLegs : ℕ) : Finset (Alloc n Q) :=
  Finset.univ.filter (Feasible cap maxLegs)

/-- Finite set of allocations actually emitted by a generator over the same
audited domain. -/
def emittedSet {n Q : ℕ}
    (emit : Alloc n Q → Prop) [DecidablePred emit] : Finset (Alloc n Q) :=
  Finset.univ.filter emit

/-- Canonical-key image of the full feasible audited-domain set. -/
def feasibleKeySet {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (routeKey : Alloc n Q → Key PoolId) : Finset (Key PoolId) :=
  (feasibleSet cap maxLegs).image routeKey

/-- Canonical-key image of the emitted audited-domain set. -/
def emittedKeySet {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (emit : Alloc n Q → Prop) [DecidablePred emit]
    (routeKey : Alloc n Q → Key PoolId) : Finset (Key PoolId) :=
  (emittedSet emit).image routeKey

theorem mem_feasibleSet_of_feasible {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ} {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc) :
    alloc ∈ feasibleSet cap maxLegs := by
  simp [feasibleSet, hFeas]

theorem mem_emittedSet_of_emit {n Q : ℕ}
    {emit : Alloc n Q → Prop} [DecidablePred emit] {alloc : Alloc n Q}
    (hEmit : emit alloc) :
    alloc ∈ emittedSet emit := by
  simp [emittedSet, hEmit]

theorem feasibleKeySet_nonempty_of_witness {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ} {routeKey : Alloc n Q → Key PoolId}
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc) :
    (feasibleKeySet cap maxLegs routeKey).Nonempty := by
  exact ⟨routeKey alloc, Finset.mem_image.mpr ⟨alloc, mem_feasibleSet_of_feasible hFeas, rfl⟩⟩

theorem emittedSet_eq_feasibleSet_of_pointwise_iff {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop} [DecidablePred emit]
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc) :
    emittedSet emit = feasibleSet cap maxLegs := by
  ext alloc
  simp [emittedSet, feasibleSet, hComplete alloc]

theorem emittedKeySet_eq_feasibleKeySet_of_pointwise_iff
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop} [DecidablePred emit]
    {routeKey : Alloc n Q → Key PoolId}
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc) :
    emittedKeySet emit routeKey = feasibleKeySet cap maxLegs routeKey := by
  simp [emittedKeySet, feasibleKeySet, emittedSet_eq_feasibleSet_of_pointwise_iff hComplete]

/-- If the emitted generator is pointwise complete for the bounded audited
domain, then any witness minimizing the canonical key over the full feasible
audited domain is already canonical over the emitted set. -/
theorem selected_domain_search_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop} [DecidablePred emit]
    (routeKey : Alloc n Q → Key PoolId)
    {allocStar : Alloc n Q}
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc)
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet emit routeKey ∧
      ∀ y ∈ emittedKeySet emit routeKey, routeKey allocStar ≤ y := by
  have hEq :
      emittedKeySet emit routeKey = feasibleKeySet cap maxLegs routeKey :=
    emittedKeySet_eq_feasibleKeySet_of_pointwise_iff hComplete
  have hMemFeasible : routeKey allocStar ∈ feasibleKeySet cap maxLegs routeKey := by
    exact Finset.mem_image.mpr ⟨allocStar, mem_feasibleSet_of_feasible hFeas, rfl⟩
  constructor
  · simpa [hEq] using hMemFeasible
  · intro y hy
    have hy' : y ∈ feasibleKeySet cap maxLegs routeKey := by
      simpa [hEq] using hy
    rcases Finset.mem_image.mp hy' with ⟨alloc, hAllocMem, rfl⟩
    exact hMin alloc (by simpa [feasibleSet] using hAllocMem)

/-- Once emitted completeness holds pointwise, the emitted key set has a unique
canonical minimum whenever the bounded audited domain has any feasible witness. -/
theorem selected_domain_canonical_exists
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop} [DecidablePred emit]
    (routeKey : Alloc n Q → Key PoolId)
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k, k ∈ emittedKeySet emit routeKey ∧ ∀ y ∈ emittedKeySet emit routeKey, k ≤ y := by
  rcases hWitness with ⟨alloc, hFeas⟩
  have hNonemptyFeasible :
      (feasibleKeySet cap maxLegs routeKey).Nonempty :=
    feasibleKeySet_nonempty_of_witness (routeKey := routeKey) hFeas
  have hEq :
      emittedKeySet emit routeKey = feasibleKeySet cap maxLegs routeKey :=
    emittedKeySet_eq_feasibleKeySet_of_pointwise_iff hComplete
  have hNonemptyEmitted :
      (emittedKeySet emit routeKey).Nonempty := by
    simpa [hEq] using hNonemptyFeasible
  exact exists_unique_canonical (emittedKeySet emit routeKey) hNonemptyEmitted

end
end ExactOutManyPoolSelectedDomainCompleteness
end ZenoDEX
end TauSwap
