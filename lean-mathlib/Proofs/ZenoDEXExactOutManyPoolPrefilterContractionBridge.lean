import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCompleteness
import Proofs.ZenoDEXExactOutManyPoolSupportPresentation

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolPrefilterContractionBridge

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation

noncomputable section

/-!
# Exact-Out Many-Pool Prefilter Contraction Bridge

This file isolates a weaker bridge than support-soundness.

Instead of requiring every feasible bounded allocation to use only selected
pools, require only that every feasible bounded allocation is **dominated** by
some selected-domain allocation under the exact-out route key.

That weaker contraction property is already enough to lift selected-domain
minimality into full bounded-domain minimality. It is also the right next theorem
surface for the many-pool exact-out frontier, because the stronger support-side
hypothesis is already falsified by bounded audits of the current runtime
prefilter.
-/

/-- The selected-domain allocation space safely contracts the full bounded
feasible domain when every feasible allocation is dominated by some
selected-feasible allocation under the route key. -/
def SelectedFeasible {n Q : ℕ}
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (selected : Finset (Fin n))
    (alloc : Alloc n Q) : Prop :=
  Feasible cap maxLegs alloc ∧ supportSet alloc ⊆ selected

/-- The selected-domain allocation space safely contracts the full bounded
feasible domain when every feasible allocation is dominated by some
selected-feasible allocation under the route key. -/
def ContractsToSelected {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (selected : Finset (Fin n))
    (routeKey : Alloc n Q → Key PoolId) : Prop :=
  ∀ alloc, Feasible cap maxLegs alloc →
    ∃ allocSel, SelectedFeasible cap maxLegs selected allocSel ∧
      routeKey allocSel ≤ routeKey alloc

/-- If a selected-domain allocation is minimal over the selected domain and the
selected domain safely contracts the full feasible bounded domain, then that
same allocation is also minimal over the full feasible bounded domain. -/
theorem contraction_implies_selected_domain_global_minimality
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    {allocStar : Alloc n Q}
    (hStarSelected : SelectedFeasible cap maxLegs selected allocStar)
    (hMinSelected : ∀ alloc, SelectedFeasible cap maxLegs selected alloc → routeKey allocStar ≤ routeKey alloc)
    (hContraction : ContractsToSelected cap maxLegs selected routeKey) :
    routeKey allocStar ∈ feasibleKeySet cap maxLegs routeKey ∧
      ∀ y ∈ feasibleKeySet cap maxLegs routeKey, routeKey allocStar ≤ y := by
  have hStarFeasible : Feasible cap maxLegs allocStar := hStarSelected.1
  constructor
  · exact Finset.mem_image.mpr ⟨allocStar, mem_feasibleSet_of_feasible hStarFeasible, rfl⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨alloc, hAllocMem, rfl⟩
    have hFeasible : Feasible cap maxLegs alloc := by
      simpa [feasibleSet] using hAllocMem
    rcases hContraction alloc hFeasible with ⟨allocSel, hSel, hDom⟩
    exact le_trans (hMinSelected allocSel hSel) hDom

/-- Under the same contraction hypothesis, a selected-domain canonical winner is
already the unique canonical minimum of the full bounded feasible-domain key
set. -/
theorem contraction_implies_selected_domain_canonical_exists
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    {allocStar : Alloc n Q}
    (hStarSelected : SelectedFeasible cap maxLegs selected allocStar)
    (hMinSelected : ∀ alloc, SelectedFeasible cap maxLegs selected alloc → routeKey allocStar ≤ routeKey alloc)
    (hContraction : ContractsToSelected cap maxLegs selected routeKey) :
    ∃! k,
      k ∈ feasibleKeySet cap maxLegs routeKey ∧
        ∀ y ∈ feasibleKeySet cap maxLegs routeKey, k ≤ y := by
  have hStar :
      routeKey allocStar ∈ feasibleKeySet cap maxLegs routeKey ∧
        ∀ y ∈ feasibleKeySet cap maxLegs routeKey, routeKey allocStar ≤ y :=
    contraction_implies_selected_domain_global_minimality
      (routeKey := routeKey) hStarSelected hMinSelected hContraction
  exact ⟨routeKey allocStar, hStar, by
    intro k hk
    exact le_antisymm (hk.2 _ hStar.1) (hStar.2 _ hk.1)⟩

end
end ExactOutManyPoolPrefilterContractionBridge
end ZenoDEX
end TauSwap
