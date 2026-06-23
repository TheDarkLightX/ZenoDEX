import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCompleteness
import Proofs.ZenoDEXExactOutManyPoolSupportPresentation

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolPrefilterSupportBridge

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation

noncomputable section

/-!
# Exact-Out Many-Pool Prefilter Support Bridge

This file does **not** prove that the current runtime prefilter is complete.
Instead, it isolates the exact remaining proof obligation in a form that can be
reused by the many-pool generator-completeness program:

- define the selected-pool support condition explicitly,
- show that if every feasible bounded allocation's positive-leg support lies
  inside the selected pool set,
- then the existing selected-domain completeness theorem already upgrades
  emitted-domain minimality to bounded-domain minimality.

This keeps the missing prefilter relation separate from the already-proved
canonicalization machinery.
-/

/-- A bounded allocation stays inside the selected prefilter set iff every
positive-output support index belongs to `selected`. -/
def SupportInside {n Q : ℕ}
    (selected : Finset (Fin n))
    (alloc : Alloc n Q) : Prop :=
  supportSet alloc ⊆ selected

/-- Feasibility together with the support-inside-selected-pools condition. -/
def SelectedFeasible {n Q : ℕ}
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (selected : Finset (Fin n))
    (alloc : Alloc n Q) : Prop :=
  Feasible cap maxLegs alloc ∧ SupportInside selected alloc

theorem supportInside_iff_forall_positive_mem
    {n Q : ℕ}
    {selected : Finset (Fin n)}
    {alloc : Alloc n Q} :
    SupportInside selected alloc ↔
      ∀ i, 0 < (alloc i : ℕ) → i ∈ selected := by
  constructor
  · intro hInside i hPos
    exact hInside ((mem_supportSet_iff).2 hPos)
  · intro hPointwise i hMem
    exact hPointwise i ((mem_supportSet_iff).1 hMem)

theorem selectedFeasible_iff_feasible_of_support_sound
    {n Q : ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {selected : Finset (Fin n)}
    (hSupportSound : ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc → SupportInside selected alloc)
    {alloc : Alloc n Q} :
    SelectedFeasible cap maxLegs selected alloc ↔ Feasible cap maxLegs alloc := by
  constructor
  · intro hSel
    exact hSel.1
  · intro hFeas
    exact ⟨hFeas, hSupportSound alloc hFeas⟩

/-- If the selected prefilter set is support-sound for every feasible bounded
allocation, then minimizing over allocations whose support stays inside the
selected set is already minimizing over the full bounded feasible domain. -/
theorem support_sound_implies_selected_domain_search_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    {allocStar : Alloc n Q}
    (hSupportSound : ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc → SupportInside selected alloc)
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (SelectedFeasible cap maxLegs selected) routeKey ∧
      ∀ y ∈ emittedKeySet (SelectedFeasible cap maxLegs selected) routeKey, routeKey allocStar ≤ y := by
  have hComplete :
      ∀ alloc, SelectedFeasible cap maxLegs selected alloc ↔ Feasible cap maxLegs alloc :=
    fun alloc => selectedFeasible_iff_feasible_of_support_sound hSupportSound
  exact selected_domain_search_complete
    (emit := SelectedFeasible cap maxLegs selected)
    routeKey
    hComplete
    hFeas
    hMin

/-- The same support-soundness hypothesis is enough to recover existence and
uniqueness of the canonical minimum over the selected-support emitted domain
whenever the full bounded domain has any feasible witness. -/
theorem support_sound_implies_selected_domain_canonical_exists
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    (hSupportSound : ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc → SupportInside selected alloc)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (SelectedFeasible cap maxLegs selected) routeKey ∧
        ∀ y ∈ emittedKeySet (SelectedFeasible cap maxLegs selected) routeKey, k ≤ y := by
  have hComplete :
      ∀ alloc, SelectedFeasible cap maxLegs selected alloc ↔ Feasible cap maxLegs alloc :=
    fun alloc => selectedFeasible_iff_feasible_of_support_sound hSupportSound
  exact selected_domain_canonical_exists
    (emit := SelectedFeasible cap maxLegs selected)
    routeKey
    hComplete
    hWitness

end
end ExactOutManyPoolPrefilterSupportBridge
end ZenoDEX
end TauSwap
