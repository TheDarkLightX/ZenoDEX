import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedPresentationBridge
import Proofs.ZenoDEXExactOutManyPoolQuotedPathRealization
import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCompleteness

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolOrderedQuotedPathCompleteness

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolQuotedStructuralReachability
open ExactOutManyPoolQuotedPathRealization
open TauSwap.Routing.ExactOutManyPoolOrderedQuotedPresentationBridge

noncomputable section

/-!
# Exact-Out Many-Pool Ordered Quoted Path Completeness

This file upgrades the ordered quoted-path cover frontier from a packet-level
presentation theorem to a pointwise completeness theorem over the bounded audited
allocation space itself.

It proves that if a list of quoted recursive paths contains exactly the sorted,
leg-bounded quoted paths reachable in the audited selected domain, then the
allocation predicate "presented by one of those quoted paths" is equivalent to
bounded audited feasibility. That is the exact hypothesis shape needed by the
existing selected-domain completeness theorems.
-/

/-- Allocation is emitted by an ordered quoted-path list when one of those
quoted paths realizes exactly its `supportLegs` presentation. -/
def emitOfOrderedQuotedPaths {n Q : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (alloc : Alloc n Q) : Prop :=
  ∃ quotedLegs ∈ quotedPaths, supportOfQuotedLegs quotedLegs = supportLegs alloc

/-- Forget the candidate-stream equality from `OrderedQuotedPathListCovers` and
keep only the exact ordered-path coverage facts. -/
def OrderedQuotedPathComplete
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (quotedPaths : List (List (QuotedLeg n))) : Prop :=
  (∀ quotedLegs ∈ quotedPaths,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT ∧
        quotedLegs.length ≤ maxLegs ∧
        QuotedStructurallyReachable quoteIn cap Q quotedLegs) ∧
    (∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        quotedLegs ∈ quotedPaths)

theorem orderedQuotedPathComplete_of_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    OrderedQuotedPathComplete (Q := Q) quoteIn cap maxLegs quotedPaths := by
  rcases hCover with ⟨_hStream, hWell, hAllOrdered⟩
  exact ⟨hWell, hAllOrdered⟩

theorem orderedQuotedPathComplete_of_set_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    OrderedQuotedPathComplete (Q := Q) quoteIn cap maxLegs quotedPaths := by
  rcases hCover with ⟨_hStream, hWell, hAllOrdered⟩
  exact ⟨hWell, hAllOrdered⟩

/-- The concrete `supportLegs` normal form uniquely determines a bounded
allocation. -/
theorem alloc_eq_of_supportLegs_eq
    {n Q : ℕ}
    {alloc₁ alloc₂ : Alloc n Q}
    (hLegs : supportLegs alloc₁ = supportLegs alloc₂) :
    alloc₁ = alloc₂ := by
  funext i
  apply Fin.ext
  by_cases hPos₁ : 0 < (alloc₁ i : ℕ)
  · have hMem₁ : (i, (alloc₁ i : ℕ)) ∈ supportLegs alloc₁ :=
        (supportLeg_mem_iff).2 ⟨rfl, hPos₁⟩
    have hMem₂ : (i, (alloc₁ i : ℕ)) ∈ supportLegs alloc₂ := by
      simpa [hLegs] using hMem₁
    exact (supportLeg_mem_iff.1 hMem₂).1
  · have hZero₁ : (alloc₁ i : ℕ) = 0 := Nat.eq_zero_of_not_pos hPos₁
    by_cases hPos₂ : 0 < (alloc₂ i : ℕ)
    · have hMem₂ : (i, (alloc₂ i : ℕ)) ∈ supportLegs alloc₂ :=
          (supportLeg_mem_iff).2 ⟨rfl, hPos₂⟩
      have hMem₁ : (i, (alloc₂ i : ℕ)) ∈ supportLegs alloc₁ := by
        simpa [hLegs] using hMem₂
      exact False.elim (hPos₁ ((supportLeg_mem_iff.1 hMem₁).2))
    · have hZero₂ : (alloc₂ i : ℕ) = 0 := Nat.eq_zero_of_not_pos hPos₂
      simp [hZero₁, hZero₂]

theorem emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hPathComplete : OrderedQuotedPathComplete (Q := Q) quoteIn cap maxLegs quotedPaths) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔ Feasible cap maxLegs alloc := by
  intro alloc
  constructor
  · rintro ⟨quotedLegs, hMem, hSupport⟩
    rcases hPathComplete.1 quotedLegs hMem with ⟨hSorted, hLen, hQuoted⟩
    rcases exists_alloc_of_sorted_quoted_presentation
        (cap := cap)
        (maxLegs := maxLegs)
        (quotedLegs := quotedLegs)
        hQuoted
        hSorted
        hLen with
      ⟨alloc', hFeas', hSupport'⟩
    have hLegEq : supportLegs alloc = supportLegs alloc' := by
      exact hSupport.symm.trans hSupport'
    have hEqAlloc : alloc = alloc' := alloc_eq_of_supportLegs_eq hLegEq
    simpa [hEqAlloc] using hFeas'
  · intro hFeas
    rcases quoted_of_feasible_supportLegs
        (quoteIn := quoteIn)
        (cap := cap)
        (alloc := alloc)
        hQuoteTotal
        hFeas with
      ⟨quotedLegs, hSupport, hQuoted⟩
    rcases feasible_has_sorted_support_presentation (hFeas := hFeas) with
      ⟨hSorted, _hNodup, hLen, _hSum, _hPos, _hCap⟩
    have hQuotedSorted : ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT := by
      simpa [hSupport] using hSorted
    have hQuotedLen : quotedLegs.length ≤ maxLegs := by
      have hLenEq : quotedLegs.length = (supportLegs alloc).length := by
        simpa [supportOfQuotedLegs] using congrArg List.length hSupport
      rw [hLenEq]
      exact hLen
    exact ⟨quotedLegs, hPathComplete.2 quotedLegs hQuotedSorted hQuotedLen hQuoted, hSupport⟩

theorem emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔ Feasible cap maxLegs alloc := by
  exact
    emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
      (quotedPaths := quotedPaths)
      hQuoteTotal
      (orderedQuotedPathComplete_of_list_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hCover)

theorem emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_set_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔ Feasible cap maxLegs alloc := by
  exact
    emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
      (quotedPaths := quotedPaths)
      hQuoteTotal
      (orderedQuotedPathComplete_of_set_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hCover)

theorem selected_domain_search_complete_of_quoteTotal_and_ordered_path_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hPathComplete : OrderedQuotedPathComplete (Q := Q) quoteIn cap maxLegs quotedPaths)
    {allocStar : Alloc n Q}
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, routeKey allocStar ≤ y := by
  exact selected_domain_search_complete
    (emit := emitOfOrderedQuotedPaths quotedPaths)
    (routeKey := routeKey)
    (hComplete :=
      emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
        (quotedPaths := quotedPaths)
        hQuoteTotal
        hPathComplete)
    hFeas
    hMin

theorem selected_domain_search_complete_of_quoteTotal_and_ordered_path_set_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    {allocStar : Alloc n Q}
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, routeKey allocStar ≤ y := by
  exact selected_domain_search_complete
    (emit := emitOfOrderedQuotedPaths quotedPaths)
    (routeKey := routeKey)
    (hComplete :=
      emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_set_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hQuoteTotal
        hCover)
    hFeas
    hMin

theorem selected_domain_canonical_exists_of_quoteTotal_and_ordered_path_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hPathComplete : OrderedQuotedPathComplete (Q := Q) quoteIn cap maxLegs quotedPaths)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, k ≤ y := by
  exact selected_domain_canonical_exists
    (emit := emitOfOrderedQuotedPaths quotedPaths)
    (routeKey := routeKey)
    (hComplete :=
      emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
        (quotedPaths := quotedPaths)
        hQuoteTotal
        hPathComplete)
    hWitness

theorem selected_domain_canonical_exists_of_quoteTotal_and_ordered_path_set_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, k ≤ y := by
  exact selected_domain_canonical_exists
    (emit := emitOfOrderedQuotedPaths quotedPaths)
    (routeKey := routeKey)
    (hComplete :=
      emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_set_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hQuoteTotal
        hCover)
    hWitness

end
end ExactOutManyPoolOrderedQuotedPathCompleteness
end ZenoDEX
end TauSwap
