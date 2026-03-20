import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedPathCompleteness

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolQuotedPathQuoteStreamCompleteness

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolQuotedStructuralReachability
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolOrderedQuotedPathCompleteness

noncomputable section

/-!
# Exact-Out Many-Pool Quoted Path Quote-Stream Completeness

This file moves the selected-domain completeness frontier one step closer to the
runtime generator semantics.

Instead of quantifying over a bare list of quoted recursive paths, it works with
a stream of emitted quote objects that carry those paths directly. This matches
the shape of the Python selected-domain builder more closely than the earlier
path-list frontier, while still staying inside a small abstract Lean model.
-/

/-- Minimal emitted quote shell carrying the quoted recursive path that
determines the selected-domain candidate. -/
structure QuotedPathQuote (n : ℕ) where
  quotedLegs : List (QuotedLeg n)

/-- Allocation is emitted by a quote stream when one emitted quote carries a
quoted path realizing exactly its support presentation. -/
def emitOfQuotedPathQuoteStream {n Q : ℕ}
    (quotes : List (QuotedPathQuote n))
    (alloc : Alloc n Q) : Prop :=
  ∃ q ∈ quotes, supportOfQuotedLegs q.quotedLegs = supportLegs alloc

/-- Concrete quote-stream completeness on the selected audited domain. -/
def OrderedQuotedPathQuoteStreamComplete
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (quotes : List (QuotedPathQuote n)) : Prop :=
  (∀ q ∈ quotes,
      ((supportOfQuotedLegs q.quotedLegs).map Prod.fst).SortedLT ∧
        q.quotedLegs.length ≤ maxLegs ∧
        QuotedStructurallyReachable quoteIn cap Q q.quotedLegs) ∧
    (∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ q ∈ quotes, q.quotedLegs = quotedLegs)

/-- Exact projected-path membership surface for an emitted quote stream: a
quoted path appears in the stream iff it is ordered, leg-bounded, and reachable
in the selected audited domain. -/
def OrderedQuotedPathProjectionSetCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (quotes : List (QuotedPathQuote n)) : Prop :=
  ∀ quotedLegs,
    quotedLegs ∈ quotes.map QuotedPathQuote.quotedLegs ↔
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT ∧
        quotedLegs.length ≤ maxLegs ∧
        QuotedStructurallyReachable quoteIn cap Q quotedLegs

theorem orderedQuotedPathQuoteStreamComplete_of_projectionSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hCover :
      OrderedQuotedPathProjectionSetCovers (Q := Q) quoteIn cap maxLegs quotes) :
    OrderedQuotedPathQuoteStreamComplete (Q := Q) quoteIn cap maxLegs quotes := by
  constructor
  · intro q hqMem
    have hMem :
        q.quotedLegs ∈ quotes.map QuotedPathQuote.quotedLegs := by
      exact List.mem_map.mpr ⟨q, hqMem, rfl⟩
    exact (hCover q.quotedLegs).1 hMem
  · intro quotedLegs hSorted hLen hQuoted
    have hMem :
        quotedLegs ∈ quotes.map QuotedPathQuote.quotedLegs := by
      exact (hCover quotedLegs).2 ⟨hSorted, hLen, hQuoted⟩
    rcases List.mem_map.mp hMem with ⟨q, hqMem, hEq⟩
    exact ⟨q, hqMem, hEq⟩

theorem emitOfQuotedPathQuoteStream_iff_emitOfOrderedQuotedPaths
    {n Q : ℕ}
    (quotes : List (QuotedPathQuote n))
    (alloc : Alloc n Q) :
    emitOfQuotedPathQuoteStream quotes alloc ↔
      emitOfOrderedQuotedPaths (quotes.map QuotedPathQuote.quotedLegs) alloc := by
  constructor
  · rintro ⟨q, hqMem, hSupport⟩
    exact ⟨q.quotedLegs, List.mem_map.mpr ⟨q, hqMem, rfl⟩, hSupport⟩
  · rintro ⟨quotedLegs, hMem, hSupport⟩
    rcases List.mem_map.mp hMem with ⟨q, hqMem, hEq⟩
    exact ⟨q, hqMem, by simpa [hEq] using hSupport⟩

theorem orderedQuotedPathComplete_of_quoteStreamComplete
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete (Q := Q) quoteIn cap maxLegs quotes) :
    OrderedQuotedPathComplete
      (Q := Q)
      quoteIn
      cap
      maxLegs
      (quotes.map QuotedPathQuote.quotedLegs) := by
  constructor
  · intro quotedLegs hMem
    rcases List.mem_map.mp hMem with ⟨q, hqMem, hEq⟩
    simpa [hEq] using hComplete.1 q hqMem
  · intro quotedLegs hSorted hLen hQuoted
    rcases hComplete.2 quotedLegs hSorted hLen hQuoted with ⟨q, hqMem, hEq⟩
    exact List.mem_map.mpr ⟨q, hqMem, hEq⟩

theorem emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_quoteStreamComplete
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete (Q := Q) quoteIn cap maxLegs quotes) :
    ∀ alloc : Alloc n Q,
      emitOfQuotedPathQuoteStream quotes alloc ↔ Feasible cap maxLegs alloc := by
  intro alloc
  rw [emitOfQuotedPathQuoteStream_iff_emitOfOrderedQuotedPaths]
  exact
    emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn)
      (cap := cap)
      (quotedPaths := quotes.map QuotedPathQuote.quotedLegs)
      hQuoteTotal
      (orderedQuotedPathComplete_of_quoteStreamComplete
        (quotes := quotes)
        hComplete)
      alloc

theorem emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_projectionSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathProjectionSetCovers (Q := Q) quoteIn cap maxLegs quotes) :
    ∀ alloc : Alloc n Q,
      emitOfQuotedPathQuoteStream quotes alloc ↔ Feasible cap maxLegs alloc := by
  exact
    emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_quoteStreamComplete
      (quotes := quotes)
      hQuoteTotal
      (orderedQuotedPathQuoteStreamComplete_of_projectionSetCover
        (quotes := quotes)
        hCover)

theorem selected_domain_search_complete_of_quoteTotal_and_quoteStreamComplete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete (Q := Q) quoteIn cap maxLegs quotes)
    {allocStar : Alloc n Q}
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, routeKey allocStar ≤ y := by
  exact selected_domain_search_complete
    (emit := emitOfQuotedPathQuoteStream quotes)
    (routeKey := routeKey)
    (hComplete :=
      emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_quoteStreamComplete
        (quotes := quotes)
        hQuoteTotal
        hComplete)
    hFeas
    hMin

theorem selected_domain_search_complete_of_quoteTotal_and_projectionSetCover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathProjectionSetCovers (Q := Q) quoteIn cap maxLegs quotes)
    {allocStar : Alloc n Q}
    (hFeas : Feasible cap maxLegs allocStar)
    (hMin : ∀ alloc, Feasible cap maxLegs alloc → routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, routeKey allocStar ≤ y := by
  exact selected_domain_search_complete
    (emit := emitOfQuotedPathQuoteStream quotes)
    (routeKey := routeKey)
    (hComplete :=
      emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_projectionSetCover
        (quotes := quotes)
        hQuoteTotal
        hCover)
    hFeas
    hMin

theorem selected_domain_canonical_exists_of_quoteTotal_and_quoteStreamComplete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete (Q := Q) quoteIn cap maxLegs quotes)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, k ≤ y := by
  exact selected_domain_canonical_exists
    (emit := emitOfQuotedPathQuoteStream quotes)
    (routeKey := routeKey)
    (hComplete :=
      emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_quoteStreamComplete
        (quotes := quotes)
        hQuoteTotal
        hComplete)
    hWitness

theorem selected_domain_canonical_exists_of_quoteTotal_and_projectionSetCover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathProjectionSetCovers (Q := Q) quoteIn cap maxLegs quotes)
    (hWitness : ∃ alloc : Alloc n Q, Feasible cap maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, k ≤ y := by
  exact selected_domain_canonical_exists
    (emit := emitOfQuotedPathQuoteStream quotes)
    (routeKey := routeKey)
    (hComplete :=
      emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_projectionSetCover
        (quotes := quotes)
        hQuoteTotal
        hCover)
    hWitness

end
end ExactOutManyPoolQuotedPathQuoteStreamCompleteness
end ZenoDEX
end TauSwap
