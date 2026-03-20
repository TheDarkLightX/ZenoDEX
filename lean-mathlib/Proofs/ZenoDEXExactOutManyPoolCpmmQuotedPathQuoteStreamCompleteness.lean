import Proofs.ZenoDEXExactOutManyPoolCpmmQuoteTotality
import Proofs.ZenoDEXExactOutManyPoolQuotedPathQuoteStreamCompleteness

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolCpmmQuotedPathQuoteStreamCompleteness

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolQuotedStructuralReachability
open ExactOutManyPoolQuotedPathQuoteStreamCompleteness
open TauSwap.Routing.ExactOutManyPoolCpmmQuoteTotality

noncomputable section

/-!
# Exact-Out Many-Pool CPMM Quoted Path Quote-Stream Completeness

This file specializes the emitted quote-stream completeness bridge to the CPMM
audited setting, where quote totality is already discharged.

The remaining local CPMM generator-side gap is therefore no longer an abstract
path-list theorem. It is exactly the statement that the emitted quote stream
from the selected-domain builder covers every ordered reachable quoted path.
-/

theorem emitOfQuotedPathQuoteStream_iff_feasible_of_cpmm_quoteStreamComplete
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes) :
    ∀ alloc : Alloc n Q,
      emitOfQuotedPathQuoteStream quotes alloc ↔
        Feasible (fun i => capOut (pools i)) maxLegs alloc := by
  exact
    emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_quoteStreamComplete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hComplete

theorem emitOfQuotedPathQuoteStream_iff_feasible_of_cpmm_projectionSetCover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolQuotedPathQuoteStreamCompleteness.OrderedQuotedPathProjectionSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes) :
    ∀ alloc : Alloc n Q,
      emitOfQuotedPathQuoteStream quotes alloc ↔
        Feasible (fun i => capOut (pools i)) maxLegs alloc := by
  exact
    ExactOutManyPoolQuotedPathQuoteStreamCompleteness.emitOfQuotedPathQuoteStream_iff_feasible_of_quoteTotal_and_projectionSetCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem selected_domain_search_complete_of_cpmm_quoteStreamComplete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes)
    {allocStar : Alloc n Q}
    (hFeas : Feasible (fun i => capOut (pools i)) maxLegs allocStar)
    (hMin :
      ∀ alloc,
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey,
        routeKey allocStar ≤ y := by
  exact
    selected_domain_search_complete_of_quoteTotal_and_quoteStreamComplete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hComplete
      hFeas
      hMin

theorem selected_domain_search_complete_of_cpmm_projectionSetCover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolQuotedPathQuoteStreamCompleteness.OrderedQuotedPathProjectionSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes)
    {allocStar : Alloc n Q}
    (hFeas : Feasible (fun i => capOut (pools i)) maxLegs allocStar)
    (hMin :
      ∀ alloc,
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey,
        routeKey allocStar ≤ y := by
  exact
    ExactOutManyPoolQuotedPathQuoteStreamCompleteness.selected_domain_search_complete_of_quoteTotal_and_projectionSetCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hFeas
      hMin

theorem selected_domain_canonical_exists_of_cpmm_quoteStreamComplete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hComplete :
      OrderedQuotedPathQuoteStreamComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes)
    (hWitness : ∃ alloc : Alloc n Q, Feasible (fun i => capOut (pools i)) maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, k ≤ y := by
  exact
    selected_domain_canonical_exists_of_quoteTotal_and_quoteStreamComplete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hComplete
      hWitness

theorem selected_domain_canonical_exists_of_cpmm_projectionSetCover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotes : List (QuotedPathQuote n))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      ExactOutManyPoolQuotedPathQuoteStreamCompleteness.OrderedQuotedPathProjectionSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotes)
    (hWitness : ∃ alloc : Alloc n Q, Feasible (fun i => capOut (pools i)) maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfQuotedPathQuoteStream quotes) routeKey, k ≤ y := by
  exact
    ExactOutManyPoolQuotedPathQuoteStreamCompleteness.selected_domain_canonical_exists_of_quoteTotal_and_projectionSetCover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotes := quotes)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hWitness

end
end ExactOutManyPoolCpmmQuotedPathQuoteStreamCompleteness
end ZenoDEX
end TauSwap
