import Proofs.ZenoDEXExactOutManyPoolCpmmQuoteTotality
import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedPathCompleteness

open scoped Classical

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolCpmmOrderedQuotedPathCompleteness

open ExactOutCanonicalMinimizer
open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolQuotedStructuralReachability
open ExactOutManyPoolOrderedQuotedPathCompleteness
open TauSwap.Routing.ExactOutManyPoolCpmmQuoteTotality
open TauSwap.Routing.ExactOutManyPoolOrderedQuotedPresentationBridge

noncomputable section

/-!
# Exact-Out Many-Pool CPMM Ordered Quoted Path Completeness

This file specializes the ordered quoted-path completeness bridge to the CPMM
audited setting, where quote totality is already discharged.

The remaining local CPMM generator-side gap is therefore no longer a theorem
about quoted reachability or feasibility. It is exactly the emitted ordered
quoted-path list-cover obligation.
-/

theorem emitOfOrderedQuotedPaths_iff_feasible_of_cpmm_ordered_path_complete
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hPathComplete :
      OrderedQuotedPathComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotedPaths) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔
        Feasible (fun i => capOut (pools i)) maxLegs alloc := by
  exact
    emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotedPaths := quotedPaths)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hPathComplete

theorem emitOfOrderedQuotedPaths_iff_feasible_of_cpmm_ordered_path_list_cover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔
        Feasible (fun i => capOut (pools i)) maxLegs alloc := by
  exact
    emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_list_cover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (inputs := inputs)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem emitOfOrderedQuotedPaths_iff_feasible_of_cpmm_ordered_path_set_cover
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    ∀ alloc : Alloc n Q,
      emitOfOrderedQuotedPaths quotedPaths alloc ↔
        Feasible (fun i => capOut (pools i)) maxLegs alloc := by
  exact
    ExactOutManyPoolOrderedQuotedPathCompleteness.emitOfOrderedQuotedPaths_iff_feasible_of_quoteTotal_and_ordered_path_set_cover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (inputs := inputs)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

theorem selected_domain_search_complete_of_cpmm_ordered_path_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hPathComplete :
      OrderedQuotedPathComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotedPaths)
    {allocStar : Alloc n Q}
    (hFeas : Feasible (fun i => capOut (pools i)) maxLegs allocStar)
    (hMin :
      ∀ alloc,
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey,
        routeKey allocStar ≤ y := by
  exact
    selected_domain_search_complete_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotedPaths := quotedPaths)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hPathComplete
      hFeas
      hMin

theorem selected_domain_search_complete_of_cpmm_ordered_path_list_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    {allocStar : Alloc n Q}
    (hFeas : Feasible (fun i => capOut (pools i)) maxLegs allocStar)
    (hMin :
      ∀ alloc,
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey,
        routeKey allocStar ≤ y := by
  exact
    selected_domain_search_complete_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotedPaths := quotedPaths)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      (orderedQuotedPathComplete_of_list_cover
        (Q := Q)
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hCover)
      hFeas
      hMin

theorem selected_domain_search_complete_of_cpmm_ordered_path_set_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    {allocStar : Alloc n Q}
    (hFeas : Feasible (fun i => capOut (pools i)) maxLegs allocStar)
    (hMin :
      ∀ alloc,
        Feasible (fun i => capOut (pools i)) maxLegs alloc →
          routeKey allocStar ≤ routeKey alloc) :
    routeKey allocStar ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
      ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey,
        routeKey allocStar ≤ y := by
  exact
    ExactOutManyPoolOrderedQuotedPathCompleteness.selected_domain_search_complete_of_quoteTotal_and_ordered_path_set_cover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (inputs := inputs)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hFeas
      hMin

theorem selected_domain_canonical_exists_of_cpmm_ordered_path_complete
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (quotedPaths : List (List (QuotedLeg n)))
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hPathComplete :
      OrderedQuotedPathComplete
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        quotedPaths)
    (hWitness : ∃ alloc : Alloc n Q, Feasible (fun i => capOut (pools i)) maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, k ≤ y := by
  exact
    selected_domain_canonical_exists_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotedPaths := quotedPaths)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hPathComplete
      hWitness

theorem selected_domain_canonical_exists_of_cpmm_ordered_path_list_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    (hWitness : ∃ alloc : Alloc n Q, Feasible (fun i => capOut (pools i)) maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, k ≤ y := by
  exact
    selected_domain_canonical_exists_of_quoteTotal_and_ordered_path_complete
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (quotedPaths := quotedPaths)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      (orderedQuotedPathComplete_of_list_cover
        (Q := Q)
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := inputs)
        hCover)
      hWitness

theorem selected_domain_canonical_exists_of_cpmm_ordered_path_set_cover
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Routing.ExactOutRouteCertificate.Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : Routing.ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs)
    (routeKey : Alloc n Q → Key PoolId)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs)
    (hWitness : ∃ alloc : Alloc n Q, Feasible (fun i => capOut (pools i)) maxLegs alloc) :
    ∃! k,
      k ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey ∧
        ∀ y ∈ emittedKeySet (emitOfOrderedQuotedPaths quotedPaths) routeKey, k ≤ y := by
  exact
    ExactOutManyPoolOrderedQuotedPathCompleteness.selected_domain_canonical_exists_of_quoteTotal_and_ordered_path_set_cover
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (quotedPaths := quotedPaths)
      (inputs := inputs)
      (routeKey := routeKey)
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover
      hWitness

end
end ExactOutManyPoolCpmmOrderedQuotedPathCompleteness
end ZenoDEX
end TauSwap
