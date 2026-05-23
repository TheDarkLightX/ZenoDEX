import Proofs.ZenoDEXExactOutManyPoolQuotedPathStreamBridge
import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedCandidateBridge

open scoped Classical

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolPathWitnessCanonicalCandidateMinimum

open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open ExactOutManyPoolQuotedPathStreamBridge
open ExactOutManyPoolOrderedQuotedCandidateBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability
open TauSwap.Routing.ExactOutManyPoolCpmmQuoteTotality

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs

noncomputable section

/-!
# Exact-Out Many-Pool Path-Witness Canonical Candidate Minimum

This file promotes the Aristotle-discovered path-witness bridge. It composes
path-only emitted witness streams with the canonical feasible allocation-to-
candidate map, removing the earlier abstract compatibility assumption from this
certificate surface.

The remaining runtime obligation is still explicit: the Python emitter must
provide or verify `PathWitnessStream(Set)Covers`. Given that cover contract, the
Lean bridge derives quote replay and a unique feasible canonical candidate
minimum.
-/

theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamCover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      PathWitnessStreamCovers
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs) :
    ∃ allocStar : Alloc n Q, Feasible cap maxLegs allocStar ∧
      canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal
          allocStar =
        guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc →
        keyLe
          guardInputs.runtimeChoice
          (canonicalCandidateOfQuoted
            (Q := Q)
            quoteIn
            cap
            maxLegs
            candidateOfQuoted
            hQuoteTotal
            alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamCover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf :=
        canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      hCover
      (by
        intro alloc quotedLegs hFeas hSupport hQuoted
        exact canonicalCandidateOfQuoted_eq_candidateOfQuoted
          (candidateOfQuoted := candidateOfQuoted)
          hQuoteTotal
          hFeas
          hSupport
          hQuoted)

theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamSetCover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      PathWitnessStreamSetCovers
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs) :
    ∃ allocStar : Alloc n Q, Feasible cap maxLegs allocStar ∧
      canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal
          allocStar =
        guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc : Alloc n Q, Feasible cap maxLegs alloc →
        keyLe
          guardInputs.runtimeChoice
          (canonicalCandidateOfQuoted
            (Q := Q)
            quoteIn
            cap
            maxLegs
            candidateOfQuoted
            hQuoteTotal
            alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamSetCover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf :=
        canonicalCandidateOfQuoted
          (Q := Q)
          quoteIn
          cap
          maxLegs
          candidateOfQuoted
          hQuoteTotal)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      hCover
      (by
        intro alloc quotedLegs hFeas hSupport hQuoted
        exact canonicalCandidateOfQuoted_eq_candidateOfQuoted
          (candidateOfQuoted := candidateOfQuoted)
          hQuoteTotal
          hFeas
          hSupport
          hQuoted)

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_pathWitnessStreamSetCover_canonicalCandidate
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      PathWitnessStreamSetCovers
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              cap
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                quoteIn
                cap
                maxLegs
                candidateOfQuoted
                hQuoteTotal) ∧
          ∀ y ∈
              feasibleCandidateSet
                cap
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  quoteIn
                  cap
                  maxLegs
                  candidateOfQuoted
                  hQuoteTotal),
            keyLe cand y := by
  rcases
      packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamSetCover_canonicalCandidate
        (quoteIn := quoteIn)
        (cap := cap)
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (domainInputs := domainInputs)
        (guardInputs := guardInputs)
        hPacket
        hQuoteTotal
        hCover with
    ⟨allocStar, hFeas, hCandStar, hQuote, hMin⟩
  let candidateOf :
      Alloc n Q → Candidate :=
    canonicalCandidateOfQuoted
      (Q := Q)
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      hQuoteTotal
  let S := feasibleCandidateSet cap maxLegs candidateOf
  have hMem : guardInputs.runtimeChoice ∈ S := by
    change
      guardInputs.runtimeChoice ∈
        (feasibleSet cap maxLegs).image candidateOf
    exact Finset.mem_image.mpr ⟨allocStar, mem_feasibleSet_of_feasible hFeas, hCandStar⟩
  have hMinSet :
      ∀ y ∈ S, keyLe guardInputs.runtimeChoice y := by
    intro y hy
    change y ∈ (feasibleSet cap maxLegs).image candidateOf at hy
    rcases Finset.mem_image.mp hy with ⟨alloc, hAllocMem, rfl⟩
    exact hMin alloc (by simpa [feasibleSet] using hAllocMem)
  constructor
  · exact hQuote
  · exact ⟨guardInputs.runtimeChoice, ⟨hMem, hMinSet⟩, by
      intro cand hCand
      have hCandLe :
          keyLe cand guardInputs.runtimeChoice :=
        hCand.2 guardInputs.runtimeChoice hMem
      have hRtLe :
          keyLe guardInputs.runtimeChoice cand :=
        hMinSet cand hCand.1
      exact keyLe_antisymm hCandLe hRtLe⟩

theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_cpmm_pathWitnessStreamSetCover_canonicalCandidate
    {n Q : ℕ}
    (pools : Fin n → CpmmPool)
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses :
      List
        (QuotedPathWitness
          (Q := Q)
          (quoteIn pools)
          (fun i => capOut (pools i))
          maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hRin : ∀ i, 0 < (pools i).reserveIn)
    (hFee : ∀ i, (pools i).feeBps < BPS)
    (hCover :
      PathWitnessStreamSetCovers
        (quoteIn pools)
        (fun i => capOut (pools i))
        maxLegs
        candidateOfQuoted
        witnesses
        guardInputs) :
    (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∃! cand,
        cand ∈
            feasibleCandidateSet
              (fun i => capOut (pools i))
              maxLegs
              (canonicalCandidateOfQuoted
                (Q := Q)
                (quoteIn pools)
                (fun i => capOut (pools i))
                maxLegs
                candidateOfQuoted
                (quoteTotalOnPositiveBounded pools hRin hFee)) ∧
          ∀ y ∈
              feasibleCandidateSet
                (fun i => capOut (pools i))
                maxLegs
                (canonicalCandidateOfQuoted
                  (Q := Q)
                  (quoteIn pools)
                  (fun i => capOut (pools i))
                  maxLegs
                  candidateOfQuoted
                  (quoteTotalOnPositiveBounded pools hRin hFee)),
            keyLe cand y := by
  exact
    packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_pathWitnessStreamSetCover_canonicalCandidate
      (quoteIn := quoteIn pools)
      (cap := fun i => capOut (pools i))
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

end
end ExactOutManyPoolPathWitnessCanonicalCandidateMinimum
end Routing
end TauSwap
