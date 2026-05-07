import Proofs.ZenoDEXExactOutManyPoolQuotedPathStreamBridge
import Proofs.ZenoDEXExactOutManyPoolOrderedQuotedCandidateBridge

open scoped Classical

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolOrderedPathWitnessShapeLadder

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
# Exact-Out Many-Pool Ordered Path-Witness Shape Ladder

This file refines the path-witness certificate boundary from all quoted
reachable paths to the ordered, leg-bounded selected-domain slice.

The remaining runtime obligation is now the more precise contract:
`OrderedPathWitnessStreamSetCovers`.
-/

/-- Runtime-shaped path-witness cover for the selected-domain slice.

The stream need only cover sorted, leg-bounded quoted paths. Each witness itself
already carries sortedness, length bound, and quoted reachability. -/
def OrderedPathWitnessStreamSetCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs) : Prop :=
  (∀ cand, cand ∈ inputs.first :: inputs.rest ↔
      cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs)) ∧
    ∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ w ∈ witnesses, w.quotedLegs = quotedLegs

/-- Ordered path-witness cover implies the existing ordered quoted-path set
cover by projecting witnesses to their quoted path payloads. -/
theorem orderedQuotedPathSetCovers_of_orderedPathWitnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      OrderedPathWitnessStreamSetCovers
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        witnesses
        inputs) :
    ExactOutManyPoolOrderedQuotedPresentationBridge.OrderedQuotedPathSetCovers
      (Q := Q)
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      (witnesses.map (fun w => w.quotedLegs))
      inputs := by
  unfold OrderedPathWitnessStreamSetCovers at hCover
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_map] using hCover.1
  · simp +zetaDelta
    exact fun w _hw => ⟨w.supportSorted, w.lengthBound, w.quotedReachable⟩
  · grind

/-- Ideal selected-domain bridge: ordered path-witness set cover plus quote
totality and packet success gives quote replay and a unique feasible canonical
candidate minimum. -/
theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_orderedPathWitnessStreamSetCover_canonicalCandidate
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
      OrderedPathWitnessStreamSetCovers
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
  apply_rules
    [packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_ordered_path_set_cover_canonicalCandidate]
  exact
    orderedQuotedPathSetCovers_of_orderedPathWitnessStreamSetCover
      candidateOfQuoted
      witnesses
      guardInputs
      hCover

/-- CPMM specialization of the ideal selected-domain bridge. -/
theorem packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_cpmm_orderedPathWitnessStreamSetCover_canonicalCandidate
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
      OrderedPathWitnessStreamSetCovers
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
  convert
    packetOk_implies_exists_unique_feasibleCandidateSet_minimum_of_quoteTotal_and_orderedPathWitnessStreamSetCover_canonicalCandidate
      (quoteIn := fun i x => quoteIn pools i x)
      (cap := fun i => capOut (pools i))
      (maxLegs := maxLegs)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      (quoteTotalOnPositiveBounded pools hRin hFee)
      hCover

end
end ExactOutManyPoolOrderedPathWitnessShapeLadder
end Routing
end TauSwap
