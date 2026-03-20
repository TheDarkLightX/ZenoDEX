import Proofs.ZenoDEXExactOutManyPoolQuotedPresentationBridge

/-!
# ZenoDEX Exact-Out Many-Pool Quoted Witness-Stream Bridge

This file turns the remaining abstract emitted-stream presentation assumption into
a concrete finite witness-list cover.

Instead of assuming `QuotedPresentedBy` directly, it packages the emitted
guarded stream as a list of quoted-path witnesses, each carrying:

- a bounded audited allocation witness,
- the quoted recursive path for that allocation,
- the support agreement between the two.

If that witness list exactly maps to the guarded candidate stream and covers
every quoted reachable path, then the abstract `QuotedPresentedBy` obligation is
discharged. This keeps the remaining local gap explicit: prove the actual
runtime-emitted candidate stream equals such a witness-list image.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolQuotedWitnessStreamBridge

open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open ExactOutManyPoolQuotedPresentationBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolQuotedPresentationBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolQuotedPresentationBridge.GuardInputs

/-- Concrete emitted-stream witness for one quoted reachable path. -/
structure QuotedWitness
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ) where
  alloc : Alloc n Q
  quotedLegs : List (QuotedLeg n)
  feasible : Feasible cap maxLegs alloc
  supportEq : supportOfQuotedLegs quotedLegs = supportLegs alloc
  quotedReachable : QuotedStructurallyReachable quoteIn cap Q quotedLegs

/-- A guarded candidate stream is concretely covered by a finite witness list if
its candidate list is exactly the image of those witnesses and every quoted
reachable path appears in the list. -/
def WitnessStreamCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs) : Prop :=
  inputs.first :: inputs.rest =
      witnesses.map (fun w => candidateOfQuoted w.quotedLegs) ∧
    ∀ quotedLegs,
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ w ∈ witnesses, w.quotedLegs = quotedLegs

/-- Weaker witness-stream cover that keeps only candidate-stream membership
equivalence, not literal list equality. -/
def WitnessStreamSetCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs) : Prop :=
  (∀ cand, cand ∈ inputs.first :: inputs.rest ↔
      cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs)) ∧
    ∀ quotedLegs,
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ w ∈ witnesses, w.quotedLegs = quotedLegs

theorem witnessStreamSetCovers_of_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover : WitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    WitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  exact ⟨by
      intro cand
      rw [hStream], hAllQuoted⟩

/-- A concrete witness-list cover is enough to discharge the abstract
`QuotedPresentedBy` obligation. -/
theorem quotedPresentedBy_of_witnessStreamCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover : WitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
      QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  constructor
  · intro quotedLegs hQuoted
    rcases hAllQuoted quotedLegs hQuoted with ⟨w, hwMem, hwEq⟩
    have hMemMap :
        candidateOfQuoted w.quotedLegs ∈
          witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := by
      exact List.mem_map.mpr ⟨w, hwMem, rfl⟩
    rw [hStream]
    simpa [hwEq] using hMemMap
  · intro cand hCand
    have hCandMap :
        cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := by
      rw [← hStream]
      exact hCand
    rcases List.mem_map.mp hCandMap with ⟨w, hwMem, hCandEq⟩
    exact ⟨w.alloc, w.quotedLegs, w.feasible, w.supportEq, w.quotedReachable, hCandEq⟩

/-- Candidate-stream membership equivalence plus quoted witness coverage is
already enough to discharge `QuotedPresentedBy`. -/
theorem quotedPresentedBy_of_witnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover : WitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  constructor
  · intro quotedLegs hQuoted
    rcases hAllQuoted quotedLegs hQuoted with ⟨w, hwMem, hwEq⟩
    have hMemMap :
        candidateOfQuoted w.quotedLegs ∈
          witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := by
      exact List.mem_map.mpr ⟨w, hwMem, rfl⟩
    exact (hStream _).2 (by simpa [hwEq] using hMemMap)
  · intro cand hCand
    have hCandMap :
        cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := (hStream _).1 hCand
    rcases List.mem_map.mp hCandMap with ⟨w, hwMem, hCandEq⟩
    exact ⟨w.alloc, w.quotedLegs, w.feasible, w.supportEq, w.quotedReachable, hCandEq⟩

/-- Quote totality plus a concrete witness-list cover upgrades certified packet
success to bounded audited-domain quote replay and minimality. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover : WitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar, Feasible cap maxLegs allocStar ∧
      candidateOf allocStar = guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc, Feasible cap maxLegs alloc →
        keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_quoted_presentation
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (quotedPresentedBy_of_witnessStreamCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := guardInputs)
        hCover)
      hCompat

/-- The same packet bridge only needs candidate-stream membership equivalence,
not literal witness-list equality. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedWitness (Q := Q) quoteIn cap maxLegs))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover : WitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar, Feasible cap maxLegs allocStar ∧
      candidateOf allocStar = guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc, Feasible cap maxLegs alloc →
        keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  exact
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_quoted_presentation
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (quotedPresentedBy_of_witnessStreamSetCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := guardInputs)
        hCover)
      hCompat

end ExactOutManyPoolQuotedWitnessStreamBridge
end Routing
end TauSwap
