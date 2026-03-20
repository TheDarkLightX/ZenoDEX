import Proofs.ZenoDEXExactOutManyPoolQuotedWitnessStreamBridge
import Proofs.ZenoDEXExactOutManyPoolQuotedPathRealization

/-!
# ZenoDEX Exact-Out Many-Pool Quoted Path-Stream Bridge

This file removes one more layer of witness boilerplate from the selected-domain
generator frontier.

The previous witness-stream bridge required each emitted candidate to carry both
its quoted recursive path and an explicit bounded allocation witness. The new
bridge observes that, once a quoted path is known to be ordered and leg-bounded,
the allocation witness can be realized inside Lean by the quoted-path
realization theorem.

So the remaining local generator-side gap can now be stated as exact coverage of
the emitted candidate stream by a finite list of quoted paths, not by a list of
quoted paths paired with separately supplied allocations.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolQuotedPathStreamBridge

open ExactOutRouteCertificate
open ExactOutManyPoolQuotedPresentationBridge
open ExactOutManyPoolQuotedWitnessStreamBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedPathRealization

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolQuotedPresentationBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolQuotedPresentationBridge.GuardInputs

/-- Concrete emitted-stream witness with only the quoted recursive path and the
local facts needed to realize its bounded allocation witness. -/
structure QuotedPathWitness
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ) where
  quotedLegs : List (QuotedLeg n)
  supportSorted : ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT
  lengthBound : quotedLegs.length ≤ maxLegs
  quotedReachable : QuotedStructurallyReachable quoteIn cap Q quotedLegs

/-- Realize the bounded allocation determined by a path witness. -/
noncomputable def QuotedPathWitness.realizedAlloc
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (w : QuotedPathWitness (Q := Q) quoteIn cap maxLegs) : Alloc n Q :=
  Classical.choose <|
    exists_alloc_of_sorted_quoted_presentation
      (cap := cap)
      (maxLegs := maxLegs)
      (quotedLegs := w.quotedLegs)
      w.quotedReachable
      w.supportSorted
      w.lengthBound

theorem QuotedPathWitness.realizedAlloc_feasible
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (w : QuotedPathWitness (Q := Q) quoteIn cap maxLegs) :
    Feasible cap maxLegs w.realizedAlloc := by
  exact
    (Classical.choose_spec <|
      exists_alloc_of_sorted_quoted_presentation
        (cap := cap)
        (maxLegs := maxLegs)
        (quotedLegs := w.quotedLegs)
        w.quotedReachable
        w.supportSorted
        w.lengthBound).1

theorem QuotedPathWitness.supportEq_realizedAlloc
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (w : QuotedPathWitness (Q := Q) quoteIn cap maxLegs) :
    supportOfQuotedLegs w.quotedLegs = supportLegs w.realizedAlloc := by
  exact
    (Classical.choose_spec <|
      exists_alloc_of_sorted_quoted_presentation
        (cap := cap)
        (maxLegs := maxLegs)
        (quotedLegs := w.quotedLegs)
        w.quotedReachable
        w.supportSorted
        w.lengthBound).2

/-- Turn a path-only witness into the earlier allocation-carrying witness. -/
noncomputable def QuotedPathWitness.toQuotedWitness
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (w : QuotedPathWitness (Q := Q) quoteIn cap maxLegs) :
    QuotedWitness (Q := Q) quoteIn cap maxLegs where
  alloc := w.realizedAlloc
  quotedLegs := w.quotedLegs
  feasible := w.realizedAlloc_feasible
  supportEq := w.supportEq_realizedAlloc
  quotedReachable := w.quotedReachable

@[simp] theorem QuotedPathWitness.toQuotedWitness_quotedLegs
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (w : QuotedPathWitness (Q := Q) quoteIn cap maxLegs) :
    w.toQuotedWitness.quotedLegs = w.quotedLegs := rfl

/-- A guarded candidate stream is concretely covered by a finite path-witness
list if its candidate list is exactly the image of those quoted paths and every
quoted reachable path appears in the list. -/
def PathWitnessStreamCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs) : Prop :=
  inputs.first :: inputs.rest =
      witnesses.map (fun w => candidateOfQuoted w.quotedLegs) ∧
    ∀ quotedLegs,
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ w ∈ witnesses, w.quotedLegs = quotedLegs

/-- Weaker path-witness cover that keeps only candidate-stream membership
equivalence, not literal list equality. -/
def PathWitnessStreamSetCovers
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
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        ∃ w ∈ witnesses, w.quotedLegs = quotedLegs

theorem pathWitnessStreamSetCovers_of_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      PathWitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    PathWitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  exact ⟨by
      intro cand
      rw [hStream], hAllQuoted⟩

/-- A path-only witness-list cover realizes the earlier allocation-carrying
cover automatically. -/
theorem witnessStreamCovers_of_pathWitnessStreamCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      PathWitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    WitnessStreamCovers
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      (witnesses.map QuotedPathWitness.toQuotedWitness)
      inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  constructor
  · simpa using hStream
  · intro quotedLegs hQuoted
    rcases hAllQuoted quotedLegs hQuoted with ⟨w, hwMem, hwEq⟩
    exact ⟨
      w.toQuotedWitness,
      List.mem_map.mpr ⟨w, hwMem, rfl⟩,
      by simpa using hwEq
    ⟩

/-- A path-only witness-set cover realizes the weaker witness-set cover
automatically. -/
theorem witnessStreamSetCovers_of_pathWitnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      PathWitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    WitnessStreamSetCovers
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      (witnesses.map QuotedPathWitness.toQuotedWitness)
      inputs := by
  rcases hCover with ⟨hStream, hAllQuoted⟩
  constructor
  · intro cand
    constructor
    · intro hCand
      have hCandMap :
          cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := (hStream _).1 hCand
      simpa using hCandMap
    · intro hCand
      have hCandMap :
          cand ∈ witnesses.map (fun w => candidateOfQuoted w.quotedLegs) := by
        simpa using hCand
      exact (hStream _).2 hCandMap
  · intro quotedLegs hQuoted
    rcases hAllQuoted quotedLegs hQuoted with ⟨w, hwMem, hwEq⟩
    exact ⟨
      w.toQuotedWitness,
      List.mem_map.mpr ⟨w, hwMem, rfl⟩,
      by simpa using hwEq
    ⟩

/-- A path-only witness-list cover is enough to discharge `QuotedPresentedBy`.
-/
theorem quotedPresentedBy_of_pathWitnessStreamCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      PathWitnessStreamCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  exact
    quotedPresentedBy_of_witnessStreamCover
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses.map QuotedPathWitness.toQuotedWitness)
      (inputs := inputs)
      (witnessStreamCovers_of_pathWitnessStreamCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := inputs)
        hCover)

/-- A path-only witness-set cover is enough to discharge `QuotedPresentedBy`.
-/
theorem quotedPresentedBy_of_pathWitnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (witnesses : List (QuotedPathWitness (Q := Q) quoteIn cap maxLegs))
    (inputs : GuardInputs)
    (hCover :
      PathWitnessStreamSetCovers quoteIn cap maxLegs candidateOfQuoted witnesses inputs) :
    QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  exact
    quotedPresentedBy_of_witnessStreamSetCover
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses.map QuotedPathWitness.toQuotedWitness)
      (inputs := inputs)
      (witnessStreamSetCovers_of_pathWitnessStreamSetCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := inputs)
        hCover)

/-- Quote totality plus a path-only witness-list cover upgrades certified packet
success to bounded audited-domain quote replay and minimality. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
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
        guardInputs)
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
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamCover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses.map QuotedPathWitness.toQuotedWitness)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (witnessStreamCovers_of_pathWitnessStreamCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := guardInputs)
        hCover)
      hCompat

/-- The same packet bridge only needs candidate-stream membership equivalence
for path witnesses, not literal list equality. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_pathWitnessStreamSetCover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
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
        guardInputs)
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
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_witnessStreamSetCover
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (witnesses := witnesses.map QuotedPathWitness.toQuotedWitness)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (witnessStreamSetCovers_of_pathWitnessStreamSetCover
        (candidateOfQuoted := candidateOfQuoted)
        (witnesses := witnesses)
        (inputs := guardInputs)
        hCover)
      hCompat

end ExactOutManyPoolQuotedPathStreamBridge
end Routing
end TauSwap
