import Proofs.ZenoDEXExactOutManyPoolQuotedStructuralReachability
import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCertifiedBridge

/-!
# ZenoDEX Exact-Out Many-Pool Quoted Presentation Bridge

This file connects the new quoted structural reachability theorem back to the
certified packet layer.

The bridge remains intentionally conditional. It does **not** prove that the
shipped runtime quote function is total or that the concrete Python generator
already emits every quoted recursive path. Instead it proves:

- if positive bounded legs always have quoted inputs,
- if every quoted reachable path is represented in the guarded candidate stream,
- and if the candidate mapping for feasible allocations agrees with the quoted
  path mapping on the same support presentation,

then the abstract `PresentedBy` hypothesis used by the certified bridge is
discharged for the full bounded audited feasible domain.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolQuotedPresentationBridge

open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs

/-- Quoted recursive paths faithfully present the guarded candidate stream. -/
def QuotedPresentedBy
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs) : Prop :=
  (∀ quotedLegs,
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        candidateOfQuoted quotedLegs ∈ inputs.first :: inputs.rest) ∧
    (∀ cand ∈ inputs.first :: inputs.rest,
      ∃ alloc : Alloc n Q, ∃ quotedLegs : List (QuotedLeg n),
        Feasible cap maxLegs alloc ∧
          supportOfQuotedLegs quotedLegs = supportLegs alloc ∧
          QuotedStructurallyReachable quoteIn cap Q quotedLegs ∧
          candidateOfQuoted quotedLegs = cand)

/-- Quote totality plus quoted-path presentation is enough to show that every
feasible bounded audited allocation maps into the guarded candidate stream. -/
theorem feasible_candidate_mem_of_quoteTotal_and_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hQuotedPresented : QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∀ alloc, Feasible cap maxLegs alloc →
      candidateOf alloc ∈ inputs.first :: inputs.rest := by
  intro alloc hFeas
  rcases quoted_of_feasible_supportLegs
      (quoteIn := quoteIn)
      (cap := cap)
      (alloc := alloc)
      hQuoteTotal
      hFeas with
    ⟨quotedLegs, hSupport, hQuoted⟩
  have hMemQuoted : candidateOfQuoted quotedLegs ∈ inputs.first :: inputs.rest :=
    hQuotedPresented.1 quotedLegs hQuoted
  have hEq : candidateOf alloc = candidateOfQuoted quotedLegs :=
    hCompat hFeas hSupport hQuoted
  simpa [hEq] using hMemQuoted

/-- The certified bridge's abstract `PresentedBy` hypothesis follows from
quoted recursive-path presentation plus quote totality on positive bounded legs.
-/
theorem presentedBy_of_quoteTotal_and_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hQuotedPresented : QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    PresentedBy (fun alloc => Feasible cap maxLegs alloc) candidateOf inputs := by
  constructor
  · intro alloc hFeas
    exact feasible_candidate_mem_of_quoteTotal_and_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := inputs)
      hQuoteTotal
      hQuotedPresented
      hCompat
      alloc
      hFeas
  · intro cand hMem
    rcases hQuotedPresented.2 cand hMem with
      ⟨alloc, quotedLegs, hFeas, hSupport, hQuoted, hCandQuoted⟩
    have hEq : candidateOf alloc = candidateOfQuoted quotedLegs :=
      hCompat hFeas hSupport hQuoted
    exact ⟨alloc, hFeas, hEq.trans hCandQuoted⟩

/-- Packet success upgrades to bounded audited-domain minimality once the
guarded stream is presented by quoted recursive paths. -/
theorem packetOk_implies_feasible_minimality_of_quoteTotal_and_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hQuotedPresented : QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted guardInputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    ∃ allocStar, Feasible cap maxLegs allocStar ∧
      candidateOf allocStar = guardInputs.runtimeChoice ∧
      ∀ alloc, Feasible cap maxLegs alloc →
        keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  have hComplete :
      ∀ alloc : Alloc n Q,
        (fun alloc : Alloc n Q => Feasible cap maxLegs alloc) alloc ↔
          Feasible cap maxLegs alloc := by
    intro alloc
    rfl
  have hPresented :
      PresentedBy (fun alloc => Feasible cap maxLegs alloc) candidateOf guardInputs :=
    presentedBy_of_quoteTotal_and_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := guardInputs)
      hQuoteTotal
      hQuotedPresented
      hCompat
  exact packetOk_implies_presented_feasible_minimality
    (emit := fun alloc => Feasible cap maxLegs alloc)
    (candidateOf := candidateOf)
    (domainInputs := domainInputs)
    (guardInputs := guardInputs)
    hPacket
    hComplete
    hPresented

/-- The same bridge also replays the emitted quote surface, not just minimality.
-/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hQuotedPresented : QuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted guardInputs)
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
  have hComplete :
      ∀ alloc : Alloc n Q,
        (fun alloc : Alloc n Q => Feasible cap maxLegs alloc) alloc ↔
          Feasible cap maxLegs alloc := by
    intro alloc
    rfl
  have hPresented :
      PresentedBy (fun alloc => Feasible cap maxLegs alloc) candidateOf guardInputs :=
    presentedBy_of_quoteTotal_and_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := guardInputs)
      hQuoteTotal
      hQuotedPresented
      hCompat
  exact packetOk_implies_presented_feasible_quote_and_minimality
    (emit := fun alloc => Feasible cap maxLegs alloc)
    (candidateOf := candidateOf)
    (domainInputs := domainInputs)
    (guardInputs := guardInputs)
    hPacket
    hComplete
    hPresented

end ExactOutManyPoolQuotedPresentationBridge
end Routing
end TauSwap
