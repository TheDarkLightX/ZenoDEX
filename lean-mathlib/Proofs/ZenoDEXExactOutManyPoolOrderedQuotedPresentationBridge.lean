import Proofs.ZenoDEXExactOutManyPoolQuotedPathRealization
import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCertifiedBridge

/-!
# ZenoDEX Exact-Out Many-Pool Ordered Quoted Presentation Bridge

This file weakens the quoted-path presentation assumption to the exact shape
needed by the selected audited-domain completeness bridge.

The earlier `QuotedPresentedBy` surface quantified over every quoted
structurally reachable path, even though the only quoted paths ever needed for
feasible audited allocations are the sorted, leg-bounded ones arising from
`supportLegs`.

This file therefore proves:

- quote totality plus presentation of only sorted, leg-bounded quoted paths is
  enough to discharge the selected-domain certified bridge,
- and that obligation can itself be stated as a raw quoted-path list cover,
  closer to the concrete Python emitter than the earlier witness bundles.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolOrderedQuotedPresentationBridge

open ExactOutRouteCertificate
open ExactOutManyPoolSelectedDomainCertifiedBridge
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolSupportPresentation
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedStructuralReachability
open TauSwap.ZenoDEX.ExactOutManyPoolQuotedPathRealization

abbrev Candidate := ExactOutRouteCertificate.Candidate
abbrev DomainInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.DomainInputs
abbrev GuardInputs := ExactOutManyPoolSelectedDomainCertifiedBridge.GuardInputs

/-- Quoted recursive paths present the guarded candidate stream only on the
ordered, leg-bounded slice that can arise from feasible audited allocations. -/
def OrderedQuotedPresentedBy
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs) : Prop :=
  (∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        candidateOfQuoted quotedLegs ∈ inputs.first :: inputs.rest) ∧
    (∀ cand ∈ inputs.first :: inputs.rest,
      ∃ quotedLegs : List (QuotedLeg n),
        ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT ∧
          quotedLegs.length ≤ maxLegs ∧
          QuotedStructurallyReachable quoteIn cap Q quotedLegs ∧
          candidateOfQuoted quotedLegs = cand)

/-- Quote totality plus ordered quoted-path presentation is enough to show that
every feasible bounded audited allocation maps into the guarded candidate
stream. -/
theorem feasible_candidate_mem_of_quoteTotal_and_ordered_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hOrderedPresented :
      OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs)
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
  rcases feasible_has_sorted_support_presentation (hFeas := hFeas) with
    ⟨hSorted, _hNodup, hLen, _hSum, _hPos, _hCap⟩
  have hQuotedSorted : ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT := by
    simpa [hSupport] using hSorted
  have hQuotedLen : quotedLegs.length ≤ maxLegs := by
    have hLenEq : quotedLegs.length = (supportLegs alloc).length := by
      simpa [supportOfQuotedLegs] using congrArg List.length hSupport
    rw [hLenEq]
    exact hLen
  have hMemQuoted : candidateOfQuoted quotedLegs ∈ inputs.first :: inputs.rest :=
    hOrderedPresented.1 quotedLegs hQuotedSorted hQuotedLen hQuoted
  have hEq : candidateOf alloc = candidateOfQuoted quotedLegs :=
    hCompat hFeas hSupport hQuoted
  simpa [hEq] using hMemQuoted

/-- The certified bridge's abstract `PresentedBy` hypothesis follows from quote
totality plus ordered quoted-path presentation. -/
theorem presentedBy_of_quoteTotal_and_ordered_quoted_presentation
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (inputs : GuardInputs)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hOrderedPresented :
      OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs)
    (hCompat :
      ∀ {alloc : Alloc n Q} {quotedLegs : List (QuotedLeg n)},
        Feasible cap maxLegs alloc →
          supportOfQuotedLegs quotedLegs = supportLegs alloc →
          QuotedStructurallyReachable quoteIn cap Q quotedLegs →
          candidateOf alloc = candidateOfQuoted quotedLegs) :
    PresentedBy (fun alloc => Feasible cap maxLegs alloc) candidateOf inputs := by
  constructor
  · intro alloc hFeas
    exact feasible_candidate_mem_of_quoteTotal_and_ordered_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := inputs)
      hQuoteTotal
      hOrderedPresented
      hCompat
      alloc
      hFeas
  · intro cand hMem
    rcases hOrderedPresented.2 cand hMem with
      ⟨quotedLegs, hSorted, hLen, hQuoted, hCandQuoted⟩
    rcases exists_alloc_of_sorted_quoted_presentation
        (cap := cap)
        (maxLegs := maxLegs)
        (quotedLegs := quotedLegs)
        hQuoted
        hSorted
        hLen with
      ⟨alloc, hFeas, hSupport⟩
    have hEq : candidateOf alloc = candidateOfQuoted quotedLegs :=
      hCompat hFeas hSupport hQuoted
    exact ⟨alloc, hFeas, hEq.trans hCandQuoted⟩

/-- Packet success upgrades to bounded audited-domain minimality once the
guarded stream is presented by ordered quoted recursive paths. -/
theorem packetOk_implies_feasible_minimality_of_quoteTotal_and_ordered_quoted_presentation
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
    (hOrderedPresented :
      OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted guardInputs)
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
    presentedBy_of_quoteTotal_and_ordered_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := guardInputs)
      hQuoteTotal
      hOrderedPresented
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
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_quoted_presentation
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
    (hOrderedPresented :
      OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted guardInputs)
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
    presentedBy_of_quoteTotal_and_ordered_quoted_presentation
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (inputs := guardInputs)
      hQuoteTotal
      hOrderedPresented
      hCompat
  exact packetOk_implies_presented_feasible_quote_and_minimality
    (emit := fun alloc => Feasible cap maxLegs alloc)
    (candidateOf := candidateOf)
    (domainInputs := domainInputs)
    (guardInputs := guardInputs)
    hPacket
    hComplete
    hPresented

/-- Raw quoted-path list cover for the guarded candidate stream. This is closer
to the concrete Python emitter than witness-bundle presentations. -/
def OrderedQuotedPathListCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : GuardInputs) : Prop :=
  inputs.first :: inputs.rest = quotedPaths.map candidateOfQuoted ∧
    (∀ quotedLegs ∈ quotedPaths,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT ∧
        quotedLegs.length ≤ maxLegs ∧
        QuotedStructurallyReachable quoteIn cap Q quotedLegs) ∧
    (∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        quotedLegs ∈ quotedPaths)

/-- Weaker raw quoted-path cover that keeps only candidate-stream membership
equivalence, not literal list equality. This is the exact surface used by the
presentation theorems below. -/
def OrderedQuotedPathSetCovers
    {n Q : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : GuardInputs) : Prop :=
  (∀ cand, cand ∈ inputs.first :: inputs.rest ↔ cand ∈ quotedPaths.map candidateOfQuoted) ∧
    (∀ quotedLegs ∈ quotedPaths,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT ∧
        quotedLegs.length ≤ maxLegs ∧
        QuotedStructurallyReachable quoteIn cap Q quotedLegs) ∧
    (∀ quotedLegs,
      ((supportOfQuotedLegs quotedLegs).map Prod.fst).SortedLT →
      quotedLegs.length ≤ maxLegs →
      QuotedStructurallyReachable quoteIn cap Q quotedLegs →
        quotedLegs ∈ quotedPaths)

theorem orderedQuotedPathSetCovers_of_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : GuardInputs)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    OrderedQuotedPathSetCovers
      (Q := Q)
      quoteIn
      cap
      maxLegs
      candidateOfQuoted
      quotedPaths
      inputs := by
  rcases hCover with ⟨hStream, hWell, hAllOrdered⟩
  exact ⟨by
      intro cand
      rw [hStream], hWell, hAllOrdered⟩

/-- An exact raw path-list cover is enough to discharge ordered quoted-path
presentation. -/
theorem orderedQuotedPresentedBy_of_ordered_path_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : GuardInputs)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  rcases hCover with ⟨hStream, hWell, hAllOrdered⟩
  constructor
  · intro quotedLegs hSorted hLen hQuoted
    have hMem : quotedLegs ∈ quotedPaths := hAllOrdered quotedLegs hSorted hLen hQuoted
    have hMemMap : candidateOfQuoted quotedLegs ∈ quotedPaths.map candidateOfQuoted := by
      exact List.mem_map.mpr ⟨quotedLegs, hMem, rfl⟩
    rw [hStream]
    simpa using hMemMap
  · intro cand hCand
    have hCandMap : cand ∈ quotedPaths.map candidateOfQuoted := by
      rw [← hStream]
      exact hCand
    rcases List.mem_map.mp hCandMap with ⟨quotedLegs, hMem, hCandEq⟩
    rcases hWell quotedLegs hMem with ⟨hSorted, hLen, hQuoted⟩
    exact ⟨quotedLegs, hSorted, hLen, hQuoted, hCandEq⟩

/-- Candidate-stream membership equivalence plus ordered quoted-path coverage is
already enough to discharge ordered quoted-path presentation. -/
theorem orderedQuotedPresentedBy_of_ordered_path_set_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (inputs : GuardInputs)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
        inputs) :
    OrderedQuotedPresentedBy (Q := Q) quoteIn cap maxLegs candidateOfQuoted inputs := by
  rcases hCover with ⟨hStream, hWell, hAllOrdered⟩
  constructor
  · intro quotedLegs hSorted hLen hQuoted
    have hMem : quotedLegs ∈ quotedPaths := hAllOrdered quotedLegs hSorted hLen hQuoted
    have hMemMap : candidateOfQuoted quotedLegs ∈ quotedPaths.map candidateOfQuoted := by
      exact List.mem_map.mpr ⟨quotedLegs, hMem, rfl⟩
    exact (hStream _).2 hMemMap
  · intro cand hCand
    have hCandMap : cand ∈ quotedPaths.map candidateOfQuoted := (hStream _).1 hCand
    rcases List.mem_map.mp hCandMap with ⟨quotedLegs, hMem, hCandEq⟩
    rcases hWell quotedLegs hMem with ⟨hSorted, hLen, hQuoted⟩
    exact ⟨quotedLegs, hSorted, hLen, hQuoted, hCandEq⟩

/-- Quote totality plus an exact raw path-list cover upgrades certified packet
success to bounded audited-domain quote replay and minimality. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_list_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathListCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
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
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_quoted_presentation
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (orderedQuotedPresentedBy_of_ordered_path_list_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := guardInputs)
        hCover)
      hCompat

/-- The packet bridge only needs candidate-stream membership equivalence, not
literal list equality, together with the same ordered quoted-path coverage. -/
theorem packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_path_set_cover
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    (candidateOf : Alloc n Q → Candidate)
    (candidateOfQuoted : List (QuotedLeg n) → Candidate)
    (quotedPaths : List (List (QuotedLeg n)))
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (ExactOutManyPoolCertifiedWinnerPacket.buildPacket
        (ExactOutManyPoolCertifiedWinnerPacket.ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hCover :
      OrderedQuotedPathSetCovers
        (Q := Q)
        quoteIn
        cap
        maxLegs
        candidateOfQuoted
        quotedPaths
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
    packetOk_implies_feasible_quote_and_minimality_of_quoteTotal_and_ordered_quoted_presentation
      (quoteIn := quoteIn)
      (cap := cap)
      (candidateOf := candidateOf)
      (candidateOfQuoted := candidateOfQuoted)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket
      hQuoteTotal
      (orderedQuotedPresentedBy_of_ordered_path_set_cover
        (candidateOfQuoted := candidateOfQuoted)
        (quotedPaths := quotedPaths)
        (inputs := guardInputs)
        hCover)
      hCompat

end ExactOutManyPoolOrderedQuotedPresentationBridge
end Routing
end TauSwap
