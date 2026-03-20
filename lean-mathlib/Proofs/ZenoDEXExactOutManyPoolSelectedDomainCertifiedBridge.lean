import Proofs.ZenoDEXExactOutManyPoolCertifiedWinnerPacket
import Proofs.ZenoDEXExactOutManyPoolSelectedDomainCompleteness

/-!
# ZenoDEX Exact-Out Many-Pool Selected-Domain Certified Bridge

This file packages the next honest generator/completeness bridge for the
many-pool exact-out proof stack.

The existing certified packet proofs already show:

- the audited bounded candidate-domain booleans hold,
- the guarded packet returns the runtime quote iff the runtime choice is minimal
  over the emitted candidate stream.

What the current audited shell still does **not** prove is that the emitted
candidate stream is complete for the full bounded audited search space. This file
therefore makes that missing fact explicit as a presentation hypothesis:

- every feasible audited allocation is emitted into the guarded candidate stream,
- every guarded candidate comes from some emitted audited allocation.

Under that extra hypothesis, successful certified-packet verification upgrades
emitted-stream minimality into minimality over the full bounded audited feasible
domain.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolSelectedDomainCertifiedBridge

open ExactOutManyPoolCertifiedWinnerPacket
open ExactOutRouteCertificate
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness

abbrev DomainInputs := ExactOutManyPoolCertifiedWinnerPacket.DomainInputs
abbrev GuardInputs := ExactOutManyPoolCertifiedWinnerPacket.GuardInputs
abbrev Candidate := ExactOutRouteCertificate.Candidate

/-- The guarded candidate stream is a faithful presentation of the emitted
bounded audited domain under `candidateOf`. -/
def PresentedBy {n Q : ℕ}
    (emit : Alloc n Q → Prop)
    (candidateOf : Alloc n Q → Candidate)
    (inputs : GuardInputs) : Prop :=
  (∀ alloc, emit alloc → candidateOf alloc ∈ inputs.first :: inputs.rest) ∧
    (∀ cand ∈ inputs.first :: inputs.rest, ∃ alloc, emit alloc ∧ candidateOf alloc = cand)

/-- If the certified packet succeeds and the guarded candidate stream faithfully
presents a pointwise-complete bounded audited generator, then the runtime choice
corresponds to a feasible audited allocation and is minimal over every feasible
audited allocation under the candidate order used by the route certificate. -/
theorem packetOk_implies_presented_feasible_minimality
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop}
    (candidateOf : Alloc n Q → Candidate)
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (buildPacket (ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc)
    (hPresented : PresentedBy emit candidateOf guardInputs) :
    ∃ allocStar, Feasible cap maxLegs allocStar ∧
      candidateOf allocStar = guardInputs.runtimeChoice ∧
      ∀ alloc, Feasible cap maxLegs alloc →
        keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  rcases (packetOk_iff_audited_emitted_minimality domainInputs guardInputs).1 hPacket with
    ⟨_hSorted, _hBudget, _hNonempty, _hCompleteFlag, _hLegBounded, _hLegSorted, _hWithin, _hCount,
      hMem, hMin⟩
  rcases hPresented.2 guardInputs.runtimeChoice hMem with ⟨allocStar, hEmitStar, hCandStar⟩
  exact ⟨allocStar, (hComplete allocStar).1 hEmitStar, hCandStar,
    by
      intro alloc hFeas
      have hEmit : emit alloc := (hComplete alloc).2 hFeas
      have hCandMem : candidateOf alloc ∈ guardInputs.first :: guardInputs.rest :=
        hPresented.1 alloc hEmit
      exact hMin (candidateOf alloc) hCandMem⟩

/-- The same bridge can be replayed directly at the emitted quote surface:
certified success yields a concrete quote plus a feasible audited witness whose
candidate is minimal over the full bounded audited domain, provided generator
presentation/completeness holds. -/
theorem packetOk_implies_presented_feasible_quote_and_minimality
    {n Q : ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {emit : Alloc n Q → Prop}
    (candidateOf : Alloc n Q → Candidate)
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs)
    (hPacket :
      (buildPacket (ofDomainAndGuard domainInputs guardInputs)).packetOk = true)
    (hComplete : ∀ alloc, emit alloc ↔ Feasible cap maxLegs alloc)
    (hPresented : PresentedBy emit candidateOf guardInputs) :
    ∃ allocStar, Feasible cap maxLegs allocStar ∧
      candidateOf allocStar = guardInputs.runtimeChoice ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice ∧
      ∀ alloc, Feasible cap maxLegs alloc →
        keyLe guardInputs.runtimeChoice (candidateOf alloc) := by
  rcases packetOk_implies_presented_feasible_minimality
      (candidateOf := candidateOf)
      (domainInputs := domainInputs)
      (guardInputs := guardInputs)
      hPacket hComplete hPresented with
    ⟨allocStar, hFeas, hCandStar, hMinAll⟩
  rcases (packetOk_iff_audited_domain_and_quote domainInputs guardInputs).1 hPacket with
    ⟨_hSorted, _hBudget, _hNonempty, _hCompleteFlag, _hLegBounded, _hLegSorted, _hWithin, _hCount,
      hQuote⟩
  exact ⟨allocStar, hFeas, hCandStar, hQuote, hMinAll⟩

end ExactOutManyPoolSelectedDomainCertifiedBridge
end Routing
end TauSwap
