import Proofs.ZenoDEXExactOutManyPoolCandidateDomainContract
import Proofs.ZenoDEXExactOutManyPoolGuardedQuotePacket

/-!
# ZenoDEX Exact-Out Many-Pool Certified Winner Packet

Deterministic shell for the unified replayable packet that bundles the bounded
candidate-domain contract and the guarded many-pool winner packet.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolCertifiedWinnerPacket

abbrev DomainInputs := ExactOutManyPoolCandidateDomainContract.Inputs
abbrev GuardInputs := ExactOutManyPoolGuardedQuotePacket.Inputs

structure Inputs where
  domainContractOk : Bool
  guardOk : Bool
  deriving DecidableEq, Repr

structure Packet where
  domainContractOk : Bool
  guardOk : Bool
  packetOk : Bool
  deriving DecidableEq, Repr

def buildPacket (inputs : Inputs) : Packet :=
  {
    domainContractOk := inputs.domainContractOk
    guardOk := inputs.guardOk
    packetOk := inputs.domainContractOk && inputs.guardOk
  }

def verifyPacket (inputs : Inputs) (packet : Packet) : Prop :=
  packet = buildPacket inputs

def ofDomainAndGuard (domainInputs : DomainInputs) (guardInputs : GuardInputs) : Inputs :=
  {
    domainContractOk :=
      (ExactOutManyPoolCandidateDomainContract.buildContract domainInputs).contractOk
    guardOk := (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).guardOk
  }

def AuditedEmittedMinimality
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs) : Prop :=
  domainInputs.auditPoolIdsSortedUnique = true ∧
    domainInputs.auditPoolIdsWithinBudget = true ∧
    domainInputs.candidateDomainNonempty = true ∧
    domainInputs.allCandidatesComplete = true ∧
    domainInputs.allCandidatesLegBounded = true ∧
    domainInputs.allCandidatesLegPoolIdsSortedUnique = true ∧
    domainInputs.allCandidatesWithinAuditPoolIds = true ∧
    domainInputs.candidateCountWithinBudget = true ∧
    guardInputs.runtimeChoice ∈ guardInputs.first :: guardInputs.rest ∧
    ∀ x ∈ guardInputs.first :: guardInputs.rest,
      ExactOutRouteCertificate.keyLe guardInputs.runtimeChoice x

theorem verifyPacket_iff (inputs : Inputs) (packet : Packet) :
    verifyPacket inputs packet ↔ packet = buildPacket inputs := by
  rfl

theorem verifyPacket_of_build (inputs : Inputs) :
    verifyPacket inputs (buildPacket inputs) := by
  rfl

theorem verifyingPacket_unique (inputs : Inputs) {packet : Packet}
    (hVerify : verifyPacket inputs packet) :
    packet = buildPacket inputs := by
  exact hVerify

theorem packetOk_iff (inputs : Inputs) :
    (buildPacket inputs).packetOk = true ↔
      inputs.domainContractOk = true ∧ inputs.guardOk = true := by
  simp [buildPacket, Bool.and_eq_true]

theorem packetOk_iff_audited_emitted_minimality
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs) :
    (buildPacket (ofDomainAndGuard domainInputs guardInputs)).packetOk = true ↔
      AuditedEmittedMinimality domainInputs guardInputs := by
  constructor
  · intro hPacket
    have hPair :
        (ExactOutManyPoolCandidateDomainContract.buildContract domainInputs).contractOk = true ∧
          (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).guardOk = true :=
      (packetOk_iff (ofDomainAndGuard domainInputs guardInputs)).1 hPacket
    rcases hPair with ⟨hDomain, hGuard⟩
    rcases (ExactOutManyPoolCandidateDomainContract.contractOk_iff domainInputs).1 hDomain with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount⟩
    have hMin :
        guardInputs.runtimeChoice ∈ guardInputs.first :: guardInputs.rest ∧
          ∀ x ∈ guardInputs.first :: guardInputs.rest,
            ExactOutRouteCertificate.keyLe guardInputs.runtimeChoice x :=
      (ExactOutManyPoolGuardedQuotePacket.guardOk_iff_mem_and_keyLe_all guardInputs).1 hGuard
    exact
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMin.1, hMin.2⟩
  · intro hAuditMin
    rcases hAuditMin with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMem, hMin⟩
    have hDomain :
        (ExactOutManyPoolCandidateDomainContract.buildContract domainInputs).contractOk = true :=
      (ExactOutManyPoolCandidateDomainContract.contractOk_iff domainInputs).2
        ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount⟩
    have hGuard :
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).guardOk = true :=
      (ExactOutManyPoolGuardedQuotePacket.guardOk_iff_mem_and_keyLe_all guardInputs).2
        ⟨hMem, hMin⟩
    exact (packetOk_iff (ofDomainAndGuard domainInputs guardInputs)).2 ⟨hDomain, hGuard⟩

theorem packetOk_iff_audited_domain_and_quote
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs) :
    (buildPacket (ofDomainAndGuard domainInputs guardInputs)).packetOk = true ↔
      domainInputs.auditPoolIdsSortedUnique = true ∧
      domainInputs.auditPoolIdsWithinBudget = true ∧
      domainInputs.candidateDomainNonempty = true ∧
      domainInputs.allCandidatesComplete = true ∧
      domainInputs.allCandidatesLegBounded = true ∧
      domainInputs.allCandidatesLegPoolIdsSortedUnique = true ∧
      domainInputs.allCandidatesWithinAuditPoolIds = true ∧
      domainInputs.candidateCountWithinBudget = true ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some guardInputs.runtimeChoice := by
  constructor
  · intro hPacket
    rcases (packetOk_iff_audited_emitted_minimality domainInputs guardInputs).1 hPacket with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMem, hMin⟩
    have hQuote :
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some guardInputs.runtimeChoice :=
      (TauSwap.Routing.ExactOutManyPoolGuardedQuotePacket.quote_eq_some_runtimeChoice_iff_mem_and_keyLe_all
        guardInputs).2 ⟨hMem, hMin⟩
    exact
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hQuote⟩
  · intro hPacket
    rcases hPacket with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hQuote⟩
    have hMin :
        guardInputs.runtimeChoice ∈ guardInputs.first :: guardInputs.rest ∧
          ∀ x ∈ guardInputs.first :: guardInputs.rest,
            ExactOutRouteCertificate.keyLe guardInputs.runtimeChoice x :=
      (TauSwap.Routing.ExactOutManyPoolGuardedQuotePacket.quote_eq_some_runtimeChoice_iff_mem_and_keyLe_all
        guardInputs).1 hQuote
    exact (packetOk_iff_audited_emitted_minimality domainInputs guardInputs).2
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMin.1, hMin.2⟩

theorem packetOk_iff_audited_domain_and_quote_eq_canonicalWinner
    (domainInputs : DomainInputs)
    (guardInputs : GuardInputs) :
    (buildPacket (ofDomainAndGuard domainInputs guardInputs)).packetOk = true ↔
      domainInputs.auditPoolIdsSortedUnique = true ∧
      domainInputs.auditPoolIdsWithinBudget = true ∧
      domainInputs.candidateDomainNonempty = true ∧
      domainInputs.allCandidatesComplete = true ∧
      domainInputs.allCandidatesLegBounded = true ∧
      domainInputs.allCandidatesLegPoolIdsSortedUnique = true ∧
      domainInputs.allCandidatesWithinAuditPoolIds = true ∧
      domainInputs.candidateCountWithinBudget = true ∧
      (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
        some (ExactOutManyPoolOracleContract.canonicalWinner guardInputs) := by
  constructor
  · intro hPacket
    rcases (packetOk_iff_audited_emitted_minimality domainInputs guardInputs).1 hPacket with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMem, hMin⟩
    have hQuote :
        (ExactOutManyPoolGuardedQuotePacket.buildPacket guardInputs).quote =
          some (ExactOutManyPoolOracleContract.canonicalWinner guardInputs) :=
      (TauSwap.Routing.ExactOutManyPoolGuardedQuotePacket.quote_eq_some_canonicalWinner_iff_mem_and_keyLe_all
        guardInputs).2 ⟨hMem, hMin⟩
    exact
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hQuote⟩
  · intro hPacket
    rcases hPacket with
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hQuote⟩
    have hMin :
        guardInputs.runtimeChoice ∈ guardInputs.first :: guardInputs.rest ∧
          ∀ x ∈ guardInputs.first :: guardInputs.rest,
            ExactOutRouteCertificate.keyLe guardInputs.runtimeChoice x :=
      (TauSwap.Routing.ExactOutManyPoolGuardedQuotePacket.quote_eq_some_canonicalWinner_iff_mem_and_keyLe_all
        guardInputs).1 hQuote
    exact (packetOk_iff_audited_emitted_minimality domainInputs guardInputs).2
      ⟨hSorted, hBudget, hNonempty, hComplete, hLegBounded, hLegSorted, hWithin, hCount,
        hMin.1, hMin.2⟩

end ExactOutManyPoolCertifiedWinnerPacket
end Routing
end TauSwap
