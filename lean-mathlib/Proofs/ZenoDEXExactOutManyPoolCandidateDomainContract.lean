/-!
# ZenoDEX Exact-Out Many-Pool Candidate-Domain Contract

This file formalizes the deterministic shell around the bounded many-pool
exact-out candidate-domain contract used by the integration/API boundary.

It proves:

- the contract is a deterministic rebuild from the bounded candidate-domain
  boolean facts,
- verifier success is equivalent to equality with the canonical rebuilt
  contract,
- `contractOk = true` iff all declared candidate-domain facts hold,
- the verifying contract is unique for fixed inputs.

This proof does **not** claim global generator completeness. It only proves the
shell around the replayable packet that exposes the emitted bounded domain.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolCandidateDomainContract

structure Inputs where
  auditPoolIdsSortedUnique : Bool
  auditPoolIdsWithinBudget : Bool
  candidateDomainNonempty : Bool
  allCandidatesComplete : Bool
  allCandidatesLegBounded : Bool
  allCandidatesLegPoolIdsSortedUnique : Bool
  allCandidatesWithinAuditPoolIds : Bool
  candidateCountWithinBudget : Bool
deriving DecidableEq, Repr

structure Contract where
  auditPoolIdsSortedUnique : Bool
  auditPoolIdsWithinBudget : Bool
  candidateDomainNonempty : Bool
  allCandidatesComplete : Bool
  allCandidatesLegBounded : Bool
  allCandidatesLegPoolIdsSortedUnique : Bool
  allCandidatesWithinAuditPoolIds : Bool
  candidateCountWithinBudget : Bool
  contractOk : Bool
deriving DecidableEq, Repr

def buildContract (inputs : Inputs) : Contract :=
  {
    auditPoolIdsSortedUnique := inputs.auditPoolIdsSortedUnique
    auditPoolIdsWithinBudget := inputs.auditPoolIdsWithinBudget
    candidateDomainNonempty := inputs.candidateDomainNonempty
    allCandidatesComplete := inputs.allCandidatesComplete
    allCandidatesLegBounded := inputs.allCandidatesLegBounded
    allCandidatesLegPoolIdsSortedUnique := inputs.allCandidatesLegPoolIdsSortedUnique
    allCandidatesWithinAuditPoolIds := inputs.allCandidatesWithinAuditPoolIds
    candidateCountWithinBudget := inputs.candidateCountWithinBudget
    contractOk :=
      inputs.auditPoolIdsSortedUnique &&
      inputs.auditPoolIdsWithinBudget &&
      inputs.candidateDomainNonempty &&
      inputs.allCandidatesComplete &&
      inputs.allCandidatesLegBounded &&
      inputs.allCandidatesLegPoolIdsSortedUnique &&
      inputs.allCandidatesWithinAuditPoolIds &&
      inputs.candidateCountWithinBudget
  }

def verifyContract (inputs : Inputs) (contract : Contract) : Prop :=
  contract = buildContract inputs

theorem verifyContract_iff
    (inputs : Inputs)
    (contract : Contract) :
    verifyContract inputs contract ↔
      contract = buildContract inputs := by
  rfl

theorem verifyContract_of_build
    (inputs : Inputs) :
    verifyContract inputs (buildContract inputs) := by
  rfl

theorem verifyingContract_unique
    (inputs : Inputs)
    {contract : Contract}
    (hVerify : verifyContract inputs contract) :
    contract = buildContract inputs := by
  exact hVerify

theorem contractOk_iff
    (inputs : Inputs) :
    (buildContract inputs).contractOk = true ↔
      inputs.auditPoolIdsSortedUnique = true ∧
      inputs.auditPoolIdsWithinBudget = true ∧
      inputs.candidateDomainNonempty = true ∧
      inputs.allCandidatesComplete = true ∧
      inputs.allCandidatesLegBounded = true ∧
      inputs.allCandidatesLegPoolIdsSortedUnique = true ∧
      inputs.allCandidatesWithinAuditPoolIds = true ∧
      inputs.candidateCountWithinBudget = true := by
  simp [buildContract, Bool.and_eq_true, and_assoc]

end ExactOutManyPoolCandidateDomainContract
end Routing
end TauSwap
