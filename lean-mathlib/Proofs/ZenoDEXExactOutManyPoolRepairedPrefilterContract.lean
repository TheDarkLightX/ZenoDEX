/-!
# ZenoDEX Exact-Out Many-Pool Repaired Prefilter Contract

This file formalizes the deterministic shell around the repaired many-pool
exact-out prefilter contract exposed at the integration/API boundary.

It proves:

- the contract is a deterministic rebuild from the declared repaired-prefilter
  boolean facts,
- verifier success is equivalent to equality with the canonical rebuilt
  contract,
- `contractOk = true` iff the repaired selected pool ids are sorted/within
  budget/subset aligned and the repaired selected domain both matches the full
  bounded canonical winner and satisfies the contraction audit,
- the verifying contract is unique for fixed inputs.

This proof does **not** claim runtime adoption or global generator completeness.
It only proves the replayable shell around the repaired-prefilter candidate
boundary.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedPrefilterContract

structure Inputs where
  currentSelectedMatchesFullCanonical : Bool
  repairedSelectedPoolIdsSortedUnique : Bool
  repairedSelectedPoolIdsWithinBudget : Bool
  repairedSelectedPoolIdsSubsetOfFeasible : Bool
  repairedSelectedDomainMatchesFullCanonical : Bool
  repairedContractionHolds : Bool
deriving DecidableEq, Repr

structure Contract where
  currentSelectedMatchesFullCanonical : Bool
  repairedSelectedPoolIdsSortedUnique : Bool
  repairedSelectedPoolIdsWithinBudget : Bool
  repairedSelectedPoolIdsSubsetOfFeasible : Bool
  repairedSelectedDomainMatchesFullCanonical : Bool
  repairedContractionHolds : Bool
  contractOk : Bool
deriving DecidableEq, Repr

def buildContract (inputs : Inputs) : Contract :=
  {
    currentSelectedMatchesFullCanonical := inputs.currentSelectedMatchesFullCanonical
    repairedSelectedPoolIdsSortedUnique := inputs.repairedSelectedPoolIdsSortedUnique
    repairedSelectedPoolIdsWithinBudget := inputs.repairedSelectedPoolIdsWithinBudget
    repairedSelectedPoolIdsSubsetOfFeasible := inputs.repairedSelectedPoolIdsSubsetOfFeasible
    repairedSelectedDomainMatchesFullCanonical := inputs.repairedSelectedDomainMatchesFullCanonical
    repairedContractionHolds := inputs.repairedContractionHolds
    contractOk :=
      inputs.repairedSelectedPoolIdsSortedUnique &&
      inputs.repairedSelectedPoolIdsWithinBudget &&
      inputs.repairedSelectedPoolIdsSubsetOfFeasible &&
      inputs.repairedSelectedDomainMatchesFullCanonical &&
      inputs.repairedContractionHolds
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
      inputs.repairedSelectedPoolIdsSortedUnique = true ∧
      inputs.repairedSelectedPoolIdsWithinBudget = true ∧
      inputs.repairedSelectedPoolIdsSubsetOfFeasible = true ∧
      inputs.repairedSelectedDomainMatchesFullCanonical = true ∧
      inputs.repairedContractionHolds = true := by
  simp [buildContract, Bool.and_eq_true, and_assoc]

end ExactOutManyPoolRepairedPrefilterContract
end Routing
end TauSwap
