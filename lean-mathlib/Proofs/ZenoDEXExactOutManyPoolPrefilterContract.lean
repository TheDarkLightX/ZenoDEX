/-!
# ZenoDEX Exact-Out Many-Pool Prefilter Contract

This file formalizes the deterministic shell around the bounded many-pool
exact-out prefilter contract used by the integration/API boundary.

It proves:

- the contract is a deterministic rebuild from the declared prefilter boolean
  facts,
- verifier success is equivalent to equality with the canonical rebuilt
  contract,
- `contractOk = true` iff all declared prefilter facts hold,
- the verifying contract is unique for fixed inputs.

This proof does **not** claim candidate-pool prefilter completeness. It only
proves the shell around the replayable packet that exposes the prefilter
boundary.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolPrefilterContract

structure Inputs where
  feasibleRowsSortedUnique : Bool
  selectedPoolIdsSortedUnique : Bool
  selectedPoolIdsWithinBudget : Bool
  selectedPoolIdsSubsetOfFeasible : Bool
  selectedIsPrefixOfFeasibleRanking : Bool
  fullCapacityGuardFeasible : Bool
  selectedCapacityGuardFeasible : Bool
deriving DecidableEq, Repr

structure Contract where
  feasibleRowsSortedUnique : Bool
  selectedPoolIdsSortedUnique : Bool
  selectedPoolIdsWithinBudget : Bool
  selectedPoolIdsSubsetOfFeasible : Bool
  selectedIsPrefixOfFeasibleRanking : Bool
  fullCapacityGuardFeasible : Bool
  selectedCapacityGuardFeasible : Bool
  contractOk : Bool
deriving DecidableEq, Repr

def buildContract (inputs : Inputs) : Contract :=
  {
    feasibleRowsSortedUnique := inputs.feasibleRowsSortedUnique
    selectedPoolIdsSortedUnique := inputs.selectedPoolIdsSortedUnique
    selectedPoolIdsWithinBudget := inputs.selectedPoolIdsWithinBudget
    selectedPoolIdsSubsetOfFeasible := inputs.selectedPoolIdsSubsetOfFeasible
    selectedIsPrefixOfFeasibleRanking := inputs.selectedIsPrefixOfFeasibleRanking
    fullCapacityGuardFeasible := inputs.fullCapacityGuardFeasible
    selectedCapacityGuardFeasible := inputs.selectedCapacityGuardFeasible
    contractOk :=
      inputs.feasibleRowsSortedUnique &&
      inputs.selectedPoolIdsSortedUnique &&
      inputs.selectedPoolIdsWithinBudget &&
      inputs.selectedPoolIdsSubsetOfFeasible &&
      inputs.selectedIsPrefixOfFeasibleRanking &&
      inputs.fullCapacityGuardFeasible &&
      inputs.selectedCapacityGuardFeasible
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
      inputs.feasibleRowsSortedUnique = true ∧
      inputs.selectedPoolIdsSortedUnique = true ∧
      inputs.selectedPoolIdsWithinBudget = true ∧
      inputs.selectedPoolIdsSubsetOfFeasible = true ∧
      inputs.selectedIsPrefixOfFeasibleRanking = true ∧
      inputs.fullCapacityGuardFeasible = true ∧
      inputs.selectedCapacityGuardFeasible = true := by
  simp [buildContract, Bool.and_eq_true, and_assoc]

end ExactOutManyPoolPrefilterContract
end Routing
end TauSwap
