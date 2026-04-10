import Proofs.ZenoDEXExactOutManyPoolRepairedPrefilterContract
import Proofs.ZenoDEXExactOutManyPoolPrefilterContractionBridge

open scoped Classical

/-!
# ZenoDEX Exact-Out Many-Pool Repaired Prefilter Semantic Bridge

This file packages the strongest honest bridge currently derivable from the
repaired many-pool exact-out prefilter contract.

What it proves:

- if the repaired prefilter contract verifies and `contractOk = true`,
- and the repaired boolean facts are interpreted as the semantic hypotheses
  required by the existing contraction bridge,

then bounded-domain canonical minimality follows.

What it does **not** prove:

- that the repaired booleans already carry those semantics,
- or that the repaired prefilter closes the world-model blocker by itself.

That remaining interpretation layer is still the real blocker.
-/

namespace TauSwap
namespace Routing
namespace ExactOutManyPoolRepairedPrefilterSemanticBridge

open ExactOutManyPoolRepairedPrefilterContract
open TauSwap.ZenoDEX.ExactOutCanonicalMinimizer
open TauSwap.ZenoDEX.ExactOutManyPoolSelectedDomainCompleteness
open TauSwap.ZenoDEX.ExactOutManyPoolPrefilterContractionBridge

noncomputable section

abbrev ContractInputs := ExactOutManyPoolRepairedPrefilterContract.Inputs
abbrev Contract := ExactOutManyPoolRepairedPrefilterContract.Contract

/-- Semantic selected-domain witness expected by the repaired prefilter bridge.
It packages the exact data needed to feed the existing contraction theorem. -/
structure SelectedDomainMinimumWitness
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    (cap : Fin n → ℕ)
    (maxLegs : ℕ)
    (selected : Finset (Fin n))
    (routeKey : Alloc n Q → Key PoolId) where
  allocStar : Alloc n Q
  selectedFeasible : SelectedFeasible cap maxLegs selected allocStar
  minimalSelected :
    ∀ alloc, SelectedFeasible cap maxLegs selected alloc →
      routeKey allocStar ≤ routeKey alloc

theorem contractOk_implies_repairedSelectedDomainMatchesFullCanonical
    (inputs : ContractInputs)
    (hOk : (buildContract inputs).contractOk = true) :
    inputs.repairedSelectedDomainMatchesFullCanonical = true := by
  rcases (contractOk_iff inputs).1 hOk with
    ⟨_hSorted, _hBudget, _hSubset, hSelected, _hContraction⟩
  exact hSelected

theorem contractOk_implies_repairedContractionHolds
    (inputs : ContractInputs)
    (hOk : (buildContract inputs).contractOk = true) :
    inputs.repairedContractionHolds = true := by
  rcases (contractOk_iff inputs).1 hOk with
    ⟨_hSorted, _hBudget, _hSubset, _hSelected, hContraction⟩
  exact hContraction

/-- Honest packaging theorem for the current repaired prefilter boundary.

If `contractOk = true` and the repaired booleans are separately interpreted as a
selected-domain minimum witness plus a contraction proof, then the selected
domain already yields a bounded-domain minimum key.
-/
theorem contractOk_and_interpretation_implies_bounded_global_minimality
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ} {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    (inputs : ContractInputs)
    (hOk : (buildContract inputs).contractOk = true)
    (hSelected :
      inputs.repairedSelectedDomainMatchesFullCanonical = true →
        SelectedDomainMinimumWitness cap maxLegs selected routeKey)
    (hContraction :
      inputs.repairedContractionHolds = true →
        ContractsToSelected cap maxLegs selected routeKey) :
    ∃ allocStar,
      SelectedFeasible cap maxLegs selected allocStar ∧
      (∀ alloc, SelectedFeasible cap maxLegs selected alloc →
        routeKey allocStar ≤ routeKey alloc) ∧
      routeKey allocStar ∈ feasibleKeySet cap maxLegs routeKey ∧
      ∀ y ∈ feasibleKeySet cap maxLegs routeKey, routeKey allocStar ≤ y := by
  let witness :=
    hSelected (contractOk_implies_repairedSelectedDomainMatchesFullCanonical inputs hOk)
  have hContractionSemantic : ContractsToSelected cap maxLegs selected routeKey :=
    hContraction (contractOk_implies_repairedContractionHolds inputs hOk)
  have hGlobal :
      routeKey witness.allocStar ∈ feasibleKeySet cap maxLegs routeKey ∧
        ∀ y ∈ feasibleKeySet cap maxLegs routeKey, routeKey witness.allocStar ≤ y :=
    contraction_implies_selected_domain_global_minimality
      (routeKey := routeKey)
      (hStarSelected := witness.selectedFeasible)
      (hMinSelected := witness.minimalSelected)
      (hContraction := hContractionSemantic)
  exact ⟨witness.allocStar, witness.selectedFeasible, witness.minimalSelected, hGlobal.1, hGlobal.2⟩

/-- The same honest packaging theorem lifted to the unique bounded-domain
canonical minimum statement used by the promoted world-model. -/
theorem contractOk_and_interpretation_implies_bounded_canonical_exists
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ} {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    (inputs : ContractInputs)
    (hOk : (buildContract inputs).contractOk = true)
    (hSelected :
      inputs.repairedSelectedDomainMatchesFullCanonical = true →
        SelectedDomainMinimumWitness cap maxLegs selected routeKey)
    (hContraction :
      inputs.repairedContractionHolds = true →
        ContractsToSelected cap maxLegs selected routeKey) :
    ∃! k,
      k ∈ feasibleKeySet cap maxLegs routeKey ∧
        ∀ y ∈ feasibleKeySet cap maxLegs routeKey, k ≤ y := by
  let witness :=
    hSelected (contractOk_implies_repairedSelectedDomainMatchesFullCanonical inputs hOk)
  have hContractionSemantic : ContractsToSelected cap maxLegs selected routeKey :=
    hContraction (contractOk_implies_repairedContractionHolds inputs hOk)
  simpa [witness] using
    contraction_implies_selected_domain_canonical_exists
      (routeKey := routeKey)
      (hStarSelected := witness.selectedFeasible)
      (hMinSelected := witness.minimalSelected)
      (hContraction := hContractionSemantic)

/-- Verified-contract wrapper for the same bridge, so replayable contract
verification composes directly with the semantic interpretation hypotheses. -/
theorem verifyContract_and_contractOk_and_interpretation_implies_bounded_canonical_exists
    {n Q : ℕ} {PoolId : Type} [LinearOrder PoolId]
    {cap : Fin n → ℕ} {maxLegs : ℕ} {selected : Finset (Fin n)}
    (routeKey : Alloc n Q → Key PoolId)
    (inputs : ContractInputs)
    {contract : Contract}
    (hVerify : verifyContract inputs contract)
    (hOk : contract.contractOk = true)
    (hSelected :
      inputs.repairedSelectedDomainMatchesFullCanonical = true →
        SelectedDomainMinimumWitness cap maxLegs selected routeKey)
    (hContraction :
      inputs.repairedContractionHolds = true →
        ContractsToSelected cap maxLegs selected routeKey) :
    ∃! k,
      k ∈ feasibleKeySet cap maxLegs routeKey ∧
        ∀ y ∈ feasibleKeySet cap maxLegs routeKey, k ≤ y := by
  unfold verifyContract at hVerify
  subst contract
  exact contractOk_and_interpretation_implies_bounded_canonical_exists
    (routeKey := routeKey)
    (inputs := inputs)
    hOk
    hSelected
    hContraction

end
end ExactOutManyPoolRepairedPrefilterSemanticBridge
end Routing
end TauSwap
