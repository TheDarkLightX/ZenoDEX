import Proofs.GlobalEconomicStateRefinementV2

/-!
# GlobalSettlementABI V2 nonempty accepted witness

This file constructs one concrete, bounded `ASSET_TRANSFER` occurrence that
inhabits the combined global state/effect refinement relation.  The witness
moves three ZUSD atoms from Alice to Bob, preserves total owned supply, changes
exactly the asset-transfer lane root, consumes exactly one occurrence, records
that replay identity at the next height, and emits no external outbox effect.

This is a mathematical non-vacuity witness for the modeled relation.  It does
not establish Python or Rust execution refinement, canonical hash correctness,
runtime reachability, verifier authority, settlement authority, release status,
or production readiness.
-/

namespace Proofs
namespace GlobalEconomicStateRefinementV2Nonempty

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

def transferPreLaneRoots (_ : LaneId) : RootId := "lane-root-pre"

def transferPostLaneRoots : LaneId → RootId
  | .assetTransfer => "lane-root-post"
  | _ => "lane-root-pre"

def transferReplayPost (replayId : Identifier) : Option RootId :=
  if replayId = "replay-transfer-1" then some "occurrence-transfer-1" else none

def transferPreState : GlobalState where
  stateRoot := "state-root-pre"
  chainId := "chain"
  deploymentRoot := "deployment-root"
  writerEpoch := 0
  height := 0
  profileRoot := "profile-root"
  laneRoots := transferPreLaneRoots
  laneReleaseIds := fun _ => "lane-release"
  laneEnabled := fun _ => true
  balances := [⟨"alice", "ZUSD", "accounts", 10⟩]
  supplies := [⟨"ZUSD", 10⟩]
  custody := []
  liabilities := []
  reserves := []
  oracleOccurrences := fun _ => none
  replayState := fun _ => none
  terminalObligations := []
  historyRoot := "history-root"
  outbox := []

def transferPostState : GlobalState where
  stateRoot := "state-root-post"
  chainId := "chain"
  deploymentRoot := "deployment-root"
  writerEpoch := 0
  height := 1
  profileRoot := "profile-root"
  laneRoots := transferPostLaneRoots
  laneReleaseIds := fun _ => "lane-release"
  laneEnabled := fun _ => true
  balances :=
    [ ⟨"alice", "ZUSD", "accounts", 7⟩,
      ⟨"bob", "ZUSD", "accounts", 3⟩ ]
  supplies := [⟨"ZUSD", 10⟩]
  custody := []
  liabilities := []
  reserves := []
  oracleOccurrences := fun _ => none
  replayState := transferReplayPost
  terminalObligations := []
  historyRoot := "history-root"
  outbox := []

def transferEffects : EffectPlan where
  rows :=
    [ ⟨.accountMovement, "alice", "ZUSD", "accounts", -3⟩,
      ⟨.accountMovement, "bob", "ZUSD", "accounts", 3⟩ ]
  assetConservation := [⟨"ZUSD", 10, 10, 10, 10, 0, 0⟩]
  feeConservation := []
  laneWrites := [⟨.assetTransfer, "lane-root-pre", "lane-root-post"⟩]
  occurrenceConsumptions := ["occurrence-transfer-1"]
  externalOutboxEnqueue := []

def transferOccurrence : CommandOccurrence where
  occurrenceId := "occurrence-transfer-1"
  replayId := "replay-transfer-1"
  chainId := "chain"
  deploymentRoot := "deployment-root"
  profileRoot := "profile-root"
  preStateRoot := "state-root-pre"
  height := 1

def transferTerminalPlan : TerminalPlan := ⟨[]⟩
def transferOraclePlan : OraclePlan := ⟨[]⟩

theorem transfer_pre_quantities_admitted :
    StateQuantitiesAdmitted transferPreState := by
  simp [StateQuantitiesAdmitted, SparseAmountRowsAdmitted,
    SparseSupplyRowsAdmitted, FitsU128, maxU128, FitsU64, maxU64,
    ReplayOccurrenceIdsInjective, OracleRegistryAdmitted,
    OracleRegistryWithinGlobalHeight, OracleRegistryKeysMatch,
    transferPreState, ownedFor, liabilityFor, amountForAsset, supplyFor]
  intro asset
  by_cases h : "ZUSD" = asset <;> simp [h] <;> omega

theorem transfer_post_quantities_admitted :
    StateQuantitiesAdmitted transferPostState := by
  simp [StateQuantitiesAdmitted, SparseAmountRowsAdmitted,
    SparseSupplyRowsAdmitted, FitsU128, maxU128, FitsU64, maxU64,
    ReplayOccurrenceIdsInjective, OracleRegistryAdmitted,
    OracleRegistryWithinGlobalHeight, OracleRegistryKeysMatch,
    transferPostState, transferReplayPost, ownedFor, liabilityFor,
    amountForAsset, supplyFor]
  intro asset
  by_cases h : "ZUSD" = asset <;> simp [h] <;> omega

theorem transfer_effect_plan_admitted : EffectPlanAdmitted transferEffects := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [transferEffects, EffectRowAdmitted, FitsI128, minI128, maxI128]
  · simp [transferEffects, AssetConservationAdmitted, FitsU128, maxU128]
  · simp [transferEffects]
  · intro asset
    by_cases h : asset = "ZUSD"
    · subst h
      decide
    · simp [transferEffects, declaredIssueFor, declaredBurnFor, issuedFor,
        burnedFor, issueContribution, burnContribution]
  · intro asset
    simp [transferEffects, declaredCurrentAllocationsFor, allocatedFeeFor,
      feeAllocationContribution]
  · simp [PlanWithinItemBounds, transferEffects]
  · simp [PlanKeysUnique, transferEffects, EconomicEffectRow.key]

theorem transfer_states_preserve_owned_supply :
    OwnedMatchesSupply transferPreState ∧ OwnedMatchesSupply transferPostState := by
  constructor <;> intro asset <;> by_cases h : "ZUSD" = asset
  · subst h
    decide
  · simp [ownedFor, amountForAsset, supplyFor, transferPreState, h]
  · subst h
    decide
  · simp [ownedFor, amountForAsset, supplyFor, transferPostState, h]

theorem transfer_balance_delta_identity (alice bob : Prop)
    [Decidable alice] [Decidable bob] :
    (if alice then (7 : Int) else 0) + (if bob then 3 else 0) -
        (if alice then 10 else 0) =
      (if alice then -3 else 0) + (if bob then 3 else 0) := by
  by_cases hAlice : alice <;> by_cases hBob : bob <;> simp [hAlice, hBob]

theorem transfer_running_deltas_fit (alice bob : Prop)
    [Decidable alice] [Decidable bob] :
    FitsI128 (if alice then -3 else 0) ∧
      FitsI128 ((if alice then -3 else 0) + (if bob then 3 else 0)) := by
  by_cases hAlice : alice <;> by_cases hBob : bob <;>
    simp [hAlice, hBob, FitsI128, minI128, maxI128] <;> omega

theorem transfer_account_table_exact :
    ExactTableEffect .accountMovement transferPreState.balances
      transferPostState.balances transferEffects := by
  intro owner asset domain
  simpa [amountAt, effectFor, transferPreState, transferPostState,
    transferEffects] using
    transfer_balance_delta_identity
      ("alice" = owner ∧ "ZUSD" = asset ∧ "accounts" = domain)
      ("bob" = owner ∧ "ZUSD" = asset ∧ "accounts" = domain)

theorem transfer_state_bearing_aggregates_fit :
    StateBearingAggregatesFitI128 transferEffects := by
  intro owner asset domain
  simpa [RunningTotalsFitI128, stateBearingContribution, transferEffects] using
    transfer_running_deltas_fit
      ("alice" = owner ∧ "ZUSD" = asset ∧ "accounts" = domain)
      ("bob" = owner ∧ "ZUSD" = asset ∧ "accounts" = domain)

theorem transfer_global_state_verified :
    Verified transferPreState transferEffects transferTerminalPlan
      transferOraclePlan [transferOccurrence] transferPostState := by
  refine {
    fixedContext := ?_,
    preQuantities := transfer_pre_quantities_admitted,
    postQuantities := transfer_post_quantities_admitted,
    effectPlan := transfer_effect_plan_admitted,
    laneWrites := ?_,
    economicTables := ?_,
    supplyEffects := ?_,
    conservationCoverage := ?_,
    conservationRows := ?_,
    annotations := ?_,
    ownedSupplyPre := transfer_states_preserve_owned_supply.1,
    ownedSupplyPost := transfer_states_preserve_owned_supply.2,
    liabilitiesPre := ?_,
    liabilitiesPost := ?_,
    terminal := ?_,
    oracle := ?_,
    replay := ?_,
    outboxClosed := ?_,
    zeroOccurrence := ?_ }
  · simp [FixedContext, transferPreState, transferPostState]
  · refine ⟨?_, ?_, ?_⟩
    · intro lane
      cases lane <;> simp [LaneWrittenBy, transferEffects, transferPreState,
        transferPostState, transferPreLaneRoots, transferPostLaneRoots]
    · intro lane changed
      cases lane <;> simp [transferPreState]
    · intro write member
      simp [transferEffects] at member
      subst write
      simp [transferPreState, transferPostState, transferPreLaneRoots,
        transferPostLaneRoots]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact transfer_account_table_exact
    · intro owner asset domain
      simp [amountAt, effectFor, transferPreState, transferPostState,
        transferEffects]
    · intro owner asset domain
      simp [amountAt, effectFor, transferPreState, transferPostState,
        transferEffects]
    · intro owner asset domain
      simp [amountAt, effectFor, transferPreState, transferPostState,
        transferEffects]
  · intro asset
    simp [supplyFor, issueDeltaFor, burnDeltaFor, issuedFor, burnedFor,
      issueContribution, burnContribution, transferPreState, transferPostState,
      transferEffects]
  · intro asset
    by_cases h : "ZUSD" = asset
    · subst h
      simp [EconomicAssetTouched, transferPreState, transferPostState,
        transferEffects, amountAt, supplyFor]
    · simp [EconomicAssetTouched, transferPreState, transferPostState,
        transferEffects, amountAt, supplyFor, h]
  · intro row member
    simp [transferEffects] at member
    subst row
    simp [ownedFor, amountForAsset, supplyFor, transferPreState,
      transferPostState]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact transfer_state_bearing_aggregates_fit
    · simp [FeeAllocationCreditsMirrored, transferEffects]
    · simp [RewardSlashMirrored, stateBearingEffectFor, effectFor,
        transferEffects]
    · simp [FeeRowsCanonical, transferEffects]
    · simp [FeeResidueExact, positiveDesignatedResidueFor,
        positiveCarriedResidueFor, transferEffects]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      liabilityFor, amountForAsset, openTerminalAmountFor, amountAt,
      transferPreState]
  · simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
      liabilityFor, amountForAsset, openTerminalAmountFor, amountAt,
      transferPostState]
  · simp [ExactTerminalRefinement, TerminalRegistryRefines,
      TerminalOwningLaneWrites, TerminalLiabilityEffects,
      TerminalLiabilityAggregatesFitI128, RunningTotalsFitI128,
      terminalLiabilityDeltaFor, effectFor, transferPreState,
      transferPostState, transferTerminalPlan, transferEffects]
  · simp [ExactOracleRefinement, OracleRegistryRefines, OracleLaneWrite,
      transferPreState, transferPostState, transferOraclePlan]
  · simp [ExactReplayRefinement, OrderedOccurrenceIds,
      OccurrenceContextMatches, ReplayRegistryRefines, transferOccurrence,
      transferPreState, transferPostState, transferEffects, transferReplayPost,
      FitsU64, maxU64]
    intro replayId different
    exact fun equal => different equal.symm
  · rfl
  · intro impossible
    contradiction

def transferAccepted : Accepted transferPreState where
  effects := transferEffects
  terminalPlan := transferTerminalPlan
  oraclePlan := transferOraclePlan
  occurrences := [transferOccurrence]
  post := transferPostState
  verified := transfer_global_state_verified

theorem combined_verified_relation_has_nonempty_asset_transfer :
    ∃ accepted : Accepted transferPreState,
      accepted.post = transferPostState ∧
      accepted.occurrences = [transferOccurrence] ∧
      accepted.effects.laneWrites =
        [⟨.assetTransfer, "lane-root-pre", "lane-root-post"⟩] ∧
      accepted.effects.externalOutboxEnqueue = [] :=
  ⟨transferAccepted, rfl, rfl, rfl, rfl⟩

end GlobalEconomicStateRefinementV2Nonempty
end Proofs
