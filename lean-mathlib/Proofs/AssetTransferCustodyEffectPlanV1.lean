import Proofs.AssetTransferEffectPlanV1
import Proofs.AssetTransferAnnotationMirrorsV1

/-!
# Custody-complete ASSET_TRANSFER V1 effect plans

This file refines the actual completed transfer plan with the private-port
physical totals used by the custody lane: balance rows plus custody rows.  It
does not include liabilities or reserves in that physical projection.  An
accepted result only rewrites the two owned-total fields of its existing asset
conservation rows; its verdict, post-state, effect rows, fee rows, lane write,
occurrence, outbox, supply fields, and issue/burn fields are retained.

The results are constructor-premise mathematical statements.  They do not
construct a global `Verified` value and do not establish commitment,
authentication, receipt, replay, runtime, compiler, or publication claims.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferCustodyEffectPlanV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace E
export Proofs.AssetTransferEffectPlanV1
  (CommitmentFields selectedPlan conservationRow feeRows selectedPlan_rows selectedPlan_fee_conservation
   complete complete_effect_plan_admitted complete_rejected_empty
   complete_accepted_plan complete_preserves_verdict_post complete_preserves_rows
   complete_accepted_exact_relations)
end E

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (Input Result StateAdmitted policyFor selectedInput lift step accepted_selected_step
   rejected_step_noop selectedInput_state_well_formed)
end K

namespace S
export Proofs.AssetTransferSparseTablesV1
  (Input Result step localState accounts projectedPlan movementEffects effectWire accepted_step_shape step_frame
   accepted_balance_equation CanonicalBalances PositiveAccounts Unique)
end S

namespace P
export Proofs.AssetTransferSparseSupplyV1
  (accepted_account_totals accepted_preserves_owned_supply)
end P

namespace T
export Proofs.AssetTransferRefinementV1
  (Policy Command Verdict RejectCode TransferState StateWellFormed CommandWellFormed IsU128 IsI128
   delta indicator accepted_iff_all_guards accepted_post_eq acceptedEffects)
end T

namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn mem_sortOn)
end C

namespace G
export Proofs.GlobalEconomicStateRefinementV2
  (GlobalState AmountRow SupplyRow amountForAsset amountAt supplyFor ownedFor
   StateQuantitiesAdmitted SparseAmountRowsAdmitted OwnedMatchesSupply
   ExactEconomicTables ExactSupplyEffects EconomicAssetTouched ExactConservationCoverage
   ConservationRowsMatchState)
end G

namespace A
export Proofs.AssetTransferAnnotationMirrorsV1
  (complete_annotation_mirrors_iff empty_annotation_mirrors)
end A

attribute [local instance] lexOrd

/-- The custody lane's private-port total: balances plus custody, excluding liabilities and
reserves. -/
def physicalFor (state : G.GlobalState) (asset : String) : Int :=
  G.amountForAsset state.balances asset + G.amountForAsset state.custody asset

/-- Rewrite exactly the two physical-total fields of one legacy conservation row. -/
def completeConservationRow (pre post : G.GlobalState) (row : AssetConservationRow) :
    AssetConservationRow :=
  { row with
    ownedAndCustodiedPreAtoms := physicalFor pre row.asset
    ownedAndCustodiedPostAtoms := physicalFor post row.asset }

/-- Rewrite exactly the conservation-row physical fields of an already evaluated plan. -/
def completePlan (pre post : G.GlobalState) (plan : EffectPlan) : EffectPlan :=
  { plan with
    assetConservation := plan.assetConservation.map (completeConservationRow pre post) }

theorem completeConservationRow_asset (pre post : G.GlobalState) (row : AssetConservationRow) :
    (completeConservationRow pre post row).asset = row.asset := rfl

theorem completeConservationRow_supply_pre (pre post : G.GlobalState) (row : AssetConservationRow) :
    (completeConservationRow pre post row).supplyPreAtoms = row.supplyPreAtoms := rfl

theorem completeConservationRow_supply_post (pre post : G.GlobalState) (row : AssetConservationRow) :
    (completeConservationRow pre post row).supplyPostAtoms = row.supplyPostAtoms := rfl

theorem completeConservationRow_authorized_issue (pre post : G.GlobalState)
    (row : AssetConservationRow) :
    (completeConservationRow pre post row).authorizedIssueAtoms = row.authorizedIssueAtoms := rfl

theorem completeConservationRow_authorized_burn (pre post : G.GlobalState)
    (row : AssetConservationRow) :
    (completeConservationRow pre post row).authorizedBurnAtoms = row.authorizedBurnAtoms := rfl

/-- Private transport over the already evaluated completed effect-plan result. -/
private def completeResult (input : K.Input)
    (output : K.Result) : K.Result :=
  match output.verdict with
  | .accepted =>
      { output with plan := completePlan input.pre.economic output.post.economic output.plan }
  | .rejected _ => output

/-- The custody completion evaluates the existing completed front door once and augments only
accepted conservation totals with the private-port physical values. -/
def complete (fields : E.CommitmentFields) (input : K.Input) : K.Result :=
  completeResult input (E.complete fields input)

theorem completePlan_rows (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).rows = plan.rows := rfl

theorem completePlan_fee_conservation (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).feeConservation = plan.feeConservation := rfl

theorem completePlan_lane_writes (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).laneWrites = plan.laneWrites := rfl

theorem completePlan_occurrences (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).occurrenceConsumptions = plan.occurrenceConsumptions := rfl

theorem completePlan_outbox (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).externalOutboxEnqueue = plan.externalOutboxEnqueue := rfl

theorem completePlan_conservation (pre post : G.GlobalState) (plan : EffectPlan) :
    (completePlan pre post plan).assetConservation =
      plan.assetConservation.map (completeConservationRow pre post) := rfl

private theorem completeResult_preserves_verdict_post (input : K.Input) (output : K.Result) :
    (completeResult input output).verdict = output.verdict ∧
      (completeResult input output).post = output.post := by
  cases verdict : output.verdict <;> simp [completeResult, verdict]

private theorem completeResult_rejected {input : K.Input} {output : K.Result} {code : T.RejectCode}
    (rejected : output.verdict = .rejected code) :
    completeResult input output = output := by
  simp [completeResult, rejected]

theorem complete_preserves_verdict_post (fields : E.CommitmentFields) (input : K.Input) :
    (complete fields input).verdict = (E.complete fields input).verdict ∧
      (complete fields input).post = (E.complete fields input).post := by
  exact completeResult_preserves_verdict_post input (E.complete fields input)

theorem complete_rejected {fields : E.CommitmentFields} {input : K.Input} {code : T.RejectCode}
    (rejected : (K.step input).verdict = .rejected code) :
    complete fields input = E.complete fields input := by
  have legacy : (E.complete fields input).verdict = .rejected code := by
    rw [(E.complete_preserves_verdict_post fields input).1]
    exact rejected
  exact completeResult_rejected legacy

theorem complete_rejected_empty {fields : E.CommitmentFields} {input : K.Input} {code : T.RejectCode}
    (rejected : (K.step input).verdict = .rejected code) :
    (complete fields input).post = input.pre ∧ (complete fields input).plan = EffectPlan.empty := by
  rw [complete_rejected rejected]
  exact E.complete_rejected_empty rejected

/-- Every rejected custody completion is the exact front-door rejection with the empty six-field
effect plan. -/
theorem complete_rejected_exact {fields : E.CommitmentFields} {input : K.Input} {code : T.RejectCode}
    (rejected : (K.step input).verdict = .rejected code) :
    complete fields input = ⟨.rejected code, input.pre, EffectPlan.empty⟩ := by
  rw [complete_rejected rejected]
  have legacyVerdict : (E.complete fields input).verdict = .rejected code := by
    rw [(E.complete_preserves_verdict_post fields input).1]
    exact rejected
  have legacyEmpty := E.complete_rejected_empty (fields := fields) rejected
  cases result : E.complete fields input with
  | mk verdict post plan =>
      simp only [result] at legacyVerdict legacyEmpty ⊢
      cases legacyVerdict
      rcases legacyEmpty with ⟨postEq, planEq⟩
      subst post
      subst plan
      rfl

/-- Apart from the mapped conservation rows, every effect-plan field is exactly inherited as a
mathematical value from the existing completed plan. -/
theorem complete_preserves_other_plan_fields (fields : E.CommitmentFields) (input : K.Input) :
    (complete fields input).plan.rows = (E.complete fields input).plan.rows ∧
      (complete fields input).plan.feeConservation = (E.complete fields input).plan.feeConservation ∧
      (complete fields input).plan.laneWrites = (E.complete fields input).plan.laneWrites ∧
      (complete fields input).plan.occurrenceConsumptions =
        (E.complete fields input).plan.occurrenceConsumptions ∧
      (complete fields input).plan.externalOutboxEnqueue =
        (E.complete fields input).plan.externalOutboxEnqueue := by
  unfold complete
  cases verdict : (E.complete fields input).verdict <;>
    simp [completeResult, verdict, completePlan]

theorem complete_accepted_plan {fields : E.CommitmentFields} {input : K.Input}
    (accepted : (K.step input).verdict = .accepted) :
    (complete fields input).plan = completePlan input.pre.economic
      (E.complete fields input).post.economic (E.complete fields input).plan := by
  have legacy : (E.complete fields input).verdict = .accepted := by
    rw [(E.complete_preserves_verdict_post fields input).1]
    exact accepted
  simp [complete, completeResult, legacy]

private theorem completePlan_projection_matches (pre post : G.GlobalState) (plan : EffectPlan)
    (projection : ProjectionMatches plan) : ProjectionMatches (completePlan pre post plan) := by
  intro asset
  simpa [completePlan, completeConservationRow, declaredIssueFor, declaredBurnFor] using
    projection asset

private theorem completePlan_fee_projection_matches (pre post : G.GlobalState) (plan : EffectPlan)
    (projection : FeeProjectionMatches plan) : FeeProjectionMatches (completePlan pre post plan) := by
  simpa [completePlan, FeeProjectionMatches] using projection

private theorem completePlan_within_item_bounds (pre post : G.GlobalState) (plan : EffectPlan)
    (bounds : PlanWithinItemBounds plan) : PlanWithinItemBounds (completePlan pre post plan) := by
  simpa [completePlan, PlanWithinItemBounds] using bounds

private theorem completePlan_keys_unique (pre post : G.GlobalState) (plan : EffectPlan)
    (keys : PlanKeysUnique plan) : PlanKeysUnique (completePlan pre post plan) := by
  simpa [completePlan, PlanKeysUnique, completeConservationRow] using keys

/-- Replacing physical fields preserves structural plan admission once their new row values
are admitted. -/
private theorem completePlan_admission_transport (pre post : G.GlobalState) (plan : EffectPlan)
    (legacy : EffectPlanAdmitted plan)
    (conservation : ∀ row ∈ plan.assetConservation,
      AssetConservationAdmitted (completeConservationRow pre post row)) :
    EffectPlanAdmitted (completePlan pre post plan) := by
  rcases legacy with ⟨rows, oldConservation, fees, projection, feeProjection, bounds, keys⟩
  refine ⟨?_, ?_, ?_, completePlan_projection_matches pre post plan projection,
    completePlan_fee_projection_matches pre post plan feeProjection,
    completePlan_within_item_bounds pre post plan bounds,
    completePlan_keys_unique pre post plan keys⟩
  · simpa [completePlan] using rows
  · intro row member
    obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp (by
      simpa [completePlan] using member)
    subst row
    exact conservation source sourceMember
  · simpa [completePlan] using fees

private theorem fitsU128_isU128 {atoms : Int} (fits : FitsU128 atoms) : T.IsU128 atoms := by
  simpa [T.IsU128, Proofs.AssetTransferRefinementV1.u128Max_eq_pow, FitsU128, maxU128]
    using fits

private theorem physicalFor_admitted {state : G.GlobalState}
    (quantities : G.StateQuantitiesAdmitted state) (asset : String) :
    FitsU128 (physicalFor state asset) := by
  rcases quantities with ⟨_, _, balances, _, custody, _, reserves, _, _, _, _, _, totals,
    _, _, _, _⟩
  have balancesU128 : ∀ row ∈ state.balances, T.IsU128 row.amountAtoms := fun row member =>
    fitsU128_isU128 (balances row member).1
  have custodyU128 : ∀ row ∈ state.custody, T.IsU128 row.amountAtoms := fun row member =>
    fitsU128_isU128 (custody row member).1
  have reservesU128 : ∀ row ∈ state.reserves, T.IsU128 row.amountAtoms := fun row member =>
    fitsU128_isU128 (reserves row member).1
  have balanceTotal := Proofs.AssetTransferPolicySelectionV1.amountForAsset_nonnegative
    state.balances balancesU128 asset
  have custodyTotal := Proofs.AssetTransferPolicySelectionV1.amountForAsset_nonnegative
    state.custody custodyU128 asset
  have reserveTotal := Proofs.AssetTransferPolicySelectionV1.amountForAsset_nonnegative
    state.reserves reservesU128 asset
  have ownedTotal := (totals asset).1
  unfold physicalFor
  unfold FitsU128 at ownedTotal ⊢
  unfold G.ownedFor at ownedTotal
  omega

private theorem selected_physical_preserved {input : K.Input} {policy : T.Policy}
    (admitted : K.StateAdmitted input.pre)
    (accepted : (S.step (K.selectedInput input policy)).verdict = .accepted) (asset : String) :
    physicalFor (S.step (K.selectedInput input policy)).post asset =
      physicalFor input.pre.economic asset := by
  have accounts := P.accepted_account_totals admitted.1.1 accepted asset
  unfold physicalFor
  rw [S.step_frame (K.selectedInput input policy)]
  simpa only [K.selectedInput] using congrArg
    (fun total => total + G.amountForAsset input.pre.economic.custody asset) accounts

private theorem completed_selected_conservation_admitted {fields : E.CommitmentFields}
    {input : K.Input} {policy : T.Policy} (admitted : K.StateAdmitted input.pre)
    (quantities : G.StateQuantitiesAdmitted input.pre.economic)
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (selectedAccepted : (S.step (K.selectedInput input policy)).verdict = .accepted) :
    AssetConservationAdmitted
      (completeConservationRow input.pre.economic (E.complete fields input).post.economic
        (E.conservationRow (K.selectedInput input policy))) := by
  have legacyAdmitted := E.complete_effect_plan_admitted fields input admitted
  have oldRow : AssetConservationAdmitted (E.conservationRow (K.selectedInput input policy)) := by
    apply legacyAdmitted.2.1
    rw [E.complete_accepted_plan accepted selection]
    simp [E.selectedPlan]
  rcases oldRow with ⟨_, _, supplyPre, supplyPost, _, _, _, supplyEquation⟩
  have postEq : (E.complete fields input).post.economic =
      (S.step (K.selectedInput input policy)).post := by
    obtain ⟨chosen, chosenSelection, _, selectedStep, _, _⟩ :=
      K.accepted_selected_step accepted
    have same : chosen = policy := Option.some.inj (chosenSelection.symm.trans selection)
    subst chosen
    rw [(E.complete_preserves_verdict_post fields input).2, selectedStep]
    simp only [K.lift]
  have physicalPre := physicalFor_admitted quantities input.command.asset
  have physicalSame : physicalFor (E.complete fields input).post.economic input.command.asset =
      physicalFor input.pre.economic input.command.asset := by
    rw [postEq]
    exact selected_physical_preserved admitted selectedAccepted input.command.asset
  have supplySame :
      G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset =
        G.supplyFor input.pre.economic.supplies input.command.asset := by
    simpa [E.conservationRow] using supplyEquation
  have supplyPre' : FitsU128
      (G.supplyFor input.pre.economic.supplies input.command.asset) := by
    simpa [E.conservationRow] using supplyPre
  have supplyPost' : FitsU128
      (G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset) := by
    simpa [E.conservationRow] using supplyPost
  change FitsU128 (physicalFor input.pre.economic input.command.asset) ∧
    FitsU128 (physicalFor (E.complete fields input).post.economic input.command.asset) ∧
    FitsU128 (G.supplyFor input.pre.economic.supplies input.command.asset) ∧
    FitsU128 (G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset) ∧
    FitsU128 0 ∧ FitsU128 0 ∧
    physicalFor (E.complete fields input).post.economic input.command.asset =
      physicalFor input.pre.economic input.command.asset + 0 - 0 ∧
    G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset =
      G.supplyFor input.pre.economic.supplies input.command.asset + 0 - 0
  refine ⟨physicalPre, ?_, supplyPre', supplyPost', zero_fits_u128, zero_fits_u128, ?_, ?_⟩
  · rw [physicalSame]
    exact physicalPre
  · rw [physicalSame]
    omega
  · simpa only [Int.add_zero, Int.sub_zero] using supplySame

/-- Initial quantitative admission supplies the u128 bounds for the custody-private totals of
every accepted plan; rejected plans remain the exact admitted empty plan. -/
theorem complete_effect_plan_admitted (fields : E.CommitmentFields) (input : K.Input)
    (admitted : K.StateAdmitted input.pre)
    (quantities : G.StateQuantitiesAdmitted input.pre.economic) :
    EffectPlanAdmitted (complete fields input).plan := by
  cases accepted : (K.step input).verdict with
  | rejected code =>
      rw [complete_rejected accepted, (E.complete_rejected_empty accepted).2]
      exact empty_effectPlan_admitted
  | accepted =>
      obtain ⟨policy, selection, selectedAccepted, _, _, _⟩ :=
        K.accepted_selected_step accepted
      rw [complete_accepted_plan accepted]
      apply completePlan_admission_transport _ _ _
        (E.complete_effect_plan_admitted fields input admitted)
      intro row member
      have rowEq : row = E.conservationRow (K.selectedInput input policy) := by
        rw [E.complete_accepted_plan accepted selection] at member
        simpa [E.selectedPlan] using member
      subst row
      exact completed_selected_conservation_admitted admitted quantities accepted selection
        selectedAccepted

/-- Accepted custody completion leaves the sparse balance-table and supply equations exact,
because those equations observe rows and post-state rather than conservation annotations. -/
theorem complete_accepted_exact_relations {fields : E.CommitmentFields} {input : K.Input}
    (admitted : K.StateAdmitted input.pre)
    (accepted : (K.step input).verdict = .accepted) :
    G.ExactEconomicTables input.pre.economic (complete fields input).post.economic
      (complete fields input).plan ∧
    G.ExactSupplyEffects input.pre.economic (complete fields input).post.economic
      (complete fields input).plan := by
  obtain ⟨tables, supply⟩ := E.complete_accepted_exact_relations admitted accepted
  have post : (complete fields input).post.economic = (E.complete fields input).post.economic :=
    congrArg (fun state => state.economic)
      (complete_preserves_verdict_post fields input).2
  have rows : (complete fields input).plan.rows = (E.complete fields input).plan.rows :=
    (complete_preserves_other_plan_fields fields input).1
  constructor
  · rw [post]
    simpa only [G.ExactEconomicTables, ExactTableEffect, effectFor, rows] using tables
  · rw [post]
    simpa only [G.ExactSupplyEffects, issueDeltaFor, burnDeltaFor, issuedFor, burnedFor, rows]
      using supply

private theorem complete_accepted_selected_post {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    (complete fields input).post.economic = (S.step (K.selectedInput input policy)).post := by
  have legacyPost : (E.complete fields input).post.economic =
      (S.step (K.selectedInput input policy)).post := by
    obtain ⟨chosen, chosenSelection, _, selectedStep, _, _⟩ :=
      K.accepted_selected_step accepted
    have same : chosen = policy := Option.some.inj (chosenSelection.symm.trans selection)
    subst chosen
    rw [(E.complete_preserves_verdict_post fields input).2, selectedStep]
    rfl
  rw [(complete_preserves_verdict_post fields input).2]
  exact legacyPost

private theorem complete_accepted_rows {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    (complete fields input).plan.rows = (E.selectedPlan fields (K.selectedInput input policy)).rows := by
  rw [(complete_preserves_other_plan_fields fields input).1,
    E.complete_accepted_plan accepted selection]

private theorem complete_accepted_fee_rows {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    (complete fields input).plan.feeConservation =
      (E.selectedPlan fields (K.selectedInput input policy)).feeConservation := by
  rw [(complete_preserves_other_plan_fields fields input).2.1,
    E.complete_accepted_plan accepted selection]

private theorem complete_accepted_conservation_rows {fields : E.CommitmentFields}
    {input : K.Input} {policy : T.Policy} (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    (complete fields input).plan.assetConservation =
      [completeConservationRow input.pre.economic (E.complete fields input).post.economic
        (E.conservationRow (K.selectedInput input policy))] := by
  rw [complete_accepted_plan accepted, E.complete_accepted_plan accepted selection]
  rfl

private theorem selectedPlan_row_asset (fields : E.CommitmentFields) (input : S.Input)
    {row : EconomicEffectRow} (member : row ∈ (E.selectedPlan fields input).rows) :
    row.asset = input.command.asset := by
  rw [E.selectedPlan_rows] at member
  change row ∈ C.sortOn S.effectWire
    (S.movementEffects .accountMovement input.command.asset
      (T.acceptedEffects (S.localState input) input.command).movements ++
    S.movementEffects .feeAllocation input.command.asset
      (T.acceptedEffects (S.localState input) input.command).feeAllocations) at member
  have raw := (C.mem_sortOn S.effectWire row _).mp member
  rcases List.mem_append.mp raw with movement | fee
  · obtain ⟨source, _, same⟩ := List.mem_map.mp (by
      simpa only [S.movementEffects] using movement)
    subst row
    rfl
  · obtain ⟨source, _, same⟩ := List.mem_map.mp (by
      simpa only [S.movementEffects] using fee)
    subst row
    rfl

private theorem selectedPlan_fee_asset (fields : E.CommitmentFields) (input : S.Input)
    {row : FeeConservationRow} (member : row ∈ (E.selectedPlan fields input).feeConservation) :
    row.asset = input.command.asset := by
  rw [E.selectedPlan_fee_conservation] at member
  unfold E.feeRows at member
  split at member
  · simp at member
  · rw [List.mem_singleton] at member
    subst row
    rfl

private theorem accepted_sender_delta_nonzero {input : S.Input}
    (amountWellFormed : T.CommandWellFormed input.command)
    (feeNonnegative : 0 ≤ input.policy.transferFeeAtoms)
    (accepted : (S.step input).verdict = .accepted) :
    T.delta (S.localState input) input.command input.command.sender ≠ 0 := by
  have leafAccepted := (S.accepted_step_shape accepted).1
  have guards :=
    (T.accepted_iff_all_guards input.context (S.localState input) input.command).mp leafAccepted
  have distinct : input.command.sender ≠ input.command.recipient := guards .selfTransfer
  have amountNonnegative : 0 ≤ input.command.amountAtoms := amountWellFormed.amount.1
  have amountNonzero : input.command.amountAtoms ≠ 0 := guards .zeroAmount
  have amountPositive : 0 < input.command.amountAtoms := by omega
  by_cases ownerIsSender : input.policy.feeOwner = input.command.sender
  · simp [T.delta, T.indicator, S.localState, ownerIsSender, distinct]
    omega
  · simp [T.delta, T.indicator, S.localState, distinct, Ne.symm ownerIsSender]
    omega

private theorem selected_sender_balance_changed {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances)
    (amountWellFormed : T.CommandWellFormed input.command)
    (feeNonnegative : 0 ≤ input.policy.transferFeeAtoms)
    (accepted : (S.step input).verdict = .accepted) :
    G.amountAt input.pre.balances input.command.sender input.command.asset S.accounts ≠
      G.amountAt (S.step input).post.balances input.command.sender input.command.asset S.accounts := by
  have deltaNonzero := accepted_sender_delta_nonzero amountWellFormed feeNonnegative accepted
  have equation := S.accepted_balance_equation canonical.1 canonical.2.1 accepted
    input.command.sender input.command.asset S.accounts
  rw [if_pos ⟨rfl, rfl⟩] at equation
  intro same
  apply deltaNonzero
  omega

private theorem physicalFor_eq_ownedFor {state : G.GlobalState}
    (reservesEmpty : state.reserves = []) (asset : String) :
    physicalFor state asset = G.ownedFor state asset := by
  unfold physicalFor G.ownedFor
  rw [reservesEmpty]
  simp [G.amountForAsset]

private theorem complete_accepted_conservation_rows_match {fields : E.CommitmentFields}
    {input : K.Input} {policy : T.Policy} (reservesEmpty : input.pre.economic.reserves = [])
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    G.ConservationRowsMatchState input.pre.economic (complete fields input).post.economic
      (complete fields input).plan := by
  intro row member
  have conservation := complete_accepted_conservation_rows (fields := fields) accepted selection
  rw [conservation] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst row
  have resultPost : (E.complete fields input).post.economic =
      (complete fields input).post.economic :=
    congrArg (fun state => state.economic) (complete_preserves_verdict_post fields input).2.symm
  have selectedPost := complete_accepted_selected_post (fields := fields) accepted selection
  have postReserves : (complete fields input).post.economic.reserves = [] := by
    rw [selectedPost, S.step_frame (K.selectedInput input policy)]
    exact reservesEmpty
  have preOwned := physicalFor_eq_ownedFor reservesEmpty input.command.asset
  have postOwned := physicalFor_eq_ownedFor postReserves input.command.asset
  dsimp only [completeConservationRow, E.conservationRow, K.selectedInput]
  change physicalFor input.pre.economic input.command.asset =
      G.ownedFor input.pre.economic input.command.asset ∧
    physicalFor (E.complete fields input).post.economic input.command.asset =
      G.ownedFor (complete fields input).post.economic input.command.asset ∧
    G.supplyFor input.pre.economic.supplies input.command.asset =
      G.supplyFor input.pre.economic.supplies input.command.asset ∧
    G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset =
      G.supplyFor (complete fields input).post.economic.supplies input.command.asset
  refine ⟨preOwned, ?_, rfl, ?_⟩
  · rw [resultPost]
    exact postOwned
  · rw [← selectedPost]

private theorem complete_accepted_touched_iff {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (admitted : K.StateAdmitted input.pre)
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (asset : String) :
    G.EconomicAssetTouched input.pre.economic (complete fields input).post.economic
      (complete fields input).plan asset ↔ input.command.asset = asset := by
  obtain ⟨chosen, chosenSelection, selectedAccepted, _, _, _⟩ :=
    K.accepted_selected_step accepted
  have chosenEq : chosen = policy := Option.some.inj (chosenSelection.symm.trans selection)
  subst chosen
  have selectedPost := complete_accepted_selected_post (fields := fields) accepted selection
  have selectedWellFormed := K.selectedInput_state_well_formed admitted selection
  have feeNonnegative : 0 ≤ policy.transferFeeAtoms := by
    simpa [K.selectedInput, S.localState] using selectedWellFormed.fee.1
  have senderChanged :
      G.amountAt input.pre.economic.balances input.command.sender input.command.asset S.accounts ≠
        G.amountAt (S.step (K.selectedInput input policy)).post.balances input.command.sender
          input.command.asset S.accounts := by
    simpa only [K.selectedInput] using selected_sender_balance_changed admitted.1 commandWellFormed
      feeNonnegative selectedAccepted
  constructor
  · intro touched
    rcases touched with rows | fees | balances | custody | liabilities | reserves | supplyChanged
    · rcases rows with ⟨row, rowMember, rowAsset⟩
      rw [complete_accepted_rows (fields := fields) accepted selection] at rowMember
      have selectedAsset := selectedPlan_row_asset fields (K.selectedInput input policy) rowMember
      calc
        input.command.asset = row.asset := by simpa only [K.selectedInput] using selectedAsset.symm
        _ = asset := rowAsset
    · rcases fees with ⟨row, rowMember, rowAsset⟩
      rw [complete_accepted_fee_rows (fields := fields) accepted selection] at rowMember
      have selectedAsset := selectedPlan_fee_asset fields (K.selectedInput input policy) rowMember
      calc
        input.command.asset = row.asset := by simpa only [K.selectedInput] using selectedAsset.symm
        _ = asset := rowAsset
    · rcases balances with ⟨owner, domain, changed⟩
      rw [selectedPost] at changed
      have equation := S.accepted_balance_equation admitted.1.1 admitted.1.2.1 selectedAccepted
        owner asset domain
      simp only [K.selectedInput] at equation
      apply Classical.byContradiction
      intro different
      have location : ¬(input.command.asset = asset ∧ S.accounts = domain) :=
        fun same => different same.1
      rw [if_neg location] at equation
      have selectedEquation :
          G.amountAt (S.step (K.selectedInput input policy)).post.balances owner asset domain -
            G.amountAt input.pre.economic.balances owner asset domain = 0 := by
        simpa only [K.selectedInput] using equation
      exfalso
      apply changed
      have unchanged :
          G.amountAt (S.step (K.selectedInput input policy)).post.balances owner asset domain =
            G.amountAt input.pre.economic.balances owner asset domain := by
        omega
      exact unchanged.symm
    · rcases custody with ⟨owner, domain, changed⟩
      exfalso
      apply changed
      rw [selectedPost, S.step_frame (K.selectedInput input policy)]
      rfl
    · rcases liabilities with ⟨owner, domain, changed⟩
      exfalso
      apply changed
      rw [selectedPost, S.step_frame (K.selectedInput input policy)]
      rfl
    · rcases reserves with ⟨owner, domain, changed⟩
      exfalso
      apply changed
      rw [selectedPost, S.step_frame (K.selectedInput input policy)]
      rfl
    · exfalso
      apply supplyChanged
      rw [selectedPost, S.step_frame (K.selectedInput input policy)]
      rfl
  · intro same
    subst asset
    exact Or.inr (Or.inr (Or.inl ⟨input.command.sender, S.accounts, by
      rw [selectedPost]
      exact senderChanged⟩))

/-- An accepted, reserve-free custody completion covers exactly the assets touched by the actual
transition.  `CommandWellFormed` supplies the nonnegative amount constructor premise needed to
show that the accepted sender movement is physically nonzero. -/
theorem complete_accepted_conservation {fields : E.CommitmentFields} {input : K.Input}
    (admitted : K.StateAdmitted input.pre) (reservesEmpty : input.pre.economic.reserves = [])
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted) :
    G.ExactConservationCoverage input.pre.economic (complete fields input).post.economic
      (complete fields input).plan ∧
    G.ConservationRowsMatchState input.pre.economic (complete fields input).post.economic
      (complete fields input).plan := by
  obtain ⟨policy, selection, _, _, _, _⟩ := K.accepted_selected_step accepted
  refine ⟨?_, complete_accepted_conservation_rows_match (fields := fields) reservesEmpty
    accepted selection⟩
  intro asset
  rw [complete_accepted_conservation_rows (fields := fields) accepted selection,
    complete_accepted_touched_iff (fields := fields) admitted commandWellFormed accepted
      selection asset]
  simp [completeConservationRow, E.conservationRow, K.selectedInput]

/-- If the actual input global state owns its full supply, the selected sparse transition keeps
that equality for every asset; custody completion does not alter the post-state. -/
theorem complete_accepted_preserves_owned_supply {fields : E.CommitmentFields} {input : K.Input}
    (admitted : K.StateAdmitted input.pre) (owned : G.OwnedMatchesSupply input.pre.economic)
    (accepted : (K.step input).verdict = .accepted) :
    G.OwnedMatchesSupply (complete fields input).post.economic := by
  obtain ⟨policy, selection, selectedAccepted, _, _, _⟩ := K.accepted_selected_step accepted
  have preserved := P.accepted_preserves_owned_supply admitted.1.1 owned selectedAccepted
  rw [complete_accepted_selected_post (fields := fields) accepted selection]
  simpa only [K.selectedInput] using preserved

private theorem annotationMirrors_congr {left right : EffectPlan}
    (rows : left.rows = right.rows) (fees : left.feeConservation = right.feeConservation) :
    AnnotationMirrors left ↔ AnnotationMirrors right := by
  unfold AnnotationMirrors StateBearingAggregatesFitI128 FeeAllocationCreditsMirrored
    RewardSlashMirrored FeeRowsCanonical FeeResidueExact positiveDesignatedResidueFor
    positiveCarriedResidueFor stateBearingEffectFor effectFor
  rw [rows, fees]

/-- Custody completion preserves every row and fee observation used by the existing five-clause
annotation relation, so its accepted front-door characterization transfers unchanged. -/
theorem complete_annotation_mirrors_iff (fields : E.CommitmentFields) {input : K.Input}
    (admitted : K.StateAdmitted input.pre) (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted) :
    AnnotationMirrors (complete fields input).plan ↔
      ∃ policy, K.policyFor input.pre.policies input.command.asset = some policy ∧
        (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender) := by
  have preserved := annotationMirrors_congr (complete_preserves_other_plan_fields fields input).1
    (complete_preserves_other_plan_fields fields input).2.1
  exact preserved.trans (A.complete_annotation_mirrors_iff fields admitted commandWellFormed accepted)

end AssetTransferCustodyEffectPlanV1
end Proofs
