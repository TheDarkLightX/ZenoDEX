import Proofs.AssetLaneCustodyRecompositionV2
import Proofs.AssetTransferFiniteEffectPlanV2

/-!
# Custody completion for finite V2 asset-lane effect plans

The existing transfer and managed leaves report account-only conservation rows.
This file models the custody coordinator's accepted-result completion: replace
the two physical totals with totals from the complete state and replace the leaf
lane write with one supplied complete-state pre/post root pair. Every other
effect-plan field is retained exactly. Source rejection returns the six-empty
plan and never reaches completion.

The complete roots are explicit observations. This finite state model retains
origin keys rather than every runtime field, so these theorems do not establish
runtime hashing, root authenticity, codecs, receipts, resource correspondence,
or publication authority.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyEffectPlanV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace C
export AssetLaneCustodyRefinementV2 (State RowsRepresentable PhysicalBalanced
  physicalFor supplyAt transferView managedView transferPost managedPost
  transfer_physical_lift managed_physical_lift)
end C
namespace R
export AssetLaneCustodyRecompositionV2 (managedAssets filteredView recomposedPost
  selected_supply_numeric_rows filtered_view_eq recomposed_post_eq)
end R
namespace H
export AssetLaneSharedProjectionV2 (selectRows supply_filter_lookup)
end H
namespace Q
export AssetLaneFiniteRecompositionV2 (selectSupplies mergeBalances mergeSupplies)
end Q
namespace FT
export AssetTransferFiniteOutcomeV2 (State Structural transition policyFor policyFor_spec
  project accepted_post_effects accepted_selected_leaf accepted_accounting)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (State Structural transition policyFor policyFor_spec
  project accepted_post_effects accepted_selected_leaf accepted_accounting)
end FM
namespace TP
export AssetTransferFiniteEffectPlanV2 (transferPlan transferConservation
  transfer_conservation_admitted transfer_plan_admitted)
end TP
namespace MP
export AssetLaneFiniteEffectPlanV2 (managedPlan managedConservation
  managed_conservation_admitted managed_plan_admitted)
end MP
namespace T
export AssetTransferRefinementV2 (RootModel Context Command Policy)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (RootModel Context Command Policy
  CommandWellFormed signedAmount isIssue)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes ValidToken)
end B

/-- The full transfer leaf reads the complete account and supply tables. -/
def transferSource (pre : C.State) : FT.State :=
  { moduleReleaseId := pre.transferState.moduleReleaseId
    policies := pre.transferState.policies
    balances := pre.transferState.balances
    supplies := pre.transferState.supplies }

/-- The managed leaf reads exactly the declared managed-asset projection. -/
def managedSource (pre : C.State) : FM.State :=
  { moduleReleaseId := pre.transferState.moduleReleaseId
    policies := pre.managedPolicies
    balances := H.selectRows (R.managedAssets pre) pre.transferState.balances
    supplies := Q.selectSupplies (R.managedAssets pre) pre.transferState.supplies }

/-- Rebuild the complete transfer state from every field of the actual finite
leaf post while retaining the custody frame. -/
def transferPostFromLeaf (pre : C.State) (leafPost : FT.State) : C.State :=
  { pre with transferState :=
      ⟨leafPost.moduleReleaseId, leafPost.policies, leafPost.balances, leafPost.supplies⟩ }

/-- Merge the actual managed-leaf post into the unchanged non-managed
complement, retaining complete policies, registry and custody. -/
def managedPostFromLeaf (pre : C.State) (leafPost : FM.State) : C.State :=
  { pre with transferState := { pre.transferState with
      balances := Q.mergeBalances (R.managedAssets pre) pre.transferState.balances
        leafPost.balances
      supplies := Q.mergeSupplies (R.managedAssets pre) pre.transferState.supplies
        leafPost.supplies } }

theorem transfer_post_from_leaf_eq {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {policy : T.Policy}
    (selected : FT.policyFor (transferSource pre) command.asset = some policy)
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    transferPostFromLeaf pre (FT.transition digest ctx (transferSource pre) command).post =
      C.transferPost pre policy command := by
  rw [(FT.accepted_post_effects accepted).1]
  rw [AssetTransferFiniteOutcomeV2.candidate, selected]
  rfl

theorem managed_post_from_leaf_eq {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command}
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    managedPostFromLeaf pre (FM.transition digest ctx (managedSource pre) command).post =
      R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command) := by
  rw [(FM.accepted_post_effects accepted).1]
  rfl

def completeConservationRow (pre post : C.State)
    (row : AssetConservationRow) : AssetConservationRow :=
  { row with
    ownedAndCustodiedPreAtoms := C.physicalFor pre row.asset
    ownedAndCustodiedPostAtoms := C.physicalFor post row.asset }

/-- Accepted-result completion changes exactly conservation physical totals and
the single lane write. `completePreRoot` and `completePostRoot` are supplied
complete-state root observations. -/
def completePlan (pre post : C.State) (completePreRoot completePostRoot : RootId)
    (source : EffectPlan) : EffectPlan :=
  { source with
    assetConservation := source.assetConservation.map (completeConservationRow pre post)
    laneWrites := [⟨.assetTransfer, completePreRoot, completePostRoot⟩] }

theorem complete_plan_fields (pre post : C.State) (completePreRoot completePostRoot : RootId)
    (source : EffectPlan) :
    (completePlan pre post completePreRoot completePostRoot source).rows = source.rows ∧
      (completePlan pre post completePreRoot completePostRoot source).assetConservation =
        source.assetConservation.map (completeConservationRow pre post) ∧
      (completePlan pre post completePreRoot completePostRoot source).feeConservation =
        source.feeConservation ∧
      (completePlan pre post completePreRoot completePostRoot source).laneWrites =
        [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
      (completePlan pre post completePreRoot completePostRoot source).occurrenceConsumptions =
        source.occurrenceConsumptions ∧
      (completePlan pre post completePreRoot completePostRoot source).externalOutboxEnqueue =
        source.externalOutboxEnqueue := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Admission of a completed row follows from source-row admission and the two
actual state invariants, once source and complete selected-asset supplies are
identified. No completed-row equation is an input. -/
theorem complete_conservation_admitted {pre post : C.State} {row : AssetConservationRow}
    (source : AssetConservationAdmitted row) (preBalanced : C.PhysicalBalanced pre)
    (postBalanced : C.PhysicalBalanced post)
    (preSupply : C.supplyAt pre row.asset = row.supplyPreAtoms)
    (postSupply : C.supplyAt post row.asset = row.supplyPostAtoms) :
    AssetConservationAdmitted (completeConservationRow pre post row) := by
  rcases source with ⟨_, _, supplyPre, supplyPost, issue, burn, _, supplyEquation⟩
  have physicalPre : C.physicalFor pre row.asset = row.supplyPreAtoms :=
    (preBalanced row.asset).trans preSupply
  have physicalPost : C.physicalFor post row.asset = row.supplyPostAtoms :=
    (postBalanced row.asset).trans postSupply
  change FitsU128 (C.physicalFor pre row.asset) ∧
    FitsU128 (C.physicalFor post row.asset) ∧ FitsU128 row.supplyPreAtoms ∧
    FitsU128 row.supplyPostAtoms ∧ FitsU128 row.authorizedIssueAtoms ∧
    FitsU128 row.authorizedBurnAtoms ∧
    C.physicalFor post row.asset =
      C.physicalFor pre row.asset + row.authorizedIssueAtoms - row.authorizedBurnAtoms ∧
    row.supplyPostAtoms =
      row.supplyPreAtoms + row.authorizedIssueAtoms - row.authorizedBurnAtoms
  exact ⟨physicalPre ▸ supplyPre, physicalPost ▸ supplyPost, supplyPre, supplyPost,
    issue, burn, by simpa only [physicalPre, physicalPost] using supplyEquation, supplyEquation⟩

private theorem complete_projection (pre post : C.State)
    (completePreRoot completePostRoot : RootId) (source : EffectPlan)
    (projection : ProjectionMatches source) :
    ProjectionMatches (completePlan pre post completePreRoot completePostRoot source) := by
  intro asset
  simpa [completePlan, completeConservationRow, declaredIssueFor, declaredBurnFor] using
    projection asset

private theorem complete_fee_projection (pre post : C.State)
    (completePreRoot completePostRoot : RootId) (source : EffectPlan)
    (projection : FeeProjectionMatches source) :
    FeeProjectionMatches (completePlan pre post completePreRoot completePostRoot source) := by
  simpa [completePlan, FeeProjectionMatches] using projection

private theorem complete_bounds (pre post : C.State)
    (completePreRoot completePostRoot : RootId) (source : EffectPlan)
    (oneLane : source.laneWrites.length = 1) (bounds : PlanWithinItemBounds source) :
    PlanWithinItemBounds (completePlan pre post completePreRoot completePostRoot source) := by
  simpa [completePlan, PlanWithinItemBounds, oneLane] using bounds

private theorem complete_keys (pre post : C.State)
    (completePreRoot completePostRoot : RootId) (source : EffectPlan)
    (keys : PlanKeysUnique source) :
    PlanKeysUnique (completePlan pre post completePreRoot completePostRoot source) := by
  rcases keys with ⟨rows, conservation, fees, _, occurrences, outbox⟩
  simp only [completePlan, PlanKeysUnique, completeConservationRow, List.map_map,
    Function.comp_def]
  exact ⟨rows, conservation, fees, by simp, occurrences, outbox⟩

/-- Replacing a known singleton lane write and the admitted physical fields
preserves full numeric plan admission. -/
theorem complete_plan_admission {pre post : C.State} {completePreRoot completePostRoot : RootId}
    {source : EffectPlan} (admitted : EffectPlanAdmitted source)
    (conservation : ∀ row ∈ source.assetConservation,
      AssetConservationAdmitted (completeConservationRow pre post row))
    (oneLane : source.laneWrites.length = 1) :
    EffectPlanAdmitted (completePlan pre post completePreRoot completePostRoot source) := by
  rcases admitted with ⟨rows, _, fees, projection, feeProjection, bounds, keys⟩
  refine ⟨?_, ?_, ?_, complete_projection pre post completePreRoot completePostRoot source projection,
    complete_fee_projection pre post completePreRoot completePostRoot source feeProjection,
    complete_bounds pre post completePreRoot completePostRoot source oneLane bounds,
    complete_keys pre post completePreRoot completePostRoot source keys⟩
  · simpa [completePlan] using rows
  · intro row member
    obtain ⟨sourceRow, sourceMember, rfl⟩ := List.mem_map.mp (by
      simpa [completePlan] using member)
    exact conservation sourceRow sourceMember
  · simpa [completePlan] using fees

def transferCompletedConservation (pre post : C.State) (command : T.Command) :
    AssetConservationRow :=
  ⟨command.asset, C.physicalFor pre command.asset, C.physicalFor post command.asset,
    C.supplyAt pre command.asset, C.supplyAt post command.asset, 0, 0⟩

def managedCompletedConservation (pre post : C.State) (command : M.Command) :
    AssetConservationRow :=
  ⟨command.asset, C.physicalFor pre command.asset, C.physicalFor post command.asset,
    C.supplyAt pre command.asset, C.supplyAt post command.asset,
    if M.isIssue command then command.amountAtoms else 0,
    if M.isIssue command then 0 else command.amountAtoms⟩

/-- Completion is unreachable on source rejection. Accepted transfer results
also fail closed if their supposedly selected policy is absent. -/
def transferEffectPlan (digest : B.Bytes → String) (ctx : T.Context) (pre : C.State)
    (command : T.Command) (completePreRoot completePostRoot : RootId) : EffectPlan :=
  let source := transferSource pre
  let result := FT.transition digest ctx source command
  match result.verdict with
  | .rejected _ => EffectPlan.empty
  | .accepted =>
      match FT.policyFor source command.asset with
      | none => EffectPlan.empty
      | some _ => completePlan pre (transferPostFromLeaf pre result.post)
          completePreRoot completePostRoot (TP.transferPlan digest ctx source command)

def managedEffectPlan (digest : B.Bytes → String) (ctx : M.Context) (pre : C.State)
    (command : M.Command) (completePreRoot completePostRoot : RootId) : EffectPlan :=
  let source := managedSource pre
  let result := FM.transition digest ctx source command
  match result.verdict with
  | .rejected _ => EffectPlan.empty
  | .accepted => completePlan pre (managedPostFromLeaf pre result.post)
      completePreRoot completePostRoot (MP.managedPlan digest ctx source command)

theorem transfer_rejected_empty {digest : B.Bytes → String} {ctx : T.Context} {pre : C.State}
    {command : T.Command} {completePreRoot completePostRoot : RootId}
    {code : AssetTransferFiniteOutcomeV2.RejectCode}
    (rejected : (FT.transition digest ctx (transferSource pre) command).verdict = .rejected code) :
    transferEffectPlan digest ctx pre command completePreRoot completePostRoot = EffectPlan.empty := by
  simp only [transferEffectPlan, rejected]

theorem managed_rejected_empty {digest : B.Bytes → String} {ctx : M.Context} {pre : C.State}
    {command : M.Command} {completePreRoot completePostRoot : RootId}
    {code : ManagedAssetFiniteOutcomeV2.RejectCode}
    (rejected : (FM.transition digest ctx (managedSource pre) command).verdict = .rejected code) :
    managedEffectPlan digest ctx pre command completePreRoot completePostRoot = EffectPlan.empty := by
  simp only [managedEffectPlan, rejected]

theorem transfer_accepted_policy {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} (roots : T.RootModel)
    (structural : FT.Structural (transferSource pre))
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    ∃ policy, FT.policyFor (transferSource pre) command.asset = some policy ∧
      policy ∈ pre.transferState.policies ∧
      (AssetTransferRefinementV2.transition roots ctx (C.transferView pre policy) command).verdict =
        .accepted := by
  obtain ⟨policy, selected, scalar, _⟩ :=
    FT.accepted_selected_leaf roots structural.balanceUnique accepted
  refine ⟨policy, selected, (FT.policyFor_spec selected).1, ?_⟩
  exact scalar

theorem transfer_completed_row_exact {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {policy : T.Policy}
    (structural : FT.Structural (transferSource pre))
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    completeConservationRow pre (C.transferPost pre policy command)
        (TP.transferConservation (transferSource pre)
          (FT.transition digest ctx (transferSource pre) command).post command) =
      transferCompletedConservation pre (C.transferPost pre policy command) command := by
  have supplies := (FT.accepted_accounting structural.balanceUnique accepted command.asset).2
  simp only [completeConservationRow, transferCompletedConservation, TP.transferConservation,
    C.supplyAt, C.transferPost]
  rw [supplies]
  rfl

theorem transfer_accepted_conservation {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {policy : T.Policy} (roots : T.RootModel)
    (admitted : C.RowsRepresentable pre)
    (structural : FT.Structural (transferSource pre))
    (selected : FT.policyFor (transferSource pre) command.asset = some policy)
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    AssetConservationAdmitted
      (transferCompletedConservation pre (C.transferPost pre policy command) command) := by
  obtain ⟨chosen, chosenSelected, scalar, _⟩ :=
    FT.accepted_selected_leaf roots structural.balanceUnique accepted
  have same : chosen = policy := Option.some.inj (chosenSelected.symm.trans selected)
  subst chosen
  have postBalanced : C.PhysicalBalanced (C.transferPost pre policy command) :=
    (C.transfer_physical_lift pre policy command admitted.balanceUnique
      (AssetTransferFiniteAccountingV2.accepted_distinct scalar) admitted.balanced).1
  have sourceAdmitted := TP.transfer_conservation_admitted structural accepted
  have supplies := (FT.accepted_accounting structural.balanceUnique accepted command.asset).2
  have postSupply :
      C.supplyAt (C.transferPost pre policy command) command.asset =
        (TP.transferConservation (transferSource pre)
          (FT.transition digest ctx (transferSource pre) command).post command).supplyPostAtoms := by
    simpa [C.supplyAt, C.transferPost, TP.transferConservation, transferSource] using
      (congrArg (fun rows => supplyFor (numericRows rows) command.asset) supplies).symm
  have completed := complete_conservation_admitted sourceAdmitted admitted.balanced postBalanced
    (preSupply := by rfl) (postSupply := postSupply)
  rw [transfer_completed_row_exact structural accepted] at completed
  exact completed

theorem transfer_accepted_fields {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {policy : T.Policy}
    {completePreRoot completePostRoot : RootId}
    (structural : FT.Structural (transferSource pre))
    (selected : FT.policyFor (transferSource pre) command.asset = some policy)
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    let completed := transferEffectPlan digest ctx pre command completePreRoot completePostRoot
    let source := TP.transferPlan digest ctx (transferSource pre) command
    let post := C.transferPost pre policy command
    completed.assetConservation = [transferCompletedConservation pre post command] ∧
      completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
      completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
      completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
      completed.externalOutboxEnqueue = source.externalOutboxEnqueue := by
  dsimp only
  have completed :
      transferEffectPlan digest ctx pre command completePreRoot completePostRoot =
        completePlan pre (C.transferPost pre policy command) completePreRoot completePostRoot
          (TP.transferPlan digest ctx (transferSource pre) command) := by
    simp only [transferEffectPlan, accepted, selected]
    rw [transfer_post_from_leaf_eq selected accepted]
  rw [completed]
  have sourceConservation :
      (TP.transferPlan digest ctx (transferSource pre) command).assetConservation =
        [TP.transferConservation (transferSource pre)
          (FT.transition digest ctx (transferSource pre) command).post command] := by
    simp only [TP.transferPlan, accepted, selected]
  have rowExact := transfer_completed_row_exact (policy := policy) structural accepted
  simp only [completePlan]
  rw [sourceConservation]
  simp [rowExact]

theorem managed_source_supply {pre : C.State} {asset : Asset}
    (selected : asset ∈ R.managedAssets pre) :
    supplyFor (numericRows (managedSource pre).supplies) asset = C.supplyAt pre asset := by
  change supplyFor (numericRows (Q.selectSupplies (R.managedAssets pre)
    pre.transferState.supplies)) asset = C.supplyAt pre asset
  rw [R.selected_supply_numeric_rows,
    H.supply_filter_lookup (R.managedAssets pre) (numericRows pre.transferState.supplies) asset selected]
  rfl

theorem recomposed_selected_supply {pre : C.State} {asset owner : String} {deltaAtoms : Int}
    (admitted : C.RowsRepresentable pre) (selected : asset ∈ R.managedAssets pre) :
    C.supplyAt (R.recomposedPost pre asset owner deltaAtoms) asset =
      C.supplyAt pre asset + deltaAtoms := by
  obtain ⟨policy, member, same⟩ := List.mem_map.mp selected
  have registered : asset ∈ pre.transferState.supplies.map V1SupplyRow.asset := by
    rw [← admitted.registryKeys, ← same]
    exact admitted.managedCovered policy member
  rw [R.recomposed_post_eq admitted selected]
  change supplyFor (numericRows (adjustComplete asset deltaAtoms
    pre.transferState.supplies)) asset = C.supplyAt pre asset + deltaAtoms
  rw [adjustComplete_lookup _ asset deltaAtoms admitted.supplyUnique registered asset]
  simp [C.supplyAt]

theorem managed_source_post_supply {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {policy : M.Policy}
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (selected : FM.policyFor (managedSource pre) command.asset = some policy)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    supplyFor (numericRows
        (FM.transition digest ctx (managedSource pre) command).post.supplies) command.asset =
      C.supplyAt (R.recomposedPost pre command.asset command.accountOwner
        (M.signedAmount command)) command.asset := by
  have policyShape := FM.policyFor_spec selected
  have selectedAsset : command.asset ∈ R.managedAssets pre :=
    List.mem_map.mpr ⟨policy, policyShape.1, policyShape.2⟩
  have sourcePre := managed_source_supply selectedAsset
  have sourceAccounting := (FM.accepted_accounting structural accepted command.asset).2
  calc
    supplyFor (numericRows
        (FM.transition digest ctx (managedSource pre) command).post.supplies) command.asset =
        supplyFor (numericRows (managedSource pre).supplies) command.asset +
          M.signedAmount command := by simpa using sourceAccounting
    _ = C.supplyAt pre command.asset + M.signedAmount command := by rw [sourcePre]
    _ = C.supplyAt (R.recomposedPost pre command.asset command.accountOwner
        (M.signedAmount command)) command.asset :=
      (recomposed_selected_supply admitted selectedAsset).symm

theorem managed_accepted_policy {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} (roots : M.RootModel)
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    ∃ policy, FM.policyFor (managedSource pre) command.asset = some policy ∧
      policy ∈ pre.managedPolicies ∧
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (C.managedView pre policy) command).verdict =
        .accepted := by
  obtain ⟨policy, selected, scalar, _⟩ := FM.accepted_selected_leaf roots structural accepted
  have member : policy ∈ pre.managedPolicies := (FM.policyFor_spec selected).1
  have scalarFiltered :
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (R.filteredView pre policy) command).verdict =
        .accepted := scalar
  rw [R.filtered_view_eq admitted member] at scalarFiltered
  exact ⟨policy, selected, member, scalarFiltered⟩

theorem managed_completed_row_exact {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {policy : M.Policy}
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (selected : FM.policyFor (managedSource pre) command.asset = some policy)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    completeConservationRow pre
        (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command))
        (MP.managedConservation (managedSource pre)
          (FM.transition digest ctx (managedSource pre) command).post command) =
      managedCompletedConservation pre
        (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)) command := by
  have policyShape := FM.policyFor_spec selected
  have selectedAsset : command.asset ∈ R.managedAssets pre :=
    List.mem_map.mpr ⟨policy, policyShape.1, policyShape.2⟩
  have sourcePre := managed_source_supply selectedAsset
  have sourcePost := managed_source_post_supply admitted structural selected accepted
  simp only [completeConservationRow, managedCompletedConservation, MP.managedConservation]
  rw [sourcePre, sourcePost]

theorem managed_accepted_conservation {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {policy : M.Policy}
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (commandAdmitted : M.CommandWellFormed command) (ownerToken : B.ValidToken command.accountOwner)
    (selected : FM.policyFor (managedSource pre) command.asset = some policy)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    AssetConservationAdmitted (managedCompletedConservation pre
      (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)) command) := by
  have policyShape := FM.policyFor_spec selected
  have selectedAsset : command.asset ∈ R.managedAssets pre :=
    List.mem_map.mpr ⟨policy, policyShape.1, policyShape.2⟩
  have registered : command.asset ∈ pre.transferState.supplies.map V1SupplyRow.asset := by
    rw [← admitted.registryKeys, ← policyShape.2]
    exact admitted.managedCovered policy policyShape.1
  have managedBalanced : C.PhysicalBalanced
      (C.managedPost pre command.asset command.accountOwner (M.signedAmount command)) :=
    (C.managed_physical_lift pre command.asset command.accountOwner (M.signedAmount command)
      admitted.balanceUnique admitted.supplyUnique registered admitted.balanced).1
  have postBalanced : C.PhysicalBalanced
      (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)) := by
    rw [R.recomposed_post_eq admitted selectedAsset]
    exact managedBalanced
  have sourceAdmitted := MP.managed_conservation_admitted structural commandAdmitted ownerToken accepted
  have sourcePre := managed_source_supply selectedAsset
  have sourcePost := managed_source_post_supply admitted structural selected accepted
  have completed := complete_conservation_admitted sourceAdmitted admitted.balanced postBalanced
    (preSupply := sourcePre.symm) (postSupply := sourcePost.symm)
  rw [managed_completed_row_exact admitted structural selected accepted] at completed
  exact completed

theorem managed_accepted_fields {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {policy : M.Policy}
    {completePreRoot completePostRoot : RootId}
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (selected : FM.policyFor (managedSource pre) command.asset = some policy)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    let completed := managedEffectPlan digest ctx pre command completePreRoot completePostRoot
    let source := MP.managedPlan digest ctx (managedSource pre) command
    let post := R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)
    completed.assetConservation = [managedCompletedConservation pre post command] ∧
      completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
      completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
      completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
      completed.externalOutboxEnqueue = source.externalOutboxEnqueue := by
  dsimp only
  have completed :
      managedEffectPlan digest ctx pre command completePreRoot completePostRoot =
        completePlan pre
          (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command))
          completePreRoot completePostRoot (MP.managedPlan digest ctx (managedSource pre) command) := by
    simp only [managedEffectPlan, accepted]
    rw [managed_post_from_leaf_eq accepted]
  rw [completed]
  have sourceConservation :
      (MP.managedPlan digest ctx (managedSource pre) command).assetConservation =
        [MP.managedConservation (managedSource pre)
          (FM.transition digest ctx (managedSource pre) command).post command] := by
    simp only [MP.managedPlan, accepted]
  have rowExact := managed_completed_row_exact admitted structural selected accepted
  simp only [completePlan]
  rw [sourceConservation]
  simp [rowExact]

theorem transfer_accepted_plan_admitted {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {policy : T.Policy}
    {completePreRoot completePostRoot : RootId} (roots : T.RootModel)
    (admitted : C.RowsRepresentable pre)
    (structural : FT.Structural (transferSource pre))
    (selected : FT.policyFor (transferSource pre) command.asset = some policy)
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    EffectPlanAdmitted
      (transferEffectPlan digest ctx pre command completePreRoot completePostRoot) := by
  have sourceAdmitted := TP.transfer_plan_admitted structural accepted
  have completedConservation :=
    transfer_accepted_conservation roots admitted structural selected accepted
  have rowExact := transfer_completed_row_exact (policy := policy) structural accepted
  have conservation : ∀ row ∈ (TP.transferPlan digest ctx (transferSource pre) command).assetConservation,
      AssetConservationAdmitted (completeConservationRow pre
        (C.transferPost pre policy command) row) := by
    intro row member
    simp only [TP.transferPlan, accepted, selected, List.mem_singleton] at member
    subst row
    rw [rowExact]
    exact completedConservation
  have oneLane :
      (TP.transferPlan digest ctx (transferSource pre) command).laneWrites.length = 1 := by
    simp [TP.transferPlan, accepted, selected]
  have transported := complete_plan_admission (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) sourceAdmitted conservation oneLane
  have completed :
      transferEffectPlan digest ctx pre command completePreRoot completePostRoot =
        completePlan pre (C.transferPost pre policy command) completePreRoot completePostRoot
          (TP.transferPlan digest ctx (transferSource pre) command) := by
    simp only [transferEffectPlan, accepted, selected]
    rw [transfer_post_from_leaf_eq selected accepted]
  rw [completed]
  exact transported

theorem managed_accepted_plan_admitted {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {policy : M.Policy}
    {completePreRoot completePostRoot : RootId}
    (admitted : C.RowsRepresentable pre) (structural : FM.Structural (managedSource pre))
    (commandAdmitted : M.CommandWellFormed command) (ownerToken : B.ValidToken command.accountOwner)
    (selected : FM.policyFor (managedSource pre) command.asset = some policy)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    EffectPlanAdmitted
      (managedEffectPlan digest ctx pre command completePreRoot completePostRoot) := by
  have sourceAdmitted := MP.managed_plan_admitted structural commandAdmitted ownerToken accepted
  have completedConservation := managed_accepted_conservation admitted structural commandAdmitted
    ownerToken selected accepted
  have rowExact := managed_completed_row_exact admitted structural selected accepted
  have conservation : ∀ row ∈ (MP.managedPlan digest ctx (managedSource pre) command).assetConservation,
      AssetConservationAdmitted (completeConservationRow pre
        (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command)) row) := by
    intro row member
    simp only [MP.managedPlan, accepted, List.mem_singleton] at member
    subst row
    rw [rowExact]
    exact completedConservation
  have oneLane :
      (MP.managedPlan digest ctx (managedSource pre) command).laneWrites.length = 1 := by
    simp [MP.managedPlan, accepted]
  have transported := complete_plan_admission (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) sourceAdmitted conservation oneLane
  have completed :
      managedEffectPlan digest ctx pre command completePreRoot completePostRoot =
        completePlan pre
          (R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command))
          completePreRoot completePostRoot (MP.managedPlan digest ctx (managedSource pre) command) := by
    simp only [managedEffectPlan, accepted]
    rw [managed_post_from_leaf_eq accepted]
  rw [completed]
  exact transported

/-- Actual finite transfer acceptance derives the selected policy, the scalar
accepted leaf, equality of the reconstructed finite post to the complete-state
post, conservation, plan admission, and every unchanged field. -/
theorem transfer_accepted_completion {digest : B.Bytes → String} {ctx : T.Context}
    {pre : C.State} {command : T.Command} {completePreRoot completePostRoot : RootId}
    (roots : T.RootModel) (admitted : C.RowsRepresentable pre)
    (structural : FT.Structural (transferSource pre))
    (accepted : (FT.transition digest ctx (transferSource pre) command).verdict = .accepted) :
    ∃ policy, FT.policyFor (transferSource pre) command.asset = some policy ∧
      policy ∈ pre.transferState.policies ∧
      (AssetTransferRefinementV2.transition roots ctx (C.transferView pre policy) command).verdict =
        .accepted ∧
      let leafPost := (FT.transition digest ctx (transferSource pre) command).post
      let post := transferPostFromLeaf pre leafPost
      let completed := transferEffectPlan digest ctx pre command completePreRoot completePostRoot
      let source := TP.transferPlan digest ctx (transferSource pre) command
      post = C.transferPost pre policy command ∧
        completed.assetConservation = [transferCompletedConservation pre post command] ∧
        AssetConservationAdmitted (transferCompletedConservation pre post command) ∧
        EffectPlanAdmitted completed ∧
        completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
        completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
        completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
        completed.externalOutboxEnqueue = source.externalOutboxEnqueue := by
  obtain ⟨policy, selected, member, scalar⟩ :=
    transfer_accepted_policy roots structural accepted
  refine ⟨policy, selected, member, scalar, ?_⟩
  dsimp only
  have postEq := transfer_post_from_leaf_eq selected accepted
  have fields := transfer_accepted_fields (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) structural selected accepted
  have conservation := transfer_accepted_conservation roots admitted structural selected accepted
  have planAdmitted := transfer_accepted_plan_admitted (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) roots admitted structural selected accepted
  refine ⟨postEq, ?_⟩
  rw [postEq]
  exact ⟨fields.1, conservation, planAdmitted, fields.2.1, fields.2.2.1,
    fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2⟩

/-- Actual finite managed acceptance derives the selected policy and scalar
leaf before proving that the merged finite post is the recomposed complete
state. No post invariant or completed-effect consistency is assumed. -/
theorem managed_accepted_completion {digest : B.Bytes → String} {ctx : M.Context}
    {pre : C.State} {command : M.Command} {completePreRoot completePostRoot : RootId}
    (roots : M.RootModel) (admitted : C.RowsRepresentable pre)
    (structural : FM.Structural (managedSource pre))
    (commandAdmitted : M.CommandWellFormed command) (ownerToken : B.ValidToken command.accountOwner)
    (accepted : (FM.transition digest ctx (managedSource pre) command).verdict = .accepted) :
    ∃ policy, FM.policyFor (managedSource pre) command.asset = some policy ∧
      policy ∈ pre.managedPolicies ∧
      (ManagedAssetLifecycleRefinementV2.transition roots ctx (C.managedView pre policy) command).verdict =
        .accepted ∧
      let leafPost := (FM.transition digest ctx (managedSource pre) command).post
      let post := managedPostFromLeaf pre leafPost
      let completed := managedEffectPlan digest ctx pre command completePreRoot completePostRoot
      let source := MP.managedPlan digest ctx (managedSource pre) command
      post = R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command) ∧
        completed.assetConservation = [managedCompletedConservation pre post command] ∧
        AssetConservationAdmitted (managedCompletedConservation pre post command) ∧
        EffectPlanAdmitted completed ∧
        completed.rows = source.rows ∧ completed.feeConservation = source.feeConservation ∧
        completed.laneWrites = [⟨.assetTransfer, completePreRoot, completePostRoot⟩] ∧
        completed.occurrenceConsumptions = source.occurrenceConsumptions ∧
        completed.externalOutboxEnqueue = source.externalOutboxEnqueue := by
  obtain ⟨policy, selected, member, scalar⟩ :=
    managed_accepted_policy roots admitted structural accepted
  refine ⟨policy, selected, member, scalar, ?_⟩
  dsimp only
  have postEq := managed_post_from_leaf_eq accepted
  have fields := managed_accepted_fields (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) admitted structural selected accepted
  have conservation := managed_accepted_conservation admitted structural commandAdmitted ownerToken
    selected accepted
  have planAdmitted := managed_accepted_plan_admitted (completePreRoot := completePreRoot)
    (completePostRoot := completePostRoot) admitted structural commandAdmitted ownerToken selected accepted
  refine ⟨postEq, ?_⟩
  rw [postEq]
  exact ⟨fields.1, conservation, planAdmitted, fields.2.1, fields.2.2.1,
    fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2⟩

end Proofs.AssetLaneCustodyEffectPlanV2
