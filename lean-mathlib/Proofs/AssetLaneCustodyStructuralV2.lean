import Proofs.AssetLaneCustodyFiniteTraceV2

/-!
# Structural closure for mixed custody traces

`CompleteStructural` records the complete-state row admission plus the ordering
and printable-token facts needed by both finite leaf projections. Transfer
policy keys and their order are derived from the complete supply/registry key
equalities. Managed policy order is explicit because row admission only says
that managed policies are covered by the registry.

The preservation results cover the modeled finite leaf step and its mixed
history runner. They do not establish resource, metadata, byte, root, receipt,
outer coordinator, runtime or publication admission.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyStructuralV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace C
export AssetLaneCustodyRefinementV2 (State RowsRepresentable)
end C
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource)
end E
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action CommandShape StaticPolicyShape FixedFrame
  step run)
end F
namespace FT
export AssetTransferFiniteOutcomeV2 (Structural CommandAdmission Verdict transition
  accepted_iff economic_candidate_structural accepted_post_effects)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (Structural transition policyFor_spec updateRows_ordered)
end FM
namespace T
export AssetTransferRefinementV2 (Command Context)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Command Context CommandWellFormed)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes ValidToken BalanceTokens SupplyTokens
  updateRows_tokens adjustComplete_tokens)
end B
namespace S
export AssetTransferSparseTablesV1 (balanceWire)
end S
namespace Trace
export AssetLaneCustodyTraceV2 (account_bounds)
end Trace
namespace H
export AssetLaneSharedProjectionV2 (selectRows selectRows_unique selectRows_total)
end H
namespace Q
export AssetLaneFiniteRecompositionV2 (selectSupplies)
end Q
namespace R
export AssetLaneCustodyRecompositionV2 (managedAssets selected_supply_numeric_rows)
end R

attribute [local instance] lexOrd

/-- Complete-state fields sufficient to construct both leaf `Structural`
predicates. This predicate deliberately excludes metadata and resource bounds. -/
structure CompleteStructural (pre : C.State) : Prop where
  rows : C.RowsRepresentable pre
  policyShape : F.StaticPolicyShape pre
  managedPolicyOrdered :
    pre.managedPolicies.Pairwise (fun left right => left.asset < right.asset)
  balanceOrdered : pre.transferState.balances.Pairwise
    (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt)
  transferFeeOwnerTokens : ∀ policy ∈ pre.transferState.policies,
    B.ValidToken policy.feeOwner
  balanceTokens : B.BalanceTokens pre.transferState.balances
  supplyTokens : B.SupplyTokens pre.transferState.supplies

/-- Per-action input shape needed by the corresponding structural candidate
theorem. It carries no selected policy or outcome premise. -/
def ActionAdmission : F.Action → Prop
  | .transfer _ command => FT.CommandAdmission command
  | .managed _ command => M.CommandWellFormed command ∧ B.ValidToken command.accountOwner

private theorem transfer_policy_ordered {pre : C.State}
    (admitted : C.RowsRepresentable pre) :
    pre.transferState.policies.Pairwise (fun left right => left.asset < right.asset) := by
  apply List.pairwise_map.mp
  rw [admitted.policyKeys, admitted.registryKeys]
  exact admitted.supplyOrdered

/-- The full transfer projection is structurally admitted by one complete-state
predicate; no selected transfer policy is an input. -/
theorem transfer_source_structural {pre : C.State} (admitted : CompleteStructural pre) :
    FT.Structural (E.transferSource pre) := by
  unfold E.transferSource
  constructor
  · change (pre.transferState.policies.map (fun policy => policy.asset)).Nodup
    rw [admitted.rows.policyKeys, admitted.rows.registryKeys]
    exact admitted.rows.supplyUnique
  · exact transfer_policy_ordered admitted.rows
  · intro policy member
    exact (admitted.policyShape.1 policy member).1
  · exact fun policy member => (admitted.policyShape.1 policy member).2
  · exact admitted.transferFeeOwnerTokens
  · exact admitted.rows.balanceUnique
  · exact admitted.rows.balancePositive
  · exact admitted.balanceOrdered
  · intro row member
    rw [admitted.rows.policyKeys]
    exact admitted.rows.holdingsCovered row (List.mem_append_left _ member)
  · exact admitted.rows.supplyUnique
  · exact admitted.rows.supplyOrdered
  · exact admitted.rows.supplyBounded
  · exact admitted.rows.registryKeys.symm.trans admitted.rows.policyKeys.symm
  · intro asset
    exact (Trace.account_bounds admitted.rows asset).2.1
  · exact admitted.balanceTokens
  · exact admitted.supplyTokens

private theorem managed_policy_unique {pre : C.State} (admitted : CompleteStructural pre) :
    (pre.managedPolicies.map (fun policy => policy.asset)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact admitted.managedPolicyOrdered.imp (fun ordered => String.ne_of_lt ordered)

private theorem selected_supply_unique {pre : C.State}
    (admitted : C.RowsRepresentable pre) :
    SourceAssetKeysUnique
      (Q.selectSupplies (R.managedAssets pre) pre.transferState.supplies) := by
  unfold SourceAssetKeysUnique Q.selectSupplies
  exact (List.filter_sublist.map V1SupplyRow.asset).nodup admitted.supplyUnique

private theorem selected_supply_ordered {pre : C.State}
    (admitted : C.RowsRepresentable pre) :
    SourceAssetKeysOrdered
      (Q.selectSupplies (R.managedAssets pre) pre.transferState.supplies) := by
  unfold SourceAssetKeysOrdered Q.selectSupplies
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp admitted.supplyOrdered).filter _

private theorem selected_supply_key_mem_iff {pre : C.State}
    (admitted : C.RowsRepresentable pre) (asset : Asset) :
    asset ∈ (Q.selectSupplies (R.managedAssets pre)
      pre.transferState.supplies).map V1SupplyRow.asset ↔
      asset ∈ R.managedAssets pre := by
  constructor
  · intro member
    obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
    have retained := of_decide_eq_true (List.mem_filter.mp rowMember).2
    exact same ▸ retained
  · intro selected
    obtain ⟨policy, policyMember, policyAsset⟩ := List.mem_map.mp selected
    have registry : policy.asset ∈ pre.originRegistry :=
      admitted.managedCovered policy policyMember
    rw [admitted.registryKeys] at registry
    obtain ⟨row, rowMember, rowAsset⟩ := List.mem_map.mp registry
    have exactAsset : row.asset = asset := rowAsset.trans policyAsset
    refine List.mem_map.mpr ⟨row, ?_, exactAsset⟩
    apply List.mem_filter.mpr
    exact ⟨rowMember, by
      apply decide_eq_true
      simpa only [exactAsset] using selected⟩

private theorem selected_supply_keys {pre : C.State} (admitted : CompleteStructural pre) :
    (Q.selectSupplies (R.managedAssets pre)
      pre.transferState.supplies).map V1SupplyRow.asset =
      pre.managedPolicies.map (fun policy => policy.asset) := by
  let selectedKeys := (Q.selectSupplies (R.managedAssets pre)
    pre.transferState.supplies).map V1SupplyRow.asset
  let managedKeys := pre.managedPolicies.map (fun policy => policy.asset)
  have selectedUnique : selectedKeys.Nodup := selected_supply_unique admitted.rows
  have managedUnique : managedKeys.Nodup := managed_policy_unique admitted
  have sameMembers : ∀ asset, asset ∈ selectedKeys ↔ asset ∈ managedKeys := by
    intro asset
    exact selected_supply_key_mem_iff admitted.rows asset
  have perm : selectedKeys.Perm managedKeys := by
    apply List.perm_iff_count.mpr
    intro asset
    rw [selectedUnique.count, managedUnique.count]
    by_cases selected : asset ∈ selectedKeys
    · rw [if_pos selected, if_pos ((sameMembers asset).mp selected)]
    · rw [if_neg selected, if_neg (fun member => selected ((sameMembers asset).mpr member))]
  change selectedKeys = managedKeys
  apply List.Perm.eq_of_pairwise (le := fun left right : Asset => left < right)
  · intro left right _ _ leftRight rightLeft
    exact False.elim (String.lt_asymm leftRight rightLeft)
  · exact selected_supply_ordered admitted.rows
  · exact List.pairwise_map.mpr admitted.managedPolicyOrdered
  · exact perm

private theorem selected_balance_zero {assets : List Asset} {rows : List AmountRow}
    {asset : Asset} (absent : asset ∉ assets) :
    amountForAsset (H.selectRows assets rows) asset = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases retained : row.asset ∈ assets
      · have different : row.asset ≠ asset := fun same => absent (same ▸ retained)
        simp only [H.selectRows, List.filter_cons, decide_eq_true retained, if_true,
          amountForAsset, List.map_cons, List.sum_cons, if_neg different, Int.zero_add]
        exact ih
      · simp only [H.selectRows, List.filter_cons, decide_eq_false retained,
          Bool.false_eq_true, if_false]
        exact ih

private theorem selected_account_cover {pre : C.State} (admitted : CompleteStructural pre)
    (asset : Asset) :
    amountForAsset (H.selectRows (R.managedAssets pre) pre.transferState.balances) asset ≤
      supplyFor (numericRows (Q.selectSupplies (R.managedAssets pre)
        pre.transferState.supplies)) asset := by
  by_cases selected : asset ∈ R.managedAssets pre
  · rw [H.selectRows_total _ _ asset selected, R.selected_supply_numeric_rows,
      AssetLaneSharedProjectionV2.supply_filter_lookup _ _ asset selected]
    exact (Trace.account_bounds admitted.rows asset).2.1
  · have supplyZero : supplyFor (numericRows (Q.selectSupplies (R.managedAssets pre)
        pre.transferState.supplies)) asset = 0 := by
      rw [supplyFor_numericRows_preserved]
      apply source_supplyFor_zero_of_absent
      intro row member same
      apply selected
      have retained := of_decide_eq_true (List.mem_filter.mp member).2
      exact same ▸ retained
    rw [selected_balance_zero selected, supplyZero]
    exact Int.le_refl 0

/-- The managed projection retains every declared managed sibling in strict
policy order, including dormant zero-supply assets. -/
theorem managed_source_structural {pre : C.State} (admitted : CompleteStructural pre) :
    FM.Structural (E.managedSource pre) := by
  unfold E.managedSource
  constructor
  · exact managed_policy_unique admitted
  · exact admitted.managedPolicyOrdered
  · exact admitted.policyShape.2
  · exact H.selectRows_unique _ _ admitted.rows.balanceUnique
  · intro row member
    exact admitted.rows.balancePositive row (List.mem_filter.mp member).1
  · exact admitted.balanceOrdered.filter _
  · intro row member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · exact selected_supply_unique admitted.rows
  · exact selected_supply_ordered admitted.rows
  · intro row member
    exact admitted.rows.supplyBounded row (List.mem_filter.mp member).1
  · exact selected_supply_keys admitted
  · exact selected_account_cover admitted
  · intro row member
    exact admitted.balanceTokens row (List.mem_filter.mp member).1
  · intro row member
    exact admitted.supplyTokens row (List.mem_filter.mp member).1

private theorem command_shape_of_admission {action : F.Action}
    (admitted : ActionAdmission action) : F.CommandShape action := by
  cases action <;> exact admitted.1

private theorem policy_shape_of_frame {pre post : C.State}
    (shape : F.StaticPolicyShape pre) (frame : F.FixedFrame pre post) :
    F.StaticPolicyShape post := by
  unfold F.StaticPolicyShape at shape ⊢
  rw [frame.2.1, frame.2.2.2.1]
  exact shape

private theorem transfer_fee_tokens_of_frame {pre post : C.State}
    (tokens : ∀ policy ∈ pre.transferState.policies, B.ValidToken policy.feeOwner)
    (frame : F.FixedFrame pre post) :
    ∀ policy ∈ post.transferState.policies, B.ValidToken policy.feeOwner := by
  rw [frame.2.1]
  exact tokens

private theorem transfer_accepted_leaf_structural {digest : B.Bytes → String} {pre : C.State}
    {context : T.Context} {command : T.Command} (admitted : CompleteStructural pre)
    (commandAdmitted : FT.CommandAdmission command)
    (accepted : (FT.transition digest context (E.transferSource pre) command).verdict =
      .accepted) :
    FT.Structural (FT.transition digest context (E.transferSource pre) command).post := by
  have economic :=
    ((FT.accepted_iff digest context (E.transferSource pre) command).mp accepted).1
  rw [(FT.accepted_post_effects accepted).1]
  exact FT.economic_candidate_structural (transfer_source_structural admitted)
    commandAdmitted economic

/-- One actual finite step preserves the complete predicate. Rejected leaves
return the exact input; accepted leaves supply the computed successor rows. -/
theorem step_preserves_complete (digest : B.Bytes → String) {pre : C.State}
    {action : F.Action} (admitted : CompleteStructural pre)
    (input : ActionAdmission action) :
    CompleteStructural (F.step digest pre action) := by
  have commandShape := command_shape_of_admission input
  have rows := AssetLaneCustodyFiniteTraceV2.step_preserves_rows digest
    admitted.rows admitted.policyShape commandShape
  have frame := AssetLaneCustodyFiniteTraceV2.step_fixed_frame digest pre action
  cases action with
  | transfer context command =>
      cases verdict : (FT.transition digest context (E.transferSource pre) command).verdict with
      | rejected code => simpa [F.step, verdict] using admitted
      | accepted =>
          have leaf := transfer_accepted_leaf_structural admitted input verdict
          refine {
            rows := rows
            policyShape := policy_shape_of_frame admitted.policyShape frame
            managedPolicyOrdered := ?_
            balanceOrdered := ?_
            transferFeeOwnerTokens :=
              transfer_fee_tokens_of_frame admitted.transferFeeOwnerTokens frame
            balanceTokens := ?_
            supplyTokens := ?_ }
          · rw [frame.2.2.2.1]
            exact admitted.managedPolicyOrdered
          · simp only [F.step, verdict]
            exact leaf.balanceOrdered
          · simp only [F.step, verdict]
            exact leaf.balanceTokens
          · simp only [F.step, verdict]
            exact leaf.supplyTokens
  | managed context command =>
      cases verdict : (FM.transition digest context (E.managedSource pre) command).verdict with
      | rejected code => simpa [F.step, verdict] using admitted
      | accepted =>
          obtain ⟨policy, selected, policyMember, _, _, complete⟩ :=
            AssetLaneCustodyFiniteTraceV2.managed_accepted_actual_post admitted.rows verdict
          have positive := rows.balancePositive
          rw [complete] at positive
          have sameAsset := (FM.policyFor_spec selected).2
          have registered : command.asset ∈
              pre.transferState.supplies.map V1SupplyRow.asset := by
            rw [← admitted.rows.registryKeys, ← sameAsset]
            exact admitted.rows.managedCovered policy policyMember
          have assetToken : B.ValidToken command.asset := by
            obtain ⟨row, member, same⟩ := List.mem_map.mp registered
            exact same ▸ admitted.supplyTokens row member
          refine {
            rows := rows
            policyShape := policy_shape_of_frame admitted.policyShape frame
            managedPolicyOrdered := ?_
            balanceOrdered := ?_
            transferFeeOwnerTokens :=
              transfer_fee_tokens_of_frame admitted.transferFeeOwnerTokens frame
            balanceTokens := ?_
            supplyTokens := ?_ }
          · rw [frame.2.2.2.1]
            exact admitted.managedPolicyOrdered
          · rw [complete]
            exact FM.updateRows_ordered _ _ _ _ admitted.rows.balanceUnique positive
          · rw [complete]
            exact B.updateRows_tokens _ _ _ _ admitted.balanceTokens assetToken input.2
          · rw [complete]
            exact B.adjustComplete_tokens _ _ _ admitted.supplyTokens

/-- A mixed finite history needs the complete structural predicate only at its
initial state and action-local command/token admission. -/
theorem run_preserves_complete (digest : B.Bytes → String) (actions : List F.Action)
    {pre : C.State} (admitted : CompleteStructural pre)
    (inputs : ∀ action ∈ actions, ActionAdmission action) :
    CompleteStructural (F.run digest pre actions) := by
  induction actions generalizing pre with
  | nil => exact admitted
  | cons first rest ih =>
      apply ih (step_preserves_complete digest admitted (inputs first List.mem_cons_self))
      intro action member
      exact inputs action (List.mem_cons_of_mem first member)

/-- Every reached prefix retains complete structure, and therefore reconstructs
both leaf `Structural` predicates without a per-successor premise. -/
theorem every_prefix_complete_and_sources (digest : B.Bytes → String)
    (actions : List F.Action) {pre : C.State} (admitted : CompleteStructural pre)
    (inputs : ∀ action ∈ actions, ActionAdmission action) (length : Nat) :
    let post := F.run digest pre (actions.take length)
    CompleteStructural post ∧ FT.Structural (E.transferSource post) ∧
      FM.Structural (E.managedSource post) := by
  let post := F.run digest pre (actions.take length)
  have complete : CompleteStructural post := by
    apply run_preserves_complete digest _ admitted
    intro action member
    exact inputs action (List.mem_of_mem_take member)
  exact ⟨complete, transfer_source_structural complete,
    managed_source_structural complete⟩

end Proofs.AssetLaneCustodyStructuralV2
