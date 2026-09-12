namespace FiniteControls

namespace F
export Proofs.AssetLaneCustodyFiniteTraceV2 (Action CommandShape StaticPolicyShape FixedFrame
  step run transfer_rejected_noop managed_rejected_noop transfer_accepted_actual_post
  managed_accepted_actual_post step_preserves_rows every_prefix_rows_and_frame)
end F
namespace E
export Proofs.AssetLaneCustodyEffectPlanV2 (transferSource managedSource)
end E
namespace FT
export Proofs.AssetTransferFiniteOutcomeV2 (RejectCode Verdict Resources accepted_iff candidate
  candidateFor policyFor transition)
end FT
namespace FM
export Proofs.ManagedAssetFiniteOutcomeV2 (RejectCode Verdict SourceCapacity accepted_iff
  candidate_resources_iff_source_capacity transition)
end FM

def digest : Proofs.AssetLaneFiniteByteAccountingV2.Bytes → String := fun _ => "finite-control-root"

def unknownTransfer : Proofs.AssetTransferRefinementV2.Command :=
  { B.transfer with asset := "ZZZ" }

def unknownManaged : Proofs.ManagedAssetLifecycleRefinementV2.Command :=
  { B.issue with asset := "ZZZ" }

def actions : List F.Action := [
  .managed M.issueContext B.issue,
  .transfer (T.baseContext "alice") B.transfer,
  .transfer (T.baseContext "alice") unknownTransfer,
  .managed M.issueContext unknownManaged,
  .transfer (T.baseContext "mallory") B.transfer,
  .managed B.burnContext B.burn]

theorem static_policies : F.StaticPolicyShape B.pre := by
  constructor
  · intro policy member
    simp only [B.pre, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact ⟨⟨by decide, by decide⟩, rfl⟩
  · intro policy member
    simp only [B.pre, List.mem_singleton] at member
    subst policy
    exact ⟨rfl, fun excluded => False.elim (excluded rfl)⟩

theorem input_command_shapes : ∀ action ∈ actions, F.CommandShape action := by
  intro action member
  simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [F.CommandShape, unknownTransfer, unknownManaged]
  all_goals constructor <;> decide

private theorem managed_source_balance_unique {pre : State} (admitted : RowsRepresentable pre) :
    Proofs.AssetTransferSparseTablesV1.Unique (E.managedSource pre).balances := by
  simpa [E.managedSource] using
    Proofs.AssetLaneSharedProjectionV2.selectRows_unique
      (Proofs.AssetLaneCustodyRecompositionV2.managedAssets pre)
      pre.transferState.balances admitted.balanceUnique

private theorem managed_source_supply_unique {pre : State} (admitted : RowsRepresentable pre) :
    Proofs.RegisteredSupplySupportV1.SourceAssetKeysUnique (E.managedSource pre).supplies := by
  change Proofs.RegisteredSupplySupportV1.SourceAssetKeysUnique
    (Proofs.AssetLaneFiniteRecompositionV2.selectSupplies
      (Proofs.AssetLaneCustodyRecompositionV2.managedAssets pre) pre.transferState.supplies)
  unfold Proofs.AssetLaneFiniteRecompositionV2.selectSupplies
    Proofs.RegisteredSupplySupportV1.SourceAssetKeysUnique
  have subset :
      (pre.transferState.supplies.filter (fun row =>
        decide (row.asset ∈ Proofs.AssetLaneCustodyRecompositionV2.managedAssets pre))).Sublist
        pre.transferState.supplies := List.filter_sublist
  exact (subset.map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset).nodup
    admitted.supplyUnique

set_option maxRecDepth 10000 in
theorem issue_accepted :
    (FM.transition digest M.issueContext (E.managedSource B.pre) B.issue).verdict = .accepted := by
  apply (FM.accepted_iff digest M.issueContext (E.managedSource B.pre) B.issue).2
  constructor
  · decide
  · apply (FM.candidate_resources_iff_source_capacity
      (pre := E.managedSource B.pre) (command := B.issue)
      (managed_source_balance_unique
        Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable)
      (managed_source_supply_unique
        Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable)
      (by decide)).2
    unfold FM.SourceCapacity
    decide

theorem transfer_candidate :
    FT.candidate (E.transferSource afterIssue) B.transfer = E.transferSource afterTransfer := by
  have projection :
      Proofs.AssetTransferFiniteOutcomeV2.project (E.transferSource afterIssue) B.policy =
        transferView afterIssue B.policy := rfl
  have selected : FT.policyFor (E.transferSource afterIssue) B.transfer.asset = some B.policy := by decide
  simp only [FT.candidate, selected]
  unfold FT.candidateFor
  rw [projection]
  simp only [E.transferSource]
  rw [transfer_rows]
  rfl

set_option maxRecDepth 10000 in
theorem transfer_accepted :
    (FT.transition digest (T.baseContext "alice") (E.transferSource afterIssue)
      B.transfer).verdict = .accepted := by
  apply (FT.accepted_iff digest (T.baseContext "alice") (E.transferSource afterIssue) B.transfer).2
  constructor
  · decide
  · rw [transfer_candidate]
    unfold FT.Resources
    decide

theorem unknown_transfer_rejected :
    (FT.transition digest (T.baseContext "alice") (E.transferSource afterTransfer)
      unknownTransfer).verdict = .rejected (.economic .unknownAsset) := by
  decide

theorem unknown_managed_rejected :
    (FM.transition digest M.issueContext (E.managedSource afterTransfer)
      unknownManaged).verdict = .rejected (.economic .unknownAsset) := by
  decide

theorem unauthorized_transfer_rejected :
    (FT.transition digest (T.baseContext "mallory") (E.transferSource afterTransfer)
      B.transfer).verdict = .rejected (.economic .unauthorizedSubject) := by
  decide

theorem issue_step :
    F.step digest B.pre (.managed M.issueContext B.issue) = afterIssue := by
  obtain ⟨_, _, _, _, _, complete⟩ :=
    F.managed_accepted_actual_post
      Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable issue_accepted
  rw [complete]
  change managedPost B.pre "ORD" "alice" 7 = afterIssue
  simp only [Proofs.AssetLaneCustodyRefinementV2.managedPost, issue_rows]
  decide

theorem transfer_step :
    F.step digest afterIssue (.transfer (T.baseContext "alice") B.transfer) = afterTransfer := by
  obtain ⟨policy, selected, _, _, complete⟩ := F.transfer_accepted_actual_post transfer_accepted
  have expected : FT.policyFor (E.transferSource afterIssue) B.transfer.asset = some B.policy := by decide
  have same : policy = B.policy := Option.some.inj (selected.symm.trans expected)
  subst policy
  rw [complete]
  change transferPost afterIssue B.policy B.transfer = afterTransfer
  simp only [Proofs.AssetLaneCustodyRefinementV2.transferPost, transfer_rows]
  rfl

theorem unknown_transfer_noop :
    F.step digest afterTransfer (.transfer (T.baseContext "alice") unknownTransfer) = afterTransfer :=
  F.transfer_rejected_noop unknown_transfer_rejected

theorem unknown_managed_noop :
    F.step digest afterTransfer (.managed M.issueContext unknownManaged) = afterTransfer :=
  F.managed_rejected_noop unknown_managed_rejected

theorem unauthorized_transfer_noop :
    F.step digest afterTransfer (.transfer (T.baseContext "mallory") B.transfer) = afterTransfer :=
  F.transfer_rejected_noop unauthorized_transfer_rejected

theorem after_transfer_rows : RowsRepresentable afterTransfer := by
  have prefixRows := (F.every_prefix_rows_and_frame digest actions
    Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable
    static_policies input_command_shapes 2).1
  simpa [actions, F.run, issue_step, transfer_step] using prefixRows

set_option maxRecDepth 10000 in
theorem burn_accepted :
    (FM.transition digest B.burnContext (E.managedSource afterTransfer) B.burn).verdict = .accepted := by
  apply (FM.accepted_iff digest B.burnContext (E.managedSource afterTransfer) B.burn).2
  constructor
  · decide
  · apply (FM.candidate_resources_iff_source_capacity
      (pre := E.managedSource afterTransfer) (command := B.burn)
      (managed_source_balance_unique after_transfer_rows)
      (managed_source_supply_unique after_transfer_rows) (by decide)).2
    unfold FM.SourceCapacity
    decide

theorem burn_step :
    F.step digest afterTransfer (.managed B.burnContext B.burn) = afterBurn := by
  obtain ⟨_, _, _, _, _, complete⟩ :=
    F.managed_accepted_actual_post after_transfer_rows burn_accepted
  rw [complete]
  change managedPost afterTransfer "ORD" "alice" (-7) = afterBurn
  simp only [Proofs.AssetLaneCustodyRefinementV2.managedPost, burn_rows]
  decide

theorem exact_history : F.run digest B.pre actions = afterBurn := by
  simp only [actions, F.run, issue_step, transfer_step, unknown_transfer_noop,
    unknown_managed_noop, unauthorized_transfer_noop, burn_step]

theorem every_prefix (length : Nat) :
    RowsRepresentable (F.run digest B.pre (actions.take length)) ∧
      F.FixedFrame B.pre (F.run digest B.pre (actions.take length)) :=
  F.every_prefix_rows_and_frame digest actions
    Proofs.AssetLaneCustodyRefinementV2.Controls.legal_custody_state_representable
    static_policies input_command_shapes length

end FiniteControls
