namespace ExactProjectionControls
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetLaneCustodyRefinementV2 Proofs.AssetLaneCustodyTraceV2
abbrev State := Proofs.AssetLaneCustodyRefinementV2.State
namespace X
export Proofs.AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  managed_source_structural step_preserves_complete)
end X
namespace E
export Proofs.AssetLaneCustodyEffectPlanV2 (transferSource managedSource
  transferPostFromLeaf managedPostFromLeaf)
end E
namespace FM
export Proofs.ManagedAssetFiniteOutcomeV2 (State transition candidate accepted_iff
  accepted_post_effects candidate_resources_iff_source_capacity SourceCapacity)
end FM
namespace F
export Proofs.AssetLaneCustodyFiniteTraceV2 (step managed_accepted_actual_post
  transfer_accepted_actual_post)
end F
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn)
end C
namespace S
export Proofs.AssetTransferSparseTablesV1 (balanceWire)
end S
namespace A
export Proofs.ManagedAssetFiniteAccountingV2 (updateRows)
end A
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (issueCommandKind burnCommandKind occurrence contextFor)
end M
namespace FT
export Proofs.AssetTransferFiniteOutcomeV2 (State transition accepted_iff accepted_post_effects
  candidate candidateFor policyFor project Resources)
end FT
namespace EP
export Proofs.AssetLaneCustodyExactProjectionV2 (transfer_post_from_leaf_exact
  transfer_accepted_step_exact managed_accepted_post_exact managed_accepted_step_exact)
end EP
attribute [local instance] lexOrd
local instance token_decidable (value : String) :
    Decidable (Proofs.AssetLaneFiniteByteAccountingV2.ValidToken value) := by
  unfold Proofs.AssetLaneFiniteByteAccountingV2.ValidToken
  infer_instance
abbrev initial := StructuralControls.twoManaged

def afterManagedIssue : State :=
  { afterIssue with managedPolicies := initial.managedPolicies }

def expectedIssueLeaf : FM.State :=
  { moduleReleaseId := "release-v2"
    policies := initial.managedPolicies
    balances := [⟨"alice", "ORD", "accounts", 107⟩, ⟨"bob", "ORD", "accounts", 15⟩]
    supplies := [⟨"AUD", 0⟩, ⟨"ORD", 127⟩] }

set_option maxRecDepth 10000 in
theorem issue_accepted :
    (FM.transition FiniteControls.digest M.issueContext (E.managedSource initial)
      B.issue).verdict = .accepted := by
  apply (FM.accepted_iff _ _ _ _).2
  constructor
  · decide
  · have initialShape := X.managed_source_structural StructuralControls.two_managed_complete
    apply (FM.candidate_resources_iff_source_capacity initialShape.balanceUnique
      initialShape.supplyUnique (by decide)).2
    unfold FM.SourceCapacity
    decide

theorem issue_leaf_expected :
    (FM.transition FiniteControls.digest M.issueContext (E.managedSource initial)
      B.issue).post = expectedIssueLeaf := by
  rw [(FM.accepted_post_effects issue_accepted).1]
  have changedRows :
      A.updateRows (E.managedSource initial).balances "ORD" "alice" 7 =
      expectedIssueLeaf.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "ORD", "accounts", 107⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [expectedIssueLeaf, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  change Proofs.ManagedAssetFiniteOutcomeV2.State.mk (E.managedSource initial).moduleReleaseId
    (E.managedSource initial).policies
    (A.updateRows (E.managedSource initial).balances "ORD" "alice" 7) _ = expectedIssueLeaf
  rw [changedRows]
  decide

theorem full_issue_state_expected :
    F.step FiniteControls.digest initial (.managed M.issueContext B.issue) =
      afterManagedIssue := by
  obtain ⟨_, _, _, _, _, complete⟩ :=
    F.managed_accepted_actual_post StructuralControls.two_managed_complete.rows issue_accepted
  rw [complete]
  change managedPost initial "ORD" "alice" 7 = afterManagedIssue
  have rows : A.updateRows initial.transferState.balances "ORD" "alice" 7 =
      afterIssue.transferState.balances := issue_rows
  simp only [Proofs.AssetLaneCustodyRefinementV2.managedPost, rows]
  decide

theorem issue_input : X.ActionAdmission (.managed M.issueContext B.issue) :=
  StructuralControls.inputs_admitted (.managed M.issueContext B.issue) (by
    simp [FiniteControls.actions])

theorem issue_post_reprojected :
    E.managedSource (E.managedPostFromLeaf initial expectedIssueLeaf) = expectedIssueLeaf := by
  have exact := EP.managed_accepted_post_exact
    (pre := initial) (context := M.issueContext) (command := B.issue)
    StructuralControls.two_managed_complete issue_input issue_accepted
  simpa [issue_leaf_expected] using exact

def audIssue : M.Command :=
  { B.issue with asset := "AUD", commandBodyHash := "aud-issue-body" }

def audIssueContext : M.Context :=
  M.contextFor (M.occurrence M.issueCommandKind "aud-issue-body" "issuer"
    "issue-grant" "occ-aud-issue")

def afterAudIssue : State :=
  { initial with transferState := { initial.transferState with
      balances := [⟨"alice", "AUD", "accounts", 7⟩,
        ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩,
        ⟨"bob", "ORD", "accounts", 15⟩]
      supplies := [⟨"AUD", 7⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩] } }

def expectedAudIssueLeaf : FM.State :=
  { moduleReleaseId := "release-v2"
    policies := [{ Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy with asset := "AUD" },
      Proofs.ManagedAssetLifecycleRefinementV2.ordinaryPolicy]
    balances := [⟨"alice", "AUD", "accounts", 7⟩,
      ⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩]
    supplies := [⟨"AUD", 7⟩, ⟨"ORD", 120⟩] }

set_option maxRecDepth 10000 in
theorem aud_issue_accepted :
    (FM.transition FiniteControls.digest audIssueContext (E.managedSource initial)
      audIssue).verdict = .accepted := by
  apply (FM.accepted_iff _ _ _ _).2
  constructor
  · decide
  · have initialShape := X.managed_source_structural StructuralControls.two_managed_complete
    apply (FM.candidate_resources_iff_source_capacity initialShape.balanceUnique
      initialShape.supplyUnique (by decide)).2
    unfold FM.SourceCapacity
    decide

set_option maxRecDepth 10000 in
theorem aud_issue_leaf_expected :
    (FM.transition FiniteControls.digest audIssueContext (E.managedSource initial)
      audIssue).post = expectedAudIssueLeaf := by
  rw [(FM.accepted_post_effects aud_issue_accepted).1]
  have changedRows :
      A.updateRows (E.managedSource initial).balances "AUD" "alice" 7 =
      expectedAudIssueLeaf.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "AUD", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [expectedAudIssueLeaf, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  change Proofs.ManagedAssetFiniteOutcomeV2.State.mk (E.managedSource initial).moduleReleaseId
    (E.managedSource initial).policies
    (A.updateRows (E.managedSource initial).balances "AUD" "alice" 7) _ = expectedAudIssueLeaf
  rw [changedRows]
  decide

theorem aud_issue_state_expected :
    F.step FiniteControls.digest initial (.managed audIssueContext audIssue) =
      afterAudIssue := by
  obtain ⟨_, _, _, _, _, complete⟩ :=
    F.managed_accepted_actual_post StructuralControls.two_managed_rows aud_issue_accepted
  rw [complete]
  change Proofs.AssetLaneCustodyRefinementV2.managedPost initial "AUD" "alice" 7 =
    afterAudIssue
  have rows : A.updateRows initial.transferState.balances "AUD" "alice" 7 =
      afterAudIssue.transferState.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "AUD", "accounts", 7⟩,
        ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩,
        ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [afterAudIssue, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  simp only [Proofs.AssetLaneCustodyRefinementV2.managedPost, rows]
  decide

theorem aud_issue_input : X.ActionAdmission (.managed audIssueContext audIssue) := by
  simp only [X.ActionAdmission]
  refine ⟨?_, ?_⟩
  · exact ⟨by decide, rfl⟩
  · unfold Proofs.AssetLaneFiniteByteAccountingV2.ValidToken
    decide

theorem aud_issue_post_reprojected :
    E.managedSource (E.managedPostFromLeaf initial expectedAudIssueLeaf) =
      expectedAudIssueLeaf := by
  have exact := EP.managed_accepted_post_exact
    (pre := initial) (context := audIssueContext) (command := audIssue)
    StructuralControls.two_managed_complete aud_issue_input aud_issue_accepted
  simpa [aud_issue_leaf_expected] using exact

theorem afterAudIssue_complete : X.CompleteStructural afterAudIssue := by
  have complete := X.step_preserves_complete FiniteControls.digest
    StructuralControls.two_managed_complete aud_issue_input
  simpa [aud_issue_state_expected] using complete

def audBurn : M.Command :=
  { B.burn with asset := "AUD", commandBodyHash := "aud-burn-body" }

def audBurnContext : M.Context :=
  M.contextFor (M.occurrence M.burnCommandKind "aud-burn-body" "alice"
    "burn-grant" "occ-aud-burn")

def afterAudBurn : State :=
  { afterAudIssue with transferState := { afterAudIssue.transferState with
      balances := [⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩]
      supplies := [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩] } }

def expectedAudBurnLeaf : FM.State :=
  { moduleReleaseId := "release-v2"
    policies := expectedAudIssueLeaf.policies
    balances := [⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩]
    supplies := [⟨"AUD", 0⟩, ⟨"ORD", 120⟩] }

set_option maxRecDepth 10000 in
theorem aud_burn_accepted :
    (FM.transition FiniteControls.digest audBurnContext (E.managedSource afterAudIssue)
      audBurn).verdict = .accepted := by
  apply (FM.accepted_iff _ _ _ _).2
  constructor
  · decide
  · have initialShape := X.managed_source_structural afterAudIssue_complete
    apply (FM.candidate_resources_iff_source_capacity initialShape.balanceUnique
      initialShape.supplyUnique (by decide)).2
    unfold FM.SourceCapacity
    decide

set_option maxRecDepth 10000 in
theorem aud_burn_leaf_expected :
    (FM.transition FiniteControls.digest audBurnContext (E.managedSource afterAudIssue)
      audBurn).post = expectedAudBurnLeaf := by
  rw [(FM.accepted_post_effects aud_burn_accepted).1]
  have changedRows :
      A.updateRows (E.managedSource afterAudIssue).balances "AUD" "alice" (-7) =
      expectedAudBurnLeaf.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [expectedAudBurnLeaf, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  change Proofs.ManagedAssetFiniteOutcomeV2.State.mk
    (E.managedSource afterAudIssue).moduleReleaseId
    (E.managedSource afterAudIssue).policies
    (A.updateRows (E.managedSource afterAudIssue).balances "AUD" "alice" (-7)) _ =
      expectedAudBurnLeaf
  rw [changedRows]
  decide

theorem aud_burn_input : X.ActionAdmission (.managed audBurnContext audBurn) := by
  simp only [X.ActionAdmission]
  refine ⟨?_, ?_⟩
  · exact ⟨by decide, rfl⟩
  · unfold Proofs.AssetLaneFiniteByteAccountingV2.ValidToken
    decide

theorem aud_burn_state_expected :
    F.step FiniteControls.digest afterAudIssue (.managed audBurnContext audBurn) =
      afterAudBurn := by
  obtain ⟨_, _, _, _, _, complete⟩ :=
    F.managed_accepted_actual_post afterAudIssue_complete.rows aud_burn_accepted
  rw [complete]
  change Proofs.AssetLaneCustodyRefinementV2.managedPost afterAudIssue "AUD" "alice" (-7) =
    afterAudBurn
  have rows : A.updateRows afterAudIssue.transferState.balances "AUD" "alice" (-7) =
      afterAudBurn.transferState.balances := by
    change C.sortOn S.balanceWire
      [⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [afterAudBurn, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  simp only [Proofs.AssetLaneCustodyRefinementV2.managedPost, rows]
  decide

theorem aud_burn_post_reprojected :
    E.managedSource (E.managedPostFromLeaf afterAudIssue expectedAudBurnLeaf) =
      expectedAudBurnLeaf := by
  have exact := EP.managed_accepted_post_exact
    (pre := afterAudIssue) (context := audBurnContext) (command := audBurn)
    afterAudIssue_complete aud_burn_input aud_burn_accepted
  simpa [aud_burn_leaf_expected] using exact

def afterInitialTransfer : State :=
  { initial with transferState := { initial.transferState with
      balances := [⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 88⟩,
        ⟨"bob", "ORD", "accounts", 25⟩,
        ⟨"m_treasury", "ORD", "accounts", 2⟩] } }

def expectedInitialTransferLeaf : FT.State :=
  { moduleReleaseId := "release-v2"
    policies := [{ B.policy with asset := "AUD" }, { B.policy with asset := "EUR" }, B.policy]
    balances := [⟨"dave", "EUR", "accounts", 7⟩,
      ⟨"alice", "ORD", "accounts", 88⟩,
      ⟨"bob", "ORD", "accounts", 25⟩,
      ⟨"m_treasury", "ORD", "accounts", 2⟩]
    supplies := [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩] }

theorem initial_transfer_rows :
    Proofs.AssetTransferFiniteAccountingV2.transferRows (transferView initial B.policy)
      B.transfer initial.transferState.balances = afterInitialTransfer.transferState.balances := by
  have feeRows :
      A.updateRows initial.transferState.balances "ORD" "m_treasury" 2 =
      [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 100⟩,
        ⟨"bob", "ORD", "accounts", 15⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] := by
    change C.sortOn S.balanceWire
      [⟨"m_treasury", "ORD", "accounts", 2⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  have recipientRows :
      A.updateRows
        [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 100⟩,
          ⟨"bob", "ORD", "accounts", 15⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩]
        "ORD" "bob" 10 =
      [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 100⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] := by
    change C.sortOn S.balanceWire
      [⟨"bob", "ORD", "accounts", 25⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 100⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] = _
    simp (disch := decide) [C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  have senderRows :
      A.updateRows
        [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 100⟩,
          ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩]
        "ORD" "alice" (-12) = afterInitialTransfer.transferState.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "ORD", "accounts", 88⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] = _
    simp (disch := decide) [afterInitialTransfer, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd,
      S.balanceWire]
  change A.updateRows
    (A.updateRows (A.updateRows initial.transferState.balances "ORD" "m_treasury" 2)
      "ORD" "bob" 10) "ORD" "alice" (-12) = _
  rw [feeRows, recipientRows, senderRows]

set_option maxRecDepth 10000 in
theorem initial_transfer_accepted :
    (FT.transition FiniteControls.digest (T.baseContext "alice")
      (E.transferSource initial) B.transfer).verdict = .accepted := by
  have selected : FT.policyFor (E.transferSource initial) B.transfer.asset = some B.policy := by
    decide
  apply (FT.accepted_iff _ _ _ _).2
  constructor
  · decide
  · unfold FT.Resources
    simp only [FT.candidate, selected, FT.candidateFor]
    have projection : FT.project (E.transferSource initial) B.policy =
        transferView initial B.policy := by rfl
    rw [projection]
    have sourceRows :
        Proofs.AssetTransferFiniteAccountingV2.transferRows (transferView initial B.policy)
            B.transfer (E.transferSource initial).balances =
          afterInitialTransfer.transferState.balances := by
      simpa only [E.transferSource] using initial_transfer_rows
    rw [sourceRows]
    decide

set_option maxRecDepth 10000 in
theorem initial_transfer_leaf_expected :
    (FT.transition FiniteControls.digest (T.baseContext "alice")
      (E.transferSource initial) B.transfer).post = expectedInitialTransferLeaf := by
  rw [(FT.accepted_post_effects initial_transfer_accepted).1]
  have selected : FT.policyFor (E.transferSource initial) B.transfer.asset = some B.policy := by
    decide
  simp only [FT.candidate, selected, FT.candidateFor]
  change {
      moduleReleaseId := initial.transferState.moduleReleaseId
      policies := initial.transferState.policies
      balances := Proofs.AssetTransferFiniteAccountingV2.transferRows
        (transferView initial B.policy) B.transfer initial.transferState.balances
      supplies := initial.transferState.supplies } = expectedInitialTransferLeaf
  rw [initial_transfer_rows]
  decide

theorem initial_transfer_state_expected :
    F.step FiniteControls.digest initial (.transfer (T.baseContext "alice") B.transfer) =
      afterInitialTransfer := by
  obtain ⟨policy, selected, _, _, complete⟩ :=
    F.transfer_accepted_actual_post initial_transfer_accepted
  have expected : FT.policyFor (E.transferSource initial) B.transfer.asset = some B.policy := by
    decide
  have same : policy = B.policy := Option.some.inj (selected.symm.trans expected)
  subst policy
  rw [complete]
  change Proofs.AssetLaneCustodyRefinementV2.transferPost initial B.policy B.transfer =
    afterInitialTransfer
  simp only [Proofs.AssetLaneCustodyRefinementV2.transferPost, initial_transfer_rows]
  rfl

theorem initial_transfer_post_reprojected :
    E.transferSource (E.transferPostFromLeaf initial expectedInitialTransferLeaf) =
      expectedInitialTransferLeaf := by
  exact EP.transfer_post_from_leaf_exact initial expectedInitialTransferLeaf

theorem initial_transfer_step_reprojected :
    E.transferSource (F.step FiniteControls.digest initial
      (.transfer (T.baseContext "alice") B.transfer)) =
      expectedInitialTransferLeaf := by
  have exact := EP.transfer_accepted_step_exact
    (pre := initial) (context := T.baseContext "alice") (command := B.transfer)
    initial_transfer_accepted
  simpa [initial_transfer_leaf_expected] using exact
end ExactProjectionControls
