import Proofs.AssetLaneCustodyTraceV2
set_option warningAsError true
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetLaneCustodyRefinementV2 Proofs.AssetLaneCustodyTraceV2
namespace B
export Proofs.AssetLaneCustodyRefinementV2.Controls (pre policy transfer issue burn burnContext roots)
end B
namespace T
export Proofs.AssetTransferRefinementV2 (baseContext transition Verdict RejectCode EffectEnvelope)
end T
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (issueContext ordinaryPolicy lifecycleRoots transition)
end M
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn)
end C
namespace S
export Proofs.AssetTransferSparseTablesV1 (balanceWire)
end S
namespace A
export Proofs.ManagedAssetFiniteAccountingV2 (updateRows)
end A
attribute [local instance] lexOrd

-- Expected tables are specified independently from the modeled row updates.
def afterIssue : State :=
  { B.pre with transferState := { B.pre.transferState with
      balances := [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 107⟩,
        ⟨"bob", "ORD", "accounts", 15⟩]
      supplies := [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 127⟩] } }

def afterTransfer : State :=
  { afterIssue with transferState := { afterIssue.transferState with
      balances := [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 95⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] } }

def afterBurn : State :=
  { afterTransfer with transferState := { afterTransfer.transferState with
      balances := [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 88⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩]
      supplies := [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩] } }

-- Equation rewriting avoids reduction through mergeSort's well-founded recursor.
theorem issue_rows :
    A.updateRows B.pre.transferState.balances "ORD" "alice" 7 =
      afterIssue.transferState.balances := by
  change C.sortOn S.balanceWire
    [⟨"alice", "ORD", "accounts", 107⟩, ⟨"dave", "EUR", "accounts", 7⟩,
      ⟨"bob", "ORD", "accounts", 15⟩] = _
  simp (disch := decide) [afterIssue, C.sortOn, List.mergeSort,
    List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd, S.balanceWire]

theorem transfer_rows :
    Proofs.AssetTransferFiniteAccountingV2.transferRows (transferView afterIssue B.policy)
      B.transfer afterIssue.transferState.balances = afterTransfer.transferState.balances := by
  have feeRows :
      A.updateRows afterIssue.transferState.balances "ORD" "m_treasury" 2 =
      [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 107⟩,
        ⟨"bob", "ORD", "accounts", 15⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] := by
    change C.sortOn S.balanceWire
      [⟨"m_treasury", "ORD", "accounts", 2⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 107⟩, ⟨"bob", "ORD", "accounts", 15⟩] = _
    simp (disch := decide) [C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd, S.balanceWire]
  have recipientRows :
      A.updateRows
        [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 107⟩,
          ⟨"bob", "ORD", "accounts", 15⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩]
        "ORD" "bob" 10 =
      [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 107⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] := by
    change C.sortOn S.balanceWire
      [⟨"bob", "ORD", "accounts", 25⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"alice", "ORD", "accounts", 107⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] = _
    simp (disch := decide) [C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd, S.balanceWire]
  have senderRows :
      A.updateRows
        [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 107⟩,
          ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩]
        "ORD" "alice" (-12) = afterTransfer.transferState.balances := by
    change C.sortOn S.balanceWire
      [⟨"alice", "ORD", "accounts", 95⟩, ⟨"dave", "EUR", "accounts", 7⟩,
        ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] = _
    simp (disch := decide) [afterTransfer, C.sortOn, List.mergeSort,
      List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd, S.balanceWire]
  change A.updateRows
    (A.updateRows (A.updateRows afterIssue.transferState.balances "ORD" "m_treasury" 2)
      "ORD" "bob" 10) "ORD" "alice" (-12) = _
  rw [feeRows, recipientRows, senderRows]

theorem burn_rows :
    A.updateRows afterTransfer.transferState.balances "ORD" "alice" (-7) =
      afterBurn.transferState.balances := by
  change C.sortOn S.balanceWire
    [⟨"alice", "ORD", "accounts", 88⟩, ⟨"dave", "EUR", "accounts", 7⟩,
      ⟨"bob", "ORD", "accounts", 25⟩, ⟨"m_treasury", "ORD", "accounts", 2⟩] = _
  simp (disch := decide) [afterBurn, C.sortOn, List.mergeSort,
    List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd, S.balanceWire]

theorem issue_result :
    managedStep M.lifecycleRoots M.issueContext B.pre M.ordinaryPolicy B.issue =
      (.accepted, afterIssue) := by
  have accepted : (M.transition M.lifecycleRoots M.issueContext
      (managedView B.pre M.ordinaryPolicy) B.issue).verdict = .accepted := by decide
  simp only [managedStep, accepted]
  change (Proofs.ManagedAssetLifecycleRefinementV2.Verdict.accepted,
    managedPost B.pre "ORD" "alice" 7) = _
  simp only [managedPost, issue_rows]
  decide

theorem transfer_result :
    transferStep B.roots (T.baseContext "alice") afterIssue B.policy B.transfer =
      (.accepted, afterTransfer) := by
  have accepted : (T.transition B.roots (T.baseContext "alice")
      (transferView afterIssue B.policy) B.transfer).verdict = .accepted := by decide
  simp only [transferStep, accepted, transferPost, transfer_rows]
  rfl

theorem unauthorized_leaf :
    (T.transition B.roots (T.baseContext "mallory")
      (transferView afterTransfer B.policy) B.transfer).verdict =
      .rejected .unauthorizedSubject := by decide

theorem unauthorized_result :
    transferStep B.roots (T.baseContext "mallory") afterTransfer B.policy B.transfer =
      (.rejected .unauthorizedSubject, afterTransfer) :=
  (rejected_transfer_noop unauthorized_leaf).1

theorem unauthorized_effects :
    (T.transition B.roots (T.baseContext "mallory")
      (transferView afterTransfer B.policy) B.transfer).effects =
        Proofs.AssetTransferRefinementV2.EffectEnvelope.empty :=
  (rejected_transfer_noop unauthorized_leaf).2

theorem burn_result :
    managedStep M.lifecycleRoots B.burnContext afterTransfer M.ordinaryPolicy B.burn =
      (.accepted, afterBurn) := by
  have accepted : (M.transition M.lifecycleRoots B.burnContext
      (managedView afterTransfer M.ordinaryPolicy) B.burn).verdict = .accepted := by decide
  simp only [managedStep, accepted]
  change (Proofs.ManagedAssetLifecycleRefinementV2.Verdict.accepted,
    managedPost afterTransfer "ORD" "alice" (-7)) = _
  simp only [managedPost, burn_rows]
  decide

def actions : List Action := [
  .managed M.issueContext M.ordinaryPolicy B.issue,
  .transfer (T.baseContext "alice") B.policy B.transfer,
  .transfer (T.baseContext "mallory") B.policy B.transfer,
  .managed B.burnContext M.ordinaryPolicy B.burn]

theorem inputs_ready : ∀ action ∈ actions, Ready B.pre action := by
  intro action member
  simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨by decide, ⟨rfl, ?_⟩, ⟨?_, rfl⟩⟩
    · intro excluded; exact False.elim (excluded rfl)
    · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, ⟨by decide, by decide⟩, rfl,
      ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩
  · exact ⟨by decide, ⟨by decide, by decide⟩, rfl,
      ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩
  · refine ⟨by decide, ⟨rfl, ?_⟩, ⟨?_, rfl⟩⟩
    · intro excluded; exact False.elim (excluded rfl)
    · exact ⟨by decide, by decide⟩

theorem history_rows : RowsRepresentable (run B.roots M.lifecycleRoots B.pre actions) :=
  run_preserves_rows B.roots M.lifecycleRoots actions Controls.legal_custody_state_representable inputs_ready

theorem exact_history : run B.roots M.lifecycleRoots B.pre actions = afterBurn := by
  simp only [actions, run, step, issue_result, transfer_result, unauthorized_result, burn_result]

theorem history_changed_accounts : run B.roots M.lifecycleRoots B.pre actions ≠ B.pre := by
  rw [exact_history]
  decide

theorem prefix_rows (length : Nat) :
    RowsRepresentable (run B.roots M.lifecycleRoots B.pre (actions.take length)) :=
  every_prefix_preserves_rows B.roots M.lifecycleRoots actions
    Controls.legal_custody_state_representable inputs_ready length

theorem physical_totals :
    physicalFor afterIssue "ORD" = 127 ∧ physicalFor afterTransfer "ORD" = 127 ∧
      physicalFor (run B.roots M.lifecycleRoots B.pre actions) "ORD" = 120 := by
  rw [exact_history]
  decide

theorem history_custody : (run B.roots M.lifecycleRoots B.pre actions).custody = B.pre.custody :=
  (run_fixed_frame B.roots M.lifecycleRoots actions B.pre).2.2.2.2

theorem history_registered_support :
    (run B.roots M.lifecycleRoots B.pre actions).transferState.supplies =
      [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩] ∧
    (run B.roots M.lifecycleRoots B.pre actions).originRegistry = ["AUD", "EUR", "ORD"] := by
  rw [exact_history]
  decide

#print axioms exact_history
#print axioms history_rows
#print axioms unauthorized_effects
