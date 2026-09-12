import Proofs.AssetLaneCustodyEffectPlanV2

/-!
# Mixed finite-outcome traces for the custody-capable asset lane

This file drives each step with the actual finite transfer or managed transition.
Rejection retains the exact complete input state. Acceptance materializes the
finite leaf post through the custody constructors and derives the existing
complete-row preservation theorem from the selected scalar policy.

One initial row-admission premise and immutable policy-shape premises suffice
for every reached prefix. Command shape is supplied only for actions in the
input history. The model excludes outer aggregate resource and binding checks,
metadata admission, bytes, roots, receipts and runtime or publication authority.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyFiniteTraceV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace C
export AssetLaneCustodyRefinementV2 (State RowsRepresentable transferPost managedPost
  transferView managedView)
end C
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource transferPostFromLeaf
  managedPostFromLeaf transfer_post_from_leaf_eq managed_post_from_leaf_eq)
end E
namespace R
export AssetLaneCustodyRecompositionV2 (managedAssets filteredView filtered_view_eq
  recomposedPost recomposed_post_eq)
end R
namespace Trace
export AssetLaneCustodyTraceV2 (transfer_preserves_rows managed_preserves_rows)
end Trace
namespace FT
export AssetTransferFiniteOutcomeV2 (RejectCode Verdict transition policyFor policyFor_spec
  project accepted_iff economic_none_iff_selected)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (RejectCode Verdict transition policyFor policyFor_spec
  project accepted_iff economic_none_iff_selected)
end FM
namespace T
export AssetTransferRefinementV2 (Context Command Policy CommandWellFormed IsU128
  accepted_iff_no_reject transition)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Context Command Policy CommandWellFormed
  PolicyWellFormed signedAmount accepted_iff_no_reject transition)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes)
end B

inductive Action where
  | transfer (context : T.Context) (command : T.Command)
  | managed (context : M.Context) (command : M.Command)

/-- Command shape belongs to the finite input history, independent of the
state reached before that action. -/
def CommandShape : Action → Prop
  | .transfer _ command => T.CommandWellFormed command
  | .managed _ command => M.CommandWellFormed command

/-- Shapes of every immutable policy that a finite transition may select. -/
def StaticPolicyShape (pre : C.State) : Prop :=
  (∀ policy ∈ pre.transferState.policies,
      T.IsU128 policy.transferFeeAtoms ∧ policy.atomDecimals = 8) ∧
    (∀ policy ∈ pre.managedPolicies, M.PolicyWellFormed policy)

/-- The complete immutable custody frame observed by this state model. -/
def FixedFrame (pre post : C.State) : Prop :=
  post.transferState.moduleReleaseId = pre.transferState.moduleReleaseId ∧
    post.transferState.policies = pre.transferState.policies ∧
    post.originRegistry = pre.originRegistry ∧
    post.managedPolicies = pre.managedPolicies ∧
    post.custody = pre.custody

/-- Execute the actual finite leaf and embed only its accepted post. -/
def step (digest : B.Bytes → String) (pre : C.State) : Action → C.State
  | .transfer context command =>
      let result := FT.transition digest context (E.transferSource pre) command
      match result.verdict with
      | .accepted => E.transferPostFromLeaf pre result.post
      | .rejected _ => pre
  | .managed context command =>
      let result := FM.transition digest context (E.managedSource pre) command
      match result.verdict with
      | .accepted => E.managedPostFromLeaf pre result.post
      | .rejected _ => pre

theorem transfer_rejected_noop {digest : B.Bytes → String} {pre : C.State}
    {context : T.Context} {command : T.Command} {code : FT.RejectCode}
    (rejected :
      (FT.transition digest context (E.transferSource pre) command).verdict = .rejected code) :
    step digest pre (.transfer context command) = pre := by
  simp [step, rejected]

theorem managed_rejected_noop {digest : B.Bytes → String} {pre : C.State}
    {context : M.Context} {command : M.Command} {code : FM.RejectCode}
    (rejected :
      (FM.transition digest context (E.managedSource pre) command).verdict = .rejected code) :
    step digest pre (.managed context command) = pre := by
  simp [step, rejected]

/-- Finite transfer acceptance selects the actual policy and materializes the
whole accepted leaf post in the complete custody frame. -/
theorem transfer_accepted_actual_post {digest : B.Bytes → String} {pre : C.State}
    {context : T.Context} {command : T.Command}
    (accepted :
      (FT.transition digest context (E.transferSource pre) command).verdict = .accepted) :
    ∃ policy, FT.policyFor (E.transferSource pre) command.asset = some policy ∧
      policy ∈ pre.transferState.policies ∧
      step digest pre (.transfer context command) =
        E.transferPostFromLeaf pre
          (FT.transition digest context (E.transferSource pre) command).post ∧
      step digest pre (.transfer context command) = C.transferPost pre policy command := by
  have economic :=
    ((FT.accepted_iff digest context (E.transferSource pre) command).mp accepted).1
  obtain ⟨policy, selected, _⟩ :=
    (FT.economic_none_iff_selected context (E.transferSource pre) command).mp economic
  have member : policy ∈ pre.transferState.policies := (FT.policyFor_spec selected).1
  have actual : step digest pre (.transfer context command) =
      E.transferPostFromLeaf pre
        (FT.transition digest context (E.transferSource pre) command).post := by
    simp [step, accepted]
  have complete : step digest pre (.transfer context command) =
      C.transferPost pre policy command := by
    simp only [step, accepted]
    exact E.transfer_post_from_leaf_eq selected accepted
  exact ⟨policy, selected, member, actual, complete⟩

/-- Managed acceptance selects an immutable managed policy, embeds the actual
finite post, and preserves every unrelated complete row through recomposition. -/
theorem managed_accepted_actual_post {digest : B.Bytes → String} {pre : C.State}
    {context : M.Context} {command : M.Command} (admitted : C.RowsRepresentable pre)
    (accepted :
      (FM.transition digest context (E.managedSource pre) command).verdict = .accepted) :
    ∃ policy, FM.policyFor (E.managedSource pre) command.asset = some policy ∧
      policy ∈ pre.managedPolicies ∧
      step digest pre (.managed context command) =
        E.managedPostFromLeaf pre
          (FM.transition digest context (E.managedSource pre) command).post ∧
      step digest pre (.managed context command) =
        R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command) ∧
      step digest pre (.managed context command) =
        C.managedPost pre command.asset command.accountOwner (M.signedAmount command) := by
  have economic :=
    ((FM.accepted_iff digest context (E.managedSource pre) command).mp accepted).1
  obtain ⟨policy, selected, _⟩ :=
    (FM.economic_none_iff_selected context (E.managedSource pre) command).mp economic
  have policySpec := FM.policyFor_spec selected
  have member : policy ∈ pre.managedPolicies := policySpec.1
  have selectedAsset : command.asset ∈ R.managedAssets pre :=
    List.mem_map.mpr ⟨policy, member, policySpec.2⟩
  have actual : step digest pre (.managed context command) =
      E.managedPostFromLeaf pre
        (FM.transition digest context (E.managedSource pre) command).post := by
    simp [step, accepted]
  have recomposed : step digest pre (.managed context command) =
      R.recomposedPost pre command.asset command.accountOwner (M.signedAmount command) := by
    simp only [step, accepted]
    exact E.managed_post_from_leaf_eq accepted
  have complete : step digest pre (.managed context command) =
      C.managedPost pre command.asset command.accountOwner (M.signedAmount command) := by
    simp only [step, accepted]
    rw [E.managed_post_from_leaf_eq accepted, R.recomposed_post_eq admitted selectedAsset]
  exact ⟨policy, selected, member, actual, recomposed, complete⟩

private theorem static_policy_shape_of_frame {pre post : C.State}
    (shape : StaticPolicyShape pre) (frame : FixedFrame pre post) :
    StaticPolicyShape post := by
  unfold StaticPolicyShape at shape ⊢
  rw [frame.2.1, frame.2.2.2.1]
  exact shape

/-- Row admission is derived from the finite verdict. Accepted leaves supply
their selected scalar policy; rejected leaves retain the exact input. -/
theorem step_preserves_rows (digest : B.Bytes → String) {pre : C.State} {action : Action}
    (admitted : C.RowsRepresentable pre) (policies : StaticPolicyShape pre)
    (commandShape : CommandShape action) :
    C.RowsRepresentable (step digest pre action) := by
  cases action with
  | transfer context command =>
      cases verdict : (FT.transition digest context (E.transferSource pre) command).verdict with
      | rejected code => simpa [step, verdict] using admitted
      | accepted =>
          have economic :=
            ((FT.accepted_iff digest context (E.transferSource pre) command).mp verdict).1
          obtain ⟨policy, selected, scalarNone⟩ :=
            (FT.economic_none_iff_selected context (E.transferSource pre) command).mp economic
          have member : policy ∈ pre.transferState.policies := (FT.policyFor_spec selected).1
          have scalar :
              (T.transition ⟨fun _ => ""⟩ context (C.transferView pre policy) command).verdict =
                .accepted :=
            (T.accepted_iff_no_reject ⟨fun _ => ""⟩ context
              (FT.project (E.transferSource pre) policy) command).mpr scalarNone
          have rows := Trace.transfer_preserves_rows admitted member
            (policies.1 policy member).1 (policies.1 policy member).2 scalar
          simp only [step, verdict]
          rw [E.transfer_post_from_leaf_eq selected verdict]
          exact rows
  | managed context command =>
      cases verdict : (FM.transition digest context (E.managedSource pre) command).verdict with
      | rejected code => simpa [step, verdict] using admitted
      | accepted =>
          have economic :=
            ((FM.accepted_iff digest context (E.managedSource pre) command).mp verdict).1
          obtain ⟨policy, selected, scalarNone⟩ :=
            (FM.economic_none_iff_selected context (E.managedSource pre) command).mp economic
          have policySpec := FM.policyFor_spec selected
          have member : policy ∈ pre.managedPolicies := policySpec.1
          have selectedAsset : command.asset ∈ R.managedAssets pre :=
            List.mem_map.mpr ⟨policy, member, policySpec.2⟩
          have filtered :
              (M.transition ⟨fun _ => ""⟩ context (R.filteredView pre policy) command).verdict =
                .accepted :=
            (M.accepted_iff_no_reject ⟨fun _ => ""⟩ context
              (FM.project (E.managedSource pre) policy) command).mpr scalarNone
          have scalar :
              (M.transition ⟨fun _ => ""⟩ context (C.managedView pre policy) command).verdict =
                .accepted := by
            rw [← R.filtered_view_eq admitted member]
            exact filtered
          have rows := Trace.managed_preserves_rows admitted member (policies.2 policy member)
            commandShape scalar
          simp only [step, verdict]
          rw [E.managed_post_from_leaf_eq verdict, R.recomposed_post_eq admitted selectedAsset]
          exact rows

/-- One finite step preserves module selection, policy lists, registry, managed
policy list and the full custody rows. -/
theorem step_fixed_frame (digest : B.Bytes → String) (pre : C.State) (action : Action) :
    FixedFrame pre (step digest pre action) := by
  cases action with
  | transfer context command =>
      cases verdict : (FT.transition digest context (E.transferSource pre) command).verdict with
      | rejected code => simp [step, verdict, FixedFrame]
      | accepted =>
          have economic :=
            ((FT.accepted_iff digest context (E.transferSource pre) command).mp verdict).1
          obtain ⟨policy, selected, _⟩ :=
            (FT.economic_none_iff_selected context (E.transferSource pre) command).mp economic
          simp only [step, verdict]
          rw [E.transfer_post_from_leaf_eq selected verdict]
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | managed context command =>
      cases verdict : (FM.transition digest context (E.managedSource pre) command).verdict with
      | rejected code => simp [step, verdict, FixedFrame]
      | accepted =>
          simp only [step, verdict]
          rw [E.managed_post_from_leaf_eq verdict]
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_frame_trans {first second third : C.State}
    (left : FixedFrame first second) (right : FixedFrame second third) :
    FixedFrame first third :=
  ⟨right.1.trans left.1,
    right.2.1.trans left.2.1,
    right.2.2.1.trans left.2.2.1,
    right.2.2.2.1.trans left.2.2.2.1,
    right.2.2.2.2.trans left.2.2.2.2⟩

def run (digest : B.Bytes → String) : C.State → List Action → C.State
  | pre, [] => pre
  | pre, action :: rest => run digest (step digest pre action) rest

/-- A mixed finite history needs complete-row admission only at its initial
state. Static policy shape follows from the fixed frame. -/
theorem run_preserves_rows (digest : B.Bytes → String) (actions : List Action)
    {pre : C.State} (admitted : C.RowsRepresentable pre)
    (policies : StaticPolicyShape pre)
    (commands : ∀ action ∈ actions, CommandShape action) :
    C.RowsRepresentable (run digest pre actions) := by
  induction actions generalizing pre with
  | nil => exact admitted
  | cons first rest ih =>
      have firstRows := step_preserves_rows digest admitted policies
        (commands first List.mem_cons_self)
      have nextPolicies := static_policy_shape_of_frame policies
        (step_fixed_frame digest pre first)
      apply ih firstRows nextPolicies
      intro action member
      exact commands action (List.mem_cons_of_mem first member)

/-- Every finite endpoint retains the complete initial immutable frame. -/
theorem run_fixed_frame (digest : B.Bytes → String) (actions : List Action) (pre : C.State) :
    FixedFrame pre (run digest pre actions) := by
  induction actions generalizing pre with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons first rest ih =>
      exact fixed_frame_trans (step_fixed_frame digest pre first)
        (ih (step digest pre first))

/-- Every reached prefix has complete row admission and the exact initial
immutable frame. -/
theorem every_prefix_rows_and_frame (digest : B.Bytes → String) (actions : List Action)
    {pre : C.State} (admitted : C.RowsRepresentable pre)
    (policies : StaticPolicyShape pre)
    (commands : ∀ action ∈ actions, CommandShape action) (length : Nat) :
    C.RowsRepresentable (run digest pre (actions.take length)) ∧
      FixedFrame pre (run digest pre (actions.take length)) := by
  constructor
  · apply run_preserves_rows digest _ admitted policies
    intro action member
    exact commands action (List.mem_of_mem_take member)
  · exact run_fixed_frame digest _ pre

end Proofs.AssetLaneCustodyFiniteTraceV2
