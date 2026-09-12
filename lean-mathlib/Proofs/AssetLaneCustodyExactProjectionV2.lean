import Proofs.AssetLaneCustodyStructuralV2

/-!
# Exact leaf reprojection for custody completion

The transfer constructor stores every finite leaf field directly. The managed
constructor merges an accepted managed leaf into the unchanged unmanaged
complement; filtering that complete result recovers the full accepted leaf,
including all managed siblings and zero-valued complete supply rows.

These are typed Lean state equalities. They do not establish runtime object
construction, resources, codecs, bytes, roots, receipts, metadata, authority or
publication admission.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyExactProjectionV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace G
export AssetLaneCustodyRefinementV2 (State)
end G
namespace E
export AssetLaneCustodyEffectPlanV2 (transferSource managedSource transferPostFromLeaf
  managedPostFromLeaf)
end E
namespace F
export AssetLaneCustodyFiniteTraceV2 (Action step transfer_accepted_actual_post
  managed_accepted_actual_post)
end F
namespace X
export AssetLaneCustodyStructuralV2 (CompleteStructural ActionAdmission
  managed_source_structural)
end X
namespace FT
export AssetTransferFiniteOutcomeV2 (State transition)
end FT
namespace FM
export ManagedAssetFiniteOutcomeV2 (State Structural transition accepted_iff
  accepted_post_effects economic_candidate_structural)
end FM
namespace T
export AssetTransferRefinementV2 (Context Command)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Context Command)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes)
end B
namespace H
export AssetLaneSharedProjectionV2 (selectRows)
end H
namespace Q
export AssetLaneFiniteRecompositionV2 (selectSupplies outsideBalances outsideSupplies
  mergeBalances mergeSupplies member_eq_of_unique_keys balance_wire_keys_unique
  AccountsDomain)
end Q
namespace R
export AssetLaneCustodyRecompositionV2 (managedAssets)
end R
namespace S
export AssetTransferSparseTablesV1 (balanceWire)
end S
namespace L
export CanonicalEpochEconomicRowsV1 (sortOn sortOn_perm sortOn_ordered)
end L

attribute [local instance] lexOrd

/-- Transfer completion is a left inverse of the full transfer source
projection for every typed leaf state. -/
theorem transfer_post_from_leaf_exact (pre : G.State) (leafPost : FT.State) :
    E.transferSource (E.transferPostFromLeaf pre leafPost) = leafPost := by
  cases leafPost
  rfl

/-- The actual accepted transfer step therefore projects to the finite
transition's complete post, rather than to an independently supplied state. -/
theorem transfer_accepted_step_exact {digest : B.Bytes → String} {pre : G.State}
    {context : T.Context} {command : T.Command}
    (accepted : (FT.transition digest context (E.transferSource pre) command).verdict =
      .accepted) :
    E.transferSource (F.step digest pre (.transfer context command)) =
      (FT.transition digest context (E.transferSource pre) command).post := by
  obtain ⟨_, _, _, actual, _⟩ := F.transfer_accepted_actual_post accepted
  rw [actual]
  exact transfer_post_from_leaf_exact _ _

private theorem selected_outside_balances_empty (managed : List Asset)
    (rows : List AmountRow) :
    (Q.outsideBalances managed rows).filter
      (fun row => decide (row.asset ∈ managed)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have outside : row.asset ∉ managed := by
    simpa using (List.mem_filter.mp member).2
  exact outside (of_decide_eq_true selected)

private theorem selected_outside_supplies_empty (managed : List Asset)
    (rows : List V1SupplyRow) :
    (Q.outsideSupplies managed rows).filter
      (fun row => decide (row.asset ∈ managed)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have outside : row.asset ∉ managed := by
    simpa using (List.mem_filter.mp member).2
  exact outside (of_decide_eq_true selected)

private theorem select_merged_balances (managed : List Asset)
    (pre leafPost : List AmountRow)
    (unique : AssetTransferSparseTablesV1.Unique leafPost)
    (ordered : leafPost.Pairwise
      (fun left right => compare (S.balanceWire left) (S.balanceWire right) = .lt))
    (accounts : Q.AccountsDomain leafPost)
    (selected : ∀ row ∈ leafPost, row.asset ∈ managed) :
    H.selectRows managed (Q.mergeBalances managed pre leafPost) = leafPost := by
  let predicate := fun row : AmountRow => decide (row.asset ∈ managed)
  let source := Q.outsideBalances managed pre ++ leafPost
  have leafSelf : leafPost.filter predicate = leafPost := by
    apply List.filter_eq_self.mpr
    intro row member
    exact decide_eq_true (selected row member)
  have sourceFilter : source.filter predicate = leafPost := by
    rw [List.filter_append, selected_outside_balances_empty managed pre, leafSelf,
      List.nil_append]
  have perm :
      (H.selectRows managed (Q.mergeBalances managed pre leafPost)).Perm leafPost := by
    have sorted := (L.sortOn_perm S.balanceWire source).filter predicate
    change List.Perm ((L.sortOn S.balanceWire source).filter predicate)
      (source.filter predicate) at sorted
    rw [sourceFilter] at sorted
    exact sorted
  have leftOrdered :
      (H.selectRows managed (Q.mergeBalances managed pre leafPost)).Pairwise
        (fun left right =>
          (compare (S.balanceWire left) (S.balanceWire right)).isLE = true) := by
    exact (L.sortOn_ordered S.balanceWire source).filter predicate
  have rightOrdered : leafPost.Pairwise
      (fun left right =>
        (compare (S.balanceWire left) (S.balanceWire right)).isLE = true) := by
    apply ordered.imp
    intro left right less
    rw [less]
    rfl
  have wireUnique := Q.balance_wire_keys_unique leafPost unique accounts
  apply List.Perm.eq_of_pairwise
    (le := fun left right : AmountRow =>
      (compare (S.balanceWire left) (S.balanceWire right)).isLE = true)
  · intro left right leftMember rightMember leftRight rightLeft
    apply Q.member_eq_of_unique_keys S.balanceWire leafPost wireUnique
      (perm.mem_iff.mp leftMember) rightMember
    exact Std.LawfulEqOrd.eq_of_compare
      (Std.OrientedCmp.isLE_antisymm leftRight rightLeft)
  · exact leftOrdered
  · exact rightOrdered
  · exact perm

private theorem select_merged_supplies (managed : List Asset)
    (pre leafPost : List V1SupplyRow) (unique : SourceAssetKeysUnique leafPost)
    (ordered : SourceAssetKeysOrdered leafPost)
    (selected : ∀ row ∈ leafPost, row.asset ∈ managed) :
    Q.selectSupplies managed (Q.mergeSupplies managed pre leafPost) = leafPost := by
  let predicate := fun row : V1SupplyRow => decide (row.asset ∈ managed)
  let source := Q.outsideSupplies managed pre ++ leafPost
  have leafSelf : leafPost.filter predicate = leafPost := by
    apply List.filter_eq_self.mpr
    intro row member
    exact decide_eq_true (selected row member)
  have sourceFilter : source.filter predicate = leafPost := by
    rw [List.filter_append, selected_outside_supplies_empty managed pre, leafSelf,
      List.nil_append]
  have perm :
      (Q.selectSupplies managed (Q.mergeSupplies managed pre leafPost)).Perm leafPost := by
    have sorted := (L.sortOn_perm V1SupplyRow.asset source).filter predicate
    change List.Perm ((L.sortOn V1SupplyRow.asset source).filter predicate)
      (source.filter predicate) at sorted
    rw [sourceFilter] at sorted
    exact sorted
  have leftOrdered :
      (Q.selectSupplies managed (Q.mergeSupplies managed pre leafPost)).Pairwise
        (fun left right => (compare left.asset right.asset).isLE = true) := by
    exact (L.sortOn_ordered V1SupplyRow.asset source).filter predicate
  have rightOrdered : leafPost.Pairwise
      (fun left right => (compare left.asset right.asset).isLE = true) := by
    have strict := List.pairwise_map.mp ordered
    apply strict.imp
    intro left right less
    change (compareOfLessAndEq left.asset right.asset).isLE = true
    simp [compareOfLessAndEq, less]
  apply List.Perm.eq_of_pairwise
    (le := fun left right : V1SupplyRow => (compare left.asset right.asset).isLE = true)
  · intro left right leftMember rightMember leftRight rightLeft
    apply Q.member_eq_of_unique_keys V1SupplyRow.asset leafPost unique
      (perm.mem_iff.mp leftMember) rightMember
    exact Std.LawfulEqOrd.eq_of_compare
      (Std.OrientedCmp.isLE_antisymm leftRight rightLeft)
  · exact leftOrdered
  · exact rightOrdered
  · exact perm

private theorem managed_accepted_leaf_structural {digest : B.Bytes → String}
    {pre : G.State} {context : M.Context} {command : M.Command}
    (admitted : X.CompleteStructural pre)
    (input : X.ActionAdmission (.managed context command))
    (accepted : (FM.transition digest context (E.managedSource pre) command).verdict =
      .accepted) :
    FM.Structural (FM.transition digest context (E.managedSource pre) command).post := by
  have economic :=
    ((FM.accepted_iff digest context (E.managedSource pre) command).mp accepted).1
  rw [(FM.accepted_post_effects accepted).1]
  exact FM.economic_candidate_structural (X.managed_source_structural admitted)
    input.1 input.2 economic

/-- Reprojecting the complete state built from an actual accepted managed leaf
recovers every field of that leaf exactly. -/
theorem managed_accepted_post_exact {digest : B.Bytes → String} {pre : G.State}
    {context : M.Context} {command : M.Command}
    (admitted : X.CompleteStructural pre)
    (input : X.ActionAdmission (.managed context command))
    (accepted : (FM.transition digest context (E.managedSource pre) command).verdict =
      .accepted) :
    E.managedSource (E.managedPostFromLeaf pre
      (FM.transition digest context (E.managedSource pre) command).post) =
        (FM.transition digest context (E.managedSource pre) command).post := by
  let leafPost := (FM.transition digest context (E.managedSource pre) command).post
  have structural : FM.Structural leafPost :=
    managed_accepted_leaf_structural admitted input accepted
  have moduleRelease : leafPost.moduleReleaseId = pre.transferState.moduleReleaseId := by
    change (FM.transition digest context (E.managedSource pre)
      command).post.moduleReleaseId = pre.transferState.moduleReleaseId
    rw [(FM.accepted_post_effects accepted).1]
    rfl
  have policies : leafPost.policies = pre.managedPolicies := by
    change (FM.transition digest context (E.managedSource pre) command).post.policies =
      pre.managedPolicies
    rw [(FM.accepted_post_effects accepted).1]
    rfl
  have balanceSelected : ∀ row ∈ leafPost.balances,
      row.asset ∈ R.managedAssets pre := by
    intro row member
    have supported := structural.balanceSupported row member
    rw [policies] at supported
    exact supported
  have supplySelected : ∀ row ∈ leafPost.supplies,
      row.asset ∈ R.managedAssets pre := by
    intro row member
    have supported : row.asset ∈ leafPost.supplies.map V1SupplyRow.asset :=
      List.mem_map.mpr ⟨row, member, rfl⟩
    rw [structural.keysAgree, policies] at supported
    exact supported
  have balances := select_merged_balances (R.managedAssets pre)
    pre.transferState.balances leafPost.balances structural.balanceUnique
    structural.balanceOrdered
    (fun row member => (structural.balancePositive row member).1) balanceSelected
  have supplies := select_merged_supplies (R.managedAssets pre)
    pre.transferState.supplies leafPost.supplies structural.supplyUnique
    structural.supplyOrdered supplySelected
  unfold E.managedSource E.managedPostFromLeaf
  change ManagedAssetFiniteOutcomeV2.State.mk pre.transferState.moduleReleaseId
      pre.managedPolicies
      (H.selectRows (R.managedAssets pre)
        (Q.mergeBalances (R.managedAssets pre) pre.transferState.balances leafPost.balances))
      (Q.selectSupplies (R.managedAssets pre)
        (Q.mergeSupplies (R.managedAssets pre) pre.transferState.supplies leafPost.supplies)) =
    leafPost
  rw [← moduleRelease, ← policies, balances, supplies]

/-- The accepted managed finite step uses the same completed state whose exact
managed reprojection was established above. -/
theorem managed_accepted_step_exact {digest : B.Bytes → String} {pre : G.State}
    {context : M.Context} {command : M.Command}
    (admitted : X.CompleteStructural pre)
    (input : X.ActionAdmission (.managed context command))
    (accepted : (FM.transition digest context (E.managedSource pre) command).verdict =
      .accepted) :
    E.managedSource (F.step digest pre (.managed context command)) =
      (FM.transition digest context (E.managedSource pre) command).post := by
  obtain ⟨_, _, _, actual, _, _⟩ :=
    F.managed_accepted_actual_post admitted.rows accepted
  rw [actual]
  exact managed_accepted_post_exact admitted input accepted

end Proofs.AssetLaneCustodyExactProjectionV2
