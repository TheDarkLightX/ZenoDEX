import Proofs.AssetTransferSparseSupplyV1
import Proofs.ManagedAssetLifecycleRefinementV2

/-!
# Finite-row materialization for managed issue and burn

The lifecycle model's balance function and account total are derived from one
finite account table. Its accepted arithmetic materializes through the existing
erase/put/sort operations, including creation and zero deletion. The selected
account is bounded by the actual per-asset sum, closing the detached-total
counterexample for this representation.

V1-labelled table helpers are reused for their integer row algebra only. This
does not convert a wire ABI, authenticate a policy, model a complete coordinator,
or prove Python/Rust execution refinement. Resource-ceiling admission, supply
support, shared multi-policy continuation, roots and publication remain separate.
-/
set_option warningAsError true

namespace Proofs.ManagedAssetFiniteAccountingV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace S
export Proofs.AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey
  balanceWire putAmount putAmount_unique amountSum_putAmount amountSum_sortOn
  perm_sum_int checkedUpdate checkedUpdate_positive checkedUpdate_spec)
end S
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (amountKey amountSum lookupLast
  lookupLast_eq_amountAt amountSum_eq_amountAt sortOn sortOn_perm)
end C
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (LifecycleState Policy RootModel
  Context Command StateWellFormed CommandWellFormed transition acceptedState
  signedAmount accepted_post_and_effects accepted_authorization_guard
  accepted_post_supply_u128 accepted_post_selected_balance_u128 RejectCode)
end M
namespace T
export Proofs.AssetTransferRefinementV2 (IsU128 u128Max)
end T

attribute [local instance] lexOrd

/-- No caller-supplied account total survives this observation. -/
def project (moduleReleaseId : String) (policy : M.Policy)
    (rows : List AmountRow) (supplyAtoms : Int) : M.LifecycleState :=
  ⟨moduleReleaseId, policy, fun owner => C.lookupLast (S.accountKey policy.asset owner) rows,
    supplyAtoms, amountForAsset rows policy.asset⟩

/-- Independent finite-row counterpart of the selected account update. -/
def updateRows (rows : List AmountRow) (asset owner : String) (delta : Int) :
    List AmountRow :=
  C.sortOn S.balanceWire (S.putAmount (S.accountKey asset owner)
    (C.lookupLast (S.accountKey asset owner) rows + delta) rows)

theorem updateRows_unique (rows : List AmountRow) (asset owner : String) (delta : Int)
    (unique : S.Unique rows) : S.Unique (updateRows rows asset owner delta) := by
  exact ((C.sortOn_perm S.balanceWire _).map C.amountKey).nodup_iff.mpr
    (S.putAmount_unique _ _ _ unique)

theorem updateRows_lookup (rows : List AmountRow) (asset owner : String) (delta : Int)
    (unique : S.Unique rows) (queryAsset queryOwner : String) :
    C.lookupLast (S.accountKey queryAsset queryOwner) (updateRows rows asset owner delta) =
      if asset = queryAsset ∧ owner = queryOwner then
        C.lookupLast (S.accountKey queryAsset queryOwner) rows + delta
      else C.lookupLast (S.accountKey queryAsset queryOwner) rows := by
  rw [C.lookupLast_eq_amountAt _ _ (updateRows_unique rows asset owner delta unique),
    ← C.amountSum_eq_amountAt]
  unfold updateRows
  rw [S.amountSum_sortOn, S.amountSum_putAmount,
    C.amountSum_eq_amountAt, ← C.lookupLast_eq_amountAt _ _ unique]
  by_cases selected : asset = queryAsset ∧ owner = queryOwner
  · rcases selected with ⟨rfl, rfl⟩
    simp
  · have different : S.accountKey asset owner ≠ S.accountKey queryAsset queryOwner := by
      simpa [S.accountKey, and_comm] using selected
    simp only [if_neg different, if_neg selected]

theorem updateRows_total (rows : List AmountRow) (asset owner : String) (delta : Int)
    (unique : S.Unique rows) (query : String) :
    amountForAsset (updateRows rows asset owner delta) query =
      amountForAsset rows query + (if asset = query then delta else 0) := by
  unfold updateRows
  rw [show amountForAsset (C.sortOn S.balanceWire _) query =
      amountForAsset (S.putAmount (S.accountKey asset owner)
        (C.lookupLast (S.accountKey asset owner) rows + delta) rows) query from
      S.perm_sum_int ((C.sortOn_perm S.balanceWire _).map _)]
  rw [AssetTransferSparseSupplyV1.amountForAsset_putAmount,
    C.lookupLast_eq_amountAt _ _ unique, ← C.amountSum_eq_amountAt]
  change amountForAsset rows query +
    (if asset = query then C.amountSum (S.accountKey asset owner) rows + delta -
      C.amountSum (S.accountKey asset owner) rows else 0) = _
  split <;> omega

theorem account_sum_le_asset_total (rows : List AmountRow) (asset owner : String)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms) :
    C.amountSum (S.accountKey asset owner) rows ≤ amountForAsset rows asset := by
  induction rows with
  | nil => change (0 : Int) ≤ 0; omega
  | cons row rows ih =>
      have head := nonnegative row (by simp)
      have tail := ih (fun next member => nonnegative next (by simp [member]))
      change (if C.amountKey row = S.accountKey asset owner then row.amountAtoms else 0) +
        C.amountSum (S.accountKey asset owner) rows ≤
        (if row.asset = asset then row.amountAtoms else 0) + amountForAsset rows asset
      by_cases same : C.amountKey row = S.accountKey asset owner
      · have selected : row.asset = asset := congrArg (fun key => key.2.1) same
        simp only [if_pos same, if_pos selected]
        omega
      · rw [if_neg same]
        split <;> omega

/-- The selected balance cannot exceed the sum containing its physical row. -/
theorem projected_balance_le_total (moduleReleaseId : String) (policy : M.Policy)
    (rows : List AmountRow) (supplyAtoms : Int) (unique : S.Unique rows)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms) (owner : String) :
    (project moduleReleaseId policy rows supplyAtoms).balance owner ≤
      (project moduleReleaseId policy rows supplyAtoms).accountTotalAtoms := by
  change C.lookupLast (S.accountKey policy.asset owner) rows ≤ amountForAsset rows policy.asset
  rw [C.lookupLast_eq_amountAt _ _ unique, ← C.amountSum_eq_amountAt]
  exact account_sum_le_asset_total rows policy.asset owner nonnegative

theorem updateRows_positive (rows : List AmountRow) (asset owner : String) (delta : Int)
    (positive : S.PositiveAccounts rows)
    (bounded : T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta)) :
    S.PositiveAccounts (updateRows rows asset owner delta) := by
  have checked : S.checkedUpdate rows asset owner delta =
      .ok (S.putAmount (S.accountKey asset owner)
        (C.lookupLast (S.accountKey asset owner) rows + delta) rows) := by
    change 0 ≤ C.lookupLast (S.accountKey asset owner) rows + delta ∧
      C.lookupLast (S.accountKey asset owner) rows + delta ≤
        AssetTransferRefinementV1.u128Max at bounded
    unfold S.checkedUpdate
    rw [if_neg (by omega), if_neg (by omega)]
  have retained := S.checkedUpdate_positive positive checked
  intro row member
  exact retained row ((C.sortOn_perm S.balanceWire _).mem_iff.mp member)

/-- The new total and every account lookup are computed from materialized rows. -/
theorem materializes_accepted_state (moduleReleaseId : String) (policy : M.Policy)
    (rows : List AmountRow) (supplyAtoms : Int) (command : M.Command)
    (unique : S.Unique rows) (selected : command.asset = policy.asset) :
    project moduleReleaseId policy
        (updateRows rows command.asset command.accountOwner (M.signedAmount command))
        (supplyAtoms + M.signedAmount command) =
      M.acceptedState (project moduleReleaseId policy rows supplyAtoms) command := by
  unfold project M.acceptedState
  congr 1
  · funext owner
    rw [updateRows_lookup rows command.asset command.accountOwner _ unique policy.asset owner]
    by_cases same : owner = command.accountOwner
    · simp only [selected, same, and_self, if_true]
    · simp only [selected, true_and, if_neg same, if_neg (Ne.symm same)]
  · rw [updateRows_total rows command.asset command.accountOwner _ unique policy.asset]
    simp only [selected, if_true]

/-- Acceptance supplies the actual selected-asset binding; it is not a premise
about a caller-proposed successor. -/
theorem accepted_materialization {roots : M.RootModel} {ctx : M.Context}
    {moduleReleaseId : String} {policy : M.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : M.Command} (unique : S.Unique rows)
    (accepted : (M.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    (M.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).post =
      project moduleReleaseId policy
        (updateRows rows command.asset command.accountOwner (M.signedAmount command))
        (supplyAtoms + M.signedAmount command) := by
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  rw [(M.accepted_post_and_effects accepted).1]
  exact (materializes_accepted_state moduleReleaseId policy rows supplyAtoms command
    unique selected).symm

/-- With a finite nonnegative source table, an accepted burn cannot make the
account total negative. Initial backing and matched deltas give the upper bound. -/
theorem accepted_preserves_state_well_formed {roots : M.RootModel} {ctx : M.Context}
    {moduleReleaseId : String} {policy : M.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : M.Command} (unique : S.Unique rows)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms)
    (preAdmitted : M.StateWellFormed (project moduleReleaseId policy rows supplyAtoms))
    (commandAdmitted : M.CommandWellFormed command)
    (accepted : (M.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    M.StateWellFormed
      (M.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).post := by
  have supply := M.accepted_post_supply_u128 preAdmitted commandAdmitted accepted
  have balance := M.accepted_post_selected_balance_u128 preAdmitted commandAdmitted accepted
  have contained := projected_balance_le_total moduleReleaseId policy rows supplyAtoms
    unique nonnegative command.accountOwner
  rw [(M.accepted_post_and_effects accepted).1] at supply balance ⊢
  change T.IsU128 (supplyAtoms + M.signedAmount command) at supply
  simp only [M.acceptedState, if_true] at balance
  change T.IsU128 (C.lookupLast (S.accountKey policy.asset command.accountOwner) rows +
    M.signedAmount command) at balance
  have cover := preAdmitted.accountCover
  change amountForAsset rows policy.asset ≤ supplyAtoms at cover
  change C.lookupLast (S.accountKey policy.asset command.accountOwner) rows ≤
    amountForAsset rows policy.asset at contained
  have total : T.IsU128 (amountForAsset rows policy.asset + M.signedAmount command) := by
    unfold T.IsU128 at supply balance ⊢
    constructor <;> omega
  constructor
  · intro owner
    change T.IsU128 (if owner = command.accountOwner then
      C.lookupLast (S.accountKey policy.asset owner) rows + M.signedAmount command
      else C.lookupLast (S.accountKey policy.asset owner) rows)
    by_cases same : owner = command.accountOwner
    · simpa only [if_pos same, same] using balance
    · rw [if_neg same]
      exact preAdmitted.balances owner
  · exact supply
  · exact total
  · change amountForAsset rows policy.asset + M.signedAmount command ≤
      supplyAtoms + M.signedAmount command
    omega
  · exact preAdmitted.policy

theorem accepted_rows_preserve_accounts {roots : M.RootModel} {ctx : M.Context}
    {moduleReleaseId : String} {policy : M.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : M.Command} (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows)
    (preAdmitted : M.StateWellFormed (project moduleReleaseId policy rows supplyAtoms))
    (commandAdmitted : M.CommandWellFormed command)
    (accepted : (M.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    S.Unique (updateRows rows command.asset command.accountOwner (M.signedAmount command)) ∧
    S.PositiveAccounts
      (updateRows rows command.asset command.accountOwner (M.signedAmount command)) := by
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  have bounded := M.accepted_post_selected_balance_u128 preAdmitted commandAdmitted accepted
  rw [(M.accepted_post_and_effects accepted).1] at bounded
  simp only [M.acceptedState, if_true] at bounded
  change T.IsU128 (C.lookupLast (S.accountKey policy.asset command.accountOwner) rows +
    M.signedAmount command) at bounded
  rw [← selected] at bounded
  exact ⟨updateRows_unique rows _ _ _ unique, updateRows_positive rows _ _ _ positive bounded⟩

/-! ## Nonvacuity and the previously detached-total counterexample -/

def exampleRows : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"bob", "ORD", "accounts", 1⟩]

/-- Three of the four ORD atoms may reside outside accounts. No liability is
counted as an additional physical holding. -/
def examplePre : M.LifecycleState :=
  project "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy exampleRows 4

def exampleBurn : M.Command :=
  { ManagedAssetLifecycleRefinementV2.burnCommand with amountAtoms := 1 }

theorem example_pre_well_formed : M.StateWellFormed examplePre := by
  constructor
  · intro owner
    by_cases bob : owner = "bob"
    · subst owner; decide
    · simp [examplePre, project, exampleRows,
        ManagedAssetLifecycleRefinementV2.ordinaryPolicy, C.lookupLast, C.amountKey,
        S.accountKey, bob, T.IsU128, T.u128Max]
  · decide
  · decide
  · decide
  · constructor
    · rfl
    · intro different
      exact False.elim (different rfl)

theorem full_account_burn_materializes_zero_with_other_asset_frame :
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext examplePre exampleBurn).verdict = .accepted ∧
    updateRows exampleRows "ORD" "bob" (-1) = [⟨"carol", "EUR", "accounts", 7⟩] ∧
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext examplePre exampleBurn).post.accountTotalAtoms = 0 ∧
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext examplePre exampleBurn).post.supplyAtoms = 3 := by
  have updated : updateRows exampleRows "ORD" "bob" (-1) =
      [⟨"carol", "EUR", "accounts", 7⟩] := by
    change C.sortOn S.balanceWire [⟨"carol", "EUR", "accounts", 7⟩] = _
    simp [C.sortOn]
  exact ⟨by decide, updated, by decide, by decide⟩

def detachedTotal : M.LifecycleState := { examplePre with accountTotalAtoms := 0 }

theorem detached_total_passes_old_quantity_premises : M.StateWellFormed detachedTotal := by
  exact ⟨example_pre_well_formed.balances, example_pre_well_formed.supply,
    by decide, by decide, example_pre_well_formed.policy⟩

/-- The earlier free total admits this model-only bad post; the finite-row
projection excludes it by construction. It is not a constructible runtime input. -/
theorem detached_total_burn_counterexample :
    detachedTotal.accountTotalAtoms ≠ amountForAsset exampleRows "ORD" ∧
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext detachedTotal exampleBurn).verdict = .accepted ∧
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext detachedTotal exampleBurn).post.accountTotalAtoms = -1 := by
  decide

end Proofs.ManagedAssetFiniteAccountingV2
