import Proofs.AssetLaneCustodyRefinementV2

/-!
# Continuation of the finite-row V2 custody model

The single-command lift does not by itself establish that its successor is a
legal input to another command. This file derives leaf input bounds from the
complete physical rows and proves preservation of `RowsRepresentable`.

Policies are selected from the initial immutable lists; their shape and command
widths are explicit input premises. Roots remain abstract. These results cover
the existing finite-row leaf model, not runtime decoding, resource ceilings,
authentication, global admission, receipts, or durable publication.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyTraceV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1 AssetLaneCustodyRefinementV2

namespace T
export AssetTransferRefinementV2 (StateWellFormed CommandWellFormed IsU128
  RootModel Context Policy Command transition Verdict)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (StateWellFormed CommandWellFormed PolicyWellFormed
  RootModel Context Policy Command transition Verdict signedAmount)
end M
namespace C
export CanonicalEpochEconomicRowsV1 (AmountKey amountKey amountSum lookupLast
  lookupLast_eq_amountAt amountSum_eq_amountAt sortOn_perm)
end C
namespace S
export AssetTransferSparseTablesV1 (accountKey putAmount eraseKey makeAmount balanceWire)
end S

attribute [local instance] lexOrd

private theorem asset_total_nonnegative (rows : List AmountRow) (asset : Asset)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms) :
    0 ≤ amountForAsset rows asset := by
  induction rows with
  | nil => change (0 : Int) ≤ 0; omega
  | cons row rows ih =>
    have head := nonnegative row List.mem_cons_self
    have tail := ih (fun next member => nonnegative next (List.mem_cons_of_mem row member))
    change 0 ≤ (if row.asset = asset then row.amountAtoms else 0) + amountForAsset rows asset
    split <;> omega

private theorem account_sum_nonnegative (rows : List AmountRow) (key : C.AmountKey)
    (nonnegative : ∀ row ∈ rows, 0 ≤ row.amountAtoms) :
    0 ≤ C.amountSum key rows := by
  induction rows with
  | nil => change (0 : Int) ≤ 0; omega
  | cons row rows ih =>
    have head := nonnegative row List.mem_cons_self
    have tail := ih (fun next member => nonnegative next (List.mem_cons_of_mem row member))
    change 0 ≤ (if C.amountKey row = key then row.amountAtoms else 0) + C.amountSum key rows
    split <;> omega

theorem supply_bounded {pre : State} (admitted : RowsRepresentable pre) (asset : Asset) :
    FitsU128 (supplyAt pre asset) := by
  unfold supplyAt
  rw [supplyFor_numericRows_preserved]
  by_cases present : asset ∈ pre.transferState.supplies.map V1SupplyRow.asset
  · obtain ⟨row, member, same⟩ := List.mem_map.mp present
    subst asset
    rw [source_supplyFor_eq_member_of_unique admitted.supplyUnique member]
    exact admitted.supplyBounded row member
  · rw [source_supplyFor_zero_of_absent (by
      intro row member same
      exact present (List.mem_map.mpr ⟨row, member, same⟩))]
    exact ⟨by omega, by unfold maxU128; omega⟩

private theorem balances_nonnegative {pre : State} (admitted : RowsRepresentable pre) :
    ∀ row ∈ pre.transferState.balances, 0 ≤ row.amountAtoms :=
  fun row member => (admitted.balancePositive row member).2.1.1

/-- Account totals are bounded by physical supply, with custody counted once. -/
theorem account_bounds {pre : State} (admitted : RowsRepresentable pre) (asset : Asset) :
    FitsU128 (amountForAsset pre.transferState.balances asset) ∧
      amountForAsset pre.transferState.balances asset ≤ supplyAt pre asset ∧
      ∀ owner, T.IsU128 (C.lookupLast (S.accountKey asset owner) pre.transferState.balances) := by
  have nonnegative := balances_nonnegative admitted
  have totalLow := asset_total_nonnegative _ asset nonnegative
  have custodyLow := asset_total_nonnegative pre.custody asset (by
    intro row member; exact Int.le_of_lt (admitted.custodyShape row member).2.1)
  have balance := admitted.balanced asset
  have supply := supply_bounded admitted asset
  dsimp only [physicalFor] at balance
  have cover : amountForAsset pre.transferState.balances asset ≤ supplyAt pre asset := by omega
  refine ⟨⟨totalLow, by exact Int.le_trans cover supply.2⟩, cover, ?_⟩
  intro owner
  rw [C.lookupLast_eq_amountAt _ _ admitted.balanceUnique, ← C.amountSum_eq_amountAt]
  have low := account_sum_nonnegative _ (S.accountKey asset owner) nonnegative
  have high := ManagedAssetFiniteAccountingV2.account_sum_le_asset_total
    pre.transferState.balances asset owner nonnegative
  change 0 ≤ _ ∧ _ ≤ maxU128
  exact ⟨low, Int.le_trans high (Int.le_trans cover supply.2)⟩

theorem transfer_view_well_formed {pre : State} (admitted : RowsRepresentable pre)
    (policy : AssetTransferRefinementV2.Policy) (fee : T.IsU128 policy.transferFeeAtoms)
    (decimals : policy.atomDecimals = 8) :
    T.StateWellFormed (transferView pre policy) := by
  have bounds := account_bounds admitted policy.asset
  exact ⟨bounds.2.2, supply_bounded admitted policy.asset, bounds.1, bounds.2.1,
    fee, decimals⟩

theorem managed_view_well_formed {pre : State} (admitted : RowsRepresentable pre)
    (policy : ManagedAssetLifecycleRefinementV2.Policy) (shape : M.PolicyWellFormed policy) :
    M.StateWellFormed (managedView pre policy) := by
  have bounds := account_bounds admitted policy.asset
  exact ⟨bounds.2.2, supply_bounded admitted policy.asset, bounds.1, bounds.2.1, shape⟩

private theorem updated_assets_covered (rows : List AmountRow) (keys : List Asset)
    (asset owner : String) (delta : Int) (selected : asset ∈ keys)
    (covered : ∀ row ∈ rows, row.asset ∈ keys) :
    ∀ row ∈ ManagedAssetFiniteAccountingV2.updateRows rows asset owner delta,
      row.asset ∈ keys := by
  intro row member
  have unsorted := (C.sortOn_perm S.balanceWire _).mem_iff.mp member
  dsimp only [S.putAmount] at unsorted
  split at unsorted
  · exact covered row ((List.mem_filter.mp unsorted).1)
  · rcases List.mem_cons.mp unsorted with same | old
    · subst row; exact selected
    · exact covered row ((List.mem_filter.mp old).1)

private theorem transfer_assets_covered (rows : List AmountRow) (keys : List Asset)
    (asset : Asset) (delta : String → Int) (roles : List String) (selected : asset ∈ keys)
    (covered : ∀ row ∈ rows, row.asset ∈ keys) :
    ∀ row ∈ AssetTransferFiniteAccountingV2.updateRoles rows asset delta roles,
      row.asset ∈ keys := by
  induction roles with
  | nil => exact covered
  | cons owner rest ih => exact updated_assets_covered _ keys asset owner _ selected ih

private theorem adjusted_supply_bounded {rows : List V1SupplyRow} (asset : Asset) (delta : Int)
    (unique : SourceAssetKeysUnique rows) (bounded : SourceRowsU128 rows)
    (after : FitsU128 (supplyFor (numericRows rows) asset + delta)) :
    SourceRowsU128 (adjustComplete asset delta rows) := by
  intro row member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  subst row
  split
  · rename_i selected
    have amount := source_supplyFor_eq_member_of_unique unique priorMember
    rw [← supplyFor_numericRows_preserved, selected] at amount
    simpa only [amount] using after
  · exact bounded prior priorMember

/-- Transfer preserves every row condition needed by the next selected leaf. -/
theorem transfer_preserves_rows {roots : T.RootModel} {context : T.Context} {pre : State}
    {policy : T.Policy} {command : T.Command} (admitted : RowsRepresentable pre)
    (selectedPolicy : policy ∈ pre.transferState.policies)
    (fee : T.IsU128 policy.transferFeeAtoms) (decimals : policy.atomDecimals = 8)
    (accepted : (T.transition roots context (transferView pre policy) command).verdict = .accepted) :
    RowsRepresentable (transferPost pre policy command) := by
  have selected : command.asset = policy.asset :=
    AssetTransferFiniteAccountingV2.accepted_selected_asset accepted
  have policyRegistered : policy.asset ∈ pre.originRegistry := by
    rw [← admitted.policyKeys]
    exact List.mem_map.mpr ⟨policy, selectedPolicy, rfl⟩
  have accounts := AssetTransferFiniteAccountingV2.accepted_rows_preserve_accounts
    admitted.balanceUnique admitted.balancePositive
    (transfer_view_well_formed admitted policy fee decimals) accepted
  have physical := transfer_physical_lift pre policy command admitted.balanceUnique
    (AssetTransferFiniteAccountingV2.accepted_distinct accepted) admitted.balanced
  refine { admitted with
    balanceUnique := accounts.1
    balancePositive := accounts.2
    holdingsCovered := ?_
    balanced := physical.1 }
  intro row member
  rcases List.mem_append.mp member with changed | retained
  · exact transfer_assets_covered _ pre.originRegistry command.asset _ _
      (selected ▸ policyRegistered) (fun item present =>
        admitted.holdingsCovered item (List.mem_append_left _ present)) row changed
  · exact admitted.holdingsCovered row (List.mem_append_right _ retained)

/-- Issue and burn preserve the complete supply carrier, including dormant keys. -/
theorem managed_preserves_rows {roots : M.RootModel} {context : M.Context} {pre : State}
    {policy : M.Policy} {command : M.Command} (admitted : RowsRepresentable pre)
    (selectedPolicy : policy ∈ pre.managedPolicies) (shape : M.PolicyWellFormed policy)
    (commandShape : M.CommandWellFormed command)
    (accepted : (M.transition roots context (managedView pre policy) command).verdict = .accepted) :
    RowsRepresentable (managedPost pre command.asset command.accountOwner (M.signedAmount command)) := by
  have selected : command.asset = policy.asset :=
    ManagedAssetLifecycleRefinementV2.accepted_authorization_guard accepted
      (code := .unknownAsset) (by decide)
  have registered : command.asset ∈ pre.originRegistry := by
    rw [selected]; exact admitted.managedCovered policy selectedPolicy
  have supplyRegistered : command.asset ∈ pre.transferState.supplies.map V1SupplyRow.asset := by
    rw [← admitted.registryKeys]; exact registered
  have source := managed_view_well_formed admitted policy shape
  have accounts := ManagedAssetFiniteAccountingV2.accepted_rows_preserve_accounts
    admitted.balanceUnique admitted.balancePositive source commandShape accepted
  have postSupply := ManagedAssetLifecycleRefinementV2.accepted_post_supply_u128
    source commandShape accepted
  rw [(ManagedAssetLifecycleRefinementV2.accepted_post_and_effects accepted).1] at postSupply
  change FitsU128 (supplyAt pre policy.asset + M.signedAmount command) at postSupply
  rw [← selected] at postSupply
  have physical := managed_physical_lift pre command.asset command.accountOwner
    (M.signedAmount command) admitted.balanceUnique admitted.supplyUnique supplyRegistered
    admitted.balanced
  refine { admitted with
    supplyUnique := adjustComplete_unique admitted.supplyUnique _ _
    supplyOrdered := adjustComplete_ordered admitted.supplyOrdered _ _
    supplyBounded := adjusted_supply_bounded _ _ admitted.supplyUnique admitted.supplyBounded postSupply
    registryKeys := ?_
    balanceUnique := accounts.1
    balancePositive := accounts.2
    holdingsCovered := ?_
    balanced := physical.1 }
  · exact admitted.registryKeys.trans (adjustComplete_keys _ _ _).symm
  · intro row member
    rcases List.mem_append.mp member with changed | retained
    · exact updated_assets_covered _ pre.originRegistry command.asset command.accountOwner _ registered
        (fun item present => admitted.holdingsCovered item (List.mem_append_left _ present)) row changed
    · exact admitted.holdingsCovered row (List.mem_append_right _ retained)

inductive Action where
  | transfer (context : T.Context) (policy : T.Policy) (command : T.Command)
  | managed (context : M.Context) (policy : M.Policy) (command : M.Command)

/-- Static input/selection premises, never an assumption about successor rows. -/
def Ready (pre : State) : Action → Prop
  | .transfer _ policy command =>
      policy ∈ pre.transferState.policies ∧ T.IsU128 policy.transferFeeAtoms ∧
        policy.atomDecimals = 8 ∧ T.CommandWellFormed command
  | .managed _ policy command =>
      policy ∈ pre.managedPolicies ∧ M.PolicyWellFormed policy ∧ M.CommandWellFormed command

def step (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (pre : State) : Action → State
  | .transfer context policy command => (transferStep transferRoots context pre policy command).2
  | .managed context policy command => (managedStep managedRoots context pre policy command).2

def run (transferRoots : T.RootModel) (managedRoots : M.RootModel) : State → List Action → State
  | pre, [] => pre
  | pre, action :: rest => run transferRoots managedRoots
      (step transferRoots managedRoots pre action) rest

/-- Rejection takes the original state; acceptance uses the actual leaf guards. -/
theorem step_preserves_rows (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    {pre : State} {action : Action} (admitted : RowsRepresentable pre) (ready : Ready pre action) :
    RowsRepresentable (step transferRoots managedRoots pre action) := by
  cases action with
  | transfer context policy command =>
    simp only [step, transferStep]
    cases verdict : (T.transition transferRoots context (transferView pre policy) command).verdict with
    | accepted => exact transfer_preserves_rows admitted ready.1 ready.2.1 ready.2.2.1 verdict
    | rejected _ => exact admitted
  | managed context policy command =>
    simp only [step, managedStep]
    cases verdict : (M.transition managedRoots context (managedView pre policy) command).verdict with
    | accepted => exact managed_preserves_rows admitted ready.1 ready.2.1 ready.2.2 verdict
    | rejected _ => exact admitted

/-- Policies and custody ownership cannot change through this command family. -/
theorem step_fixed_frame (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (pre : State) (action : Action) :
    let post := step transferRoots managedRoots pre action
    post.transferState.moduleReleaseId = pre.transferState.moduleReleaseId ∧
      post.transferState.policies = pre.transferState.policies ∧
      post.originRegistry = pre.originRegistry ∧
      post.managedPolicies = pre.managedPolicies ∧ post.custody = pre.custody := by
  cases action with
  | transfer context policy command =>
    simp only [step, transferStep]
    cases (T.transition transferRoots context (transferView pre policy) command).verdict <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | managed context policy command =>
    simp only [step, managedStep]
    cases (M.transition managedRoots context (managedView pre policy) command).verdict <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem ready_after_step (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    {pre : State} (first : Action) {next : Action} (ready : Ready pre next) :
    Ready (step transferRoots managedRoots pre first) next := by
  have frame := step_fixed_frame transferRoots managedRoots pre first
  cases next with
  | transfer context policy command =>
    change policy ∈ _ ∧ _
    rw [frame.2.1]
    exact ready
  | managed context policy command =>
    change policy ∈ _ ∧ _
    rw [frame.2.2.2.1]
    exact ready

/-- An arbitrary finite mixed history needs representation admission only once.
All later representation bounds follow from the executable modeled steps. -/
theorem run_preserves_rows (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (actions : List Action) {pre : State} (admitted : RowsRepresentable pre)
    (ready : ∀ action ∈ actions, Ready pre action) :
    RowsRepresentable (run transferRoots managedRoots pre actions) := by
  induction actions generalizing pre with
  | nil => exact admitted
  | cons first rest ih =>
    apply ih (step_preserves_rows transferRoots managedRoots admitted (ready first List.mem_cons_self))
    intro next member
    exact ready_after_step transferRoots managedRoots first
      (ready next (List.mem_cons_of_mem first member))

/-- Whole-row custody preservation rules out equal-total owner substitution. -/
theorem run_fixed_frame (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (actions : List Action) (pre : State) :
    let post := run transferRoots managedRoots pre actions
    post.transferState.moduleReleaseId = pre.transferState.moduleReleaseId ∧
      post.transferState.policies = pre.transferState.policies ∧
      post.originRegistry = pre.originRegistry ∧
      post.managedPolicies = pre.managedPolicies ∧ post.custody = pre.custody := by
  induction actions generalizing pre with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons first rest ih =>
    have firstFrame := step_fixed_frame transferRoots managedRoots pre first
    have restFrame := ih (step transferRoots managedRoots pre first)
    exact ⟨restFrame.1.trans firstFrame.1,
      restFrame.2.1.trans firstFrame.2.1,
      restFrame.2.2.1.trans firstFrame.2.2.1,
      restFrame.2.2.2.1.trans firstFrame.2.2.2.1,
      restFrame.2.2.2.2.trans firstFrame.2.2.2.2⟩

/-- Each reached prefix preserves physical/supply reconciliation and row admission. -/
theorem every_prefix_preserves_rows (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (actions : List Action) {pre : State} (admitted : RowsRepresentable pre)
    (ready : ∀ action ∈ actions, Ready pre action) (length : Nat) :
    RowsRepresentable (run transferRoots managedRoots pre (actions.take length)) := by
  apply run_preserves_rows transferRoots managedRoots _ admitted
  intro action member
  exact ready action (List.mem_of_mem_take member)

end Proofs.AssetLaneCustodyTraceV2
