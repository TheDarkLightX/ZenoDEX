import Proofs.ManagedAssetRegisteredAccountingV2
import Proofs.AssetTransferFiniteAccountingV2

/-!
# Shared finite account observations for the V2 asset lane

The runtime derives its transfer and managed leaves from one account table.
Filtering that table to the declared managed assets preserves every selected
asset's account lookup and actual total. No independent sibling balance state
or detached account-total premise is introduced.

These observations do not authenticate the declared policy set or establish
resource, codec, root, replay, or publisher admission.
-/
set_option warningAsError true

namespace Proofs.AssetLaneSharedProjectionV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace A
export Proofs.ManagedAssetFiniteAccountingV2 (project updateRows updateRows_lookup
  updateRows_total)
end A
namespace S
export Proofs.AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey)
end S
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (amountKey amountSum lookupLast
  lookupLast_eq_amountAt amountSum_eq_amountAt)
end C
namespace M
export Proofs.ManagedAssetLifecycleRefinementV2 (Policy LifecycleState StateWellFormed
  PolicyWellFormed RootModel Context Command CommandWellFormed transition signedAmount)
end M
namespace T
export Proofs.AssetTransferRefinementV2 (Policy TransferState StateWellFormed IsU128
  Command RootModel Context transition delta)
end T
namespace F
export Proofs.AssetTransferFiniteAccountingV2 (project transferRows transferRows_lookup
  transferRows_totals accepted_materialization accepted_project_well_formed accepted_distinct)
end F
namespace R
export Proofs.ManagedAssetRegisteredAccountingV2 (accountingPost
  accepted_accounting_well_formed)
end R

/-- The same membership filter used by the managed-leaf observation. -/
def selectRows (assets : List String) (rows : List AmountRow) : List AmountRow :=
  rows.filter (fun row => decide (row.asset ∈ assets))

theorem selectRows_unique (assets : List String) (rows : List AmountRow)
    (unique : S.Unique rows) : S.Unique (selectRows assets rows) := by
  have subset : (selectRows assets rows).Sublist rows := List.filter_sublist
  exact (subset.map C.amountKey).nodup unique

theorem selectRows_amountSum (assets : List String) (rows : List AmountRow)
    (asset owner : String) (selected : asset ∈ assets) :
    C.amountSum (S.accountKey asset owner) (selectRows assets rows) =
      C.amountSum (S.accountKey asset owner) rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases retained : row.asset ∈ assets
      · have shape : selectRows assets (row :: rows) = row :: selectRows assets rows := by
          simp [selectRows, retained]
        rw [shape]
        change (if C.amountKey row = S.accountKey asset owner then row.amountAtoms else 0) +
          C.amountSum (S.accountKey asset owner) (selectRows assets rows) = _
        rw [ih]
        rfl
      · have different : C.amountKey row ≠ S.accountKey asset owner := by
          intro same
          have bound : row.asset = asset := congrArg (fun key => key.2.1) same
          exact retained (bound ▸ selected)
        have shape : selectRows assets (row :: rows) = selectRows assets rows := by
          simp [selectRows, retained]
        rw [shape]
        change C.amountSum (S.accountKey asset owner) (selectRows assets rows) =
          (if C.amountKey row = S.accountKey asset owner then row.amountAtoms else 0) + _
        rw [if_neg different, Int.zero_add, ih]

theorem selectRows_total (assets : List String) (rows : List AmountRow)
    (asset : String) (selected : asset ∈ assets) :
    amountForAsset (selectRows assets rows) asset = amountForAsset rows asset := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases retained : row.asset ∈ assets
      · have shape : selectRows assets (row :: rows) = row :: selectRows assets rows := by
          simp [selectRows, retained]
        rw [shape]
        change (if row.asset = asset then row.amountAtoms else 0) +
          amountForAsset (selectRows assets rows) asset = _
        rw [ih]
        rfl
      · have different : row.asset ≠ asset := fun same => retained (same ▸ selected)
        have shape : selectRows assets (row :: rows) = selectRows assets rows := by
          simp [selectRows, retained]
        rw [shape]
        change amountForAsset (selectRows assets rows) asset =
          (if row.asset = asset then row.amountAtoms else 0) + _
        rw [if_neg different, Int.zero_add, ih]
        rfl

theorem selectRows_lookup (assets : List String) (rows : List AmountRow)
    (asset owner : String) (selected : asset ∈ assets) (unique : S.Unique rows) :
    C.lookupLast (S.accountKey asset owner) (selectRows assets rows) =
      C.lookupLast (S.accountKey asset owner) rows := by
  rw [C.lookupLast_eq_amountAt _ _ (selectRows_unique assets rows unique),
    C.lookupLast_eq_amountAt _ _ unique, ← C.amountSum_eq_amountAt,
    ← C.amountSum_eq_amountAt]
  exact selectRows_amountSum assets rows asset owner selected

/-- A managed leaf's selected-policy model observes the actual shared rows,
including the total, even though the runtime leaf receives a filtered table. -/
theorem managed_projection_filter (release : String) (policy : M.Policy)
    (assets : List String) (rows : List AmountRow) (supply : Int)
    (selected : policy.asset ∈ assets) (unique : S.Unique rows) :
    A.project release policy (selectRows assets rows) supply =
      A.project release policy rows supply := by
  unfold A.project
  congr 1
  · funext owner
    exact selectRows_lookup assets rows policy.asset owner selected unique
  · exact selectRows_total assets rows policy.asset selected

/-- The runtime's supply-row membership filter preserves the selected numeric
lookup. This requires no uniqueness, ordering or source-image hypothesis. -/
theorem supply_filter_lookup (assets : List Asset) (rows : List SupplyRow)
    (asset : Asset) (selected : asset ∈ assets) :
    supplyFor (rows.filter (fun row => decide (row.asset ∈ assets))) asset =
      supplyFor rows asset := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases retained : row.asset ∈ assets
      · simp only [List.filter_cons, decide_eq_true retained, if_true]
        change (if row.asset = asset then row.amountAtoms else 0) +
          supplyFor (rows.filter (fun row => decide (row.asset ∈ assets))) asset = _
        rw [ih]
        rfl
      · have different : row.asset ≠ asset := fun same => retained (same ▸ selected)
        simp only [List.filter_cons, decide_eq_false retained, Bool.false_eq_true, if_false]
        change supplyFor (rows.filter (fun row => decide (row.asset ∈ assets))) asset =
          (if row.asset = asset then row.amountAtoms else 0) + _
        rw [if_neg different, Int.zero_add, ih]
        rfl

theorem full_managed_filter_projection (release : String) (policy : M.Policy)
    (assets : List Asset) (rows : List AmountRow) (supplies : List SupplyRow)
    (selected : policy.asset ∈ assets) (unique : S.Unique rows) :
    A.project release policy (selectRows assets rows)
        (supplyFor (supplies.filter (fun row => decide (row.asset ∈ assets))) policy.asset) =
      A.project release policy rows (supplyFor supplies policy.asset) := by
  rw [supply_filter_lookup assets supplies policy.asset selected]
  exact managed_projection_filter release policy assets rows _ selected unique


/-- Both leaf observations read these same physical rows and supply lookup. -/
def managedView (release : String) (policy : M.Policy) (state : GlobalState) : M.LifecycleState :=
  A.project release policy state.balances (supplyFor state.supplies policy.asset)

def transferView (release : String) (policy : T.Policy) (state : GlobalState) : T.TransferState :=
  F.project release policy state.balances (supplyFor state.supplies policy.asset)

def afterManaged (state : GlobalState) (command : M.Command) : GlobalState :=
  R.accountingPost state command.asset command.accountOwner (M.signedAmount command)

/-- Exact update of the sibling observation; other owners and assets are framed. -/
theorem managed_transfer_lookup (release : String) (policy : T.Policy)
    (pre : GlobalState) (command : M.Command) (unique : S.Unique pre.balances)
    (owner : String) :
    (transferView release policy (afterManaged pre command)).balance owner =
      if command.asset = policy.asset ∧ command.accountOwner = owner then
        (transferView release policy pre).balance owner + M.signedAmount command
      else (transferView release policy pre).balance owner := by
  exact A.updateRows_lookup pre.balances command.asset command.accountOwner _ unique policy.asset owner

theorem managed_transfer_frame (release : String) (policy : T.Policy)
    (pre : GlobalState) (keys : List Asset) (command : M.Command)
    (canonical : RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩)
    (registered : command.asset ∈ keys) (unique : S.Unique pre.balances)
    (different : command.asset ≠ policy.asset) :
    transferView release policy (afterManaged pre command) = transferView release policy pre := by
  have numeric := RegisteredSupplyViewV1.arbitrary_view_adjust_lookup
    ⟨keys, pre.supplies⟩ canonical command.asset (M.signedAmount command) registered policy.asset
  unfold transferView F.project
  congr 1
  · funext owner
    rw [show (afterManaged pre command).balances =
      A.updateRows pre.balances command.asset command.accountOwner (M.signedAmount command) from rfl]
    rw [A.updateRows_lookup _ _ _ _ unique]
    simp only [different, false_and, if_false]
  · change supplyFor (RegisteredSupplyUpdateV1.adjustSparse command.asset
        (M.signedAmount command) pre.supplies) policy.asset = _
    rw [numeric]
    simp only [Ne.symm different, if_false, Int.add_zero]
  · change amountForAsset (A.updateRows pre.balances command.asset command.accountOwner _) policy.asset = _
    rw [A.updateRows_total _ _ _ _ unique]
    simp only [different, if_false, Int.add_zero]

/-- Quantitative continuation for transfer after an accepted issue or burn.
Only asset equality is needed here; policy identity/authentication is separate. -/
theorem accepted_managed_preserves_transfer_quantities
    {pre : GlobalState} {keys : List Asset} {roots : M.RootModel} {ctx : M.Context}
    {release : String} {managedPolicy : M.Policy} {transferPolicy : T.Policy}
    {command : M.Command}
    (canonical : RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩)
    (registered : managedPolicy.asset ∈ keys) (unique : S.Unique pre.balances)
    (nonnegative : ∀ row ∈ pre.balances, 0 ≤ row.amountAtoms)
    (preAdmitted : M.StateWellFormed (managedView release managedPolicy pre))
    (commandAdmitted : M.CommandWellFormed command)
    (accepted : (M.transition roots ctx (managedView release managedPolicy pre) command).verdict = .accepted)
    (sameAsset : transferPolicy.asset = managedPolicy.asset)
    (fee : T.IsU128 transferPolicy.transferFeeAtoms) (decimals : transferPolicy.atomDecimals = 8) :
    T.StateWellFormed (transferView release transferPolicy (afterManaged pre command)) := by
  have post := R.accepted_accounting_well_formed canonical registered unique nonnegative
    preAdmitted commandAdmitted accepted
  constructor
  · intro owner
    simpa only [transferView, F.project, sameAsset, afterManaged, A.project] using post.balances owner
  · simpa only [transferView, F.project, sameAsset, afterManaged, A.project] using post.supply
  · simpa only [transferView, F.project, sameAsset, afterManaged, A.project] using post.accountTotal
  · simpa only [transferView, F.project, sameAsset, afterManaged, A.project] using post.accountCover
  · exact fee
  · exact decimals

/-- The local asset-lane constructor requires equality, stronger than global
account coverage when some holdings reside in custody or reserves. -/
def AccountsMatchSupply (state : GlobalState) : Prop :=
  ∀ asset, amountForAsset state.balances asset = supplyFor state.supplies asset

theorem afterManaged_accounts_match_supply (pre : GlobalState) (keys : List Asset)
    (command : M.Command) (canonical : RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩)
    (registered : command.asset ∈ keys) (unique : S.Unique pre.balances)
    (accounting : AccountsMatchSupply pre) : AccountsMatchSupply (afterManaged pre command) := by
  intro asset
  change amountForAsset (A.updateRows pre.balances command.asset command.accountOwner _) asset =
    supplyFor (RegisteredSupplyUpdateV1.adjustSparse command.asset _ pre.supplies) asset
  rw [A.updateRows_total _ _ _ _ unique,
    RegisteredSupplyViewV1.arbitrary_view_adjust_lookup _ canonical _ _ registered asset,
    accounting asset]
  simp only [eq_comm]

/-- Arithmetic successor only: roots/metadata are not recomputed or admitted. -/
def afterTransfer (release : String) (policy : T.Policy) (pre : GlobalState)
    (command : T.Command) : GlobalState :=
  { pre with balances := F.transferRows (transferView release policy pre) command pre.balances }

theorem transfer_managed_lookup (release : String) (transferPolicy : T.Policy)
    (managedPolicy : M.Policy) (pre : GlobalState) (command : T.Command)
    (unique : S.Unique pre.balances) (distinct : command.sender ≠ command.recipient)
    (owner : String) :
    (managedView release managedPolicy (afterTransfer release transferPolicy pre command)).balance owner =
      (managedView release managedPolicy pre).balance owner +
        (if command.asset = managedPolicy.asset then
          T.delta (transferView release transferPolicy pre) command owner else 0) := by
  exact F.transferRows_lookup _ command pre.balances unique distinct managedPolicy.asset owner

theorem transfer_managed_frame (release : String) (transferPolicy : T.Policy)
    (managedPolicy : M.Policy) (pre : GlobalState) (command : T.Command)
    (unique : S.Unique pre.balances) (distinct : command.sender ≠ command.recipient)
    (different : command.asset ≠ managedPolicy.asset) :
    managedView release managedPolicy (afterTransfer release transferPolicy pre command) =
      managedView release managedPolicy pre := by
  unfold managedView A.project
  congr 1
  · funext owner
    change C.lookupLast (S.accountKey managedPolicy.asset owner)
      (F.transferRows (transferView release transferPolicy pre) command pre.balances) = _
    rw [F.transferRows_lookup _ _ _ unique distinct]
    simp only [different, if_false, Int.add_zero]
  · exact F.transferRows_totals _ command pre.balances unique distinct managedPolicy.asset

/-- The selected transfer view is the actual accepted V2 model post. -/
theorem accepted_transfer_materialization {release : String} {policy : T.Policy}
    {pre : GlobalState} {command : T.Command} {roots : T.RootModel} {ctx : T.Context}
    (unique : S.Unique pre.balances)
    (accepted : (T.transition roots ctx (transferView release policy pre) command).verdict = .accepted) :
    transferView release policy (afterTransfer release policy pre command) =
      (T.transition roots ctx (transferView release policy pre) command).post := by
  exact (F.accepted_materialization unique accepted).symm

/-- Quantitative continuation for managed issue/burn after an accepted transfer. -/
theorem accepted_transfer_preserves_managed_quantities
    {pre : GlobalState} {roots : T.RootModel} {ctx : T.Context}
    {release : String} {transferPolicy : T.Policy} {managedPolicy : M.Policy}
    {command : T.Command} (unique : S.Unique pre.balances)
    (preAdmitted : T.StateWellFormed (transferView release transferPolicy pre))
    (accepted : (T.transition roots ctx (transferView release transferPolicy pre) command).verdict = .accepted)
    (sameAsset : transferPolicy.asset = managedPolicy.asset)
    (policyAdmitted : M.PolicyWellFormed managedPolicy) :
    M.StateWellFormed
      (managedView release managedPolicy (afterTransfer release transferPolicy pre command)) := by
  have post := F.accepted_project_well_formed unique preAdmitted accepted
  change T.StateWellFormed
    (transferView release transferPolicy (afterTransfer release transferPolicy pre command)) at post
  constructor
  · intro owner
    simpa only [managedView, A.project, transferView, F.project, sameAsset] using post.balances owner
  · simpa only [managedView, A.project, transferView, F.project, sameAsset] using post.supply
  · simpa only [managedView, A.project, transferView, F.project, sameAsset] using post.accountTotal
  · simpa only [managedView, A.project, transferView, F.project, sameAsset] using post.accountCover
  · exact policyAdmitted

theorem afterTransfer_accounts_match_supply (release : String) (policy : T.Policy)
    (pre : GlobalState) (command : T.Command) (unique : S.Unique pre.balances)
    (distinct : command.sender ≠ command.recipient) (accounting : AccountsMatchSupply pre) :
    AccountsMatchSupply (afterTransfer release policy pre command) := by
  intro asset
  change amountForAsset (F.transferRows _ command pre.balances) asset = supplyFor pre.supplies asset
  rw [F.transferRows_totals _ _ _ unique distinct]
  exact accounting asset

namespace Controls

def pre : GlobalState :=
  { staticGlobalState with
    balances := [⟨"carol", "EUR", "accounts", 7⟩]
    supplies := [⟨"EUR", 7⟩] }

def keys : List Asset := ["EUR", "ORD"]

def transferPolicy : T.Policy :=
  { AssetTransferRefinementV2.ordinaryPolicy with
    asset := "ORD", assetOriginRoot := some "origin-ord" }

def issue : M.Command :=
  { ManagedAssetLifecycleRefinementV2.issueCommand with amountAtoms := 1 }

def transfer : T.Command :=
  { AssetTransferRefinementV2.baseCommand "alice" "bob" 1 with
    asset := "ORD", assetOriginRoot := some "origin-ord" }

def transferRoots : T.RootModel := ⟨fun _ => "control-root"⟩

theorem unique : S.Unique pre.balances := by unfold S.Unique; decide

theorem canonical : RegisteredSupplyViewV1.CanonicalView ⟨keys, pre.supplies⟩ :=
  RegisteredSupplyViewV1.canonical_encode [⟨"EUR", 7⟩, ⟨"ORD", 0⟩]
    (by unfold RegisteredSupplySupportV1.SourceAssetKeysUnique; decide)
    (by unfold RegisteredSupplyUpdateV1.SourceAssetKeysOrdered; decide)

theorem account_supply_equality : AccountsMatchSupply pre := by
  intro asset
  simp [pre, amountForAsset, supplyFor]

theorem issue_accepts :
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.issueContext
      (managedView "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy pre) issue).verdict =
        .accepted := by decide

def issuedTransfer : T.TransferState :=
  ⟨"release-v2", transferPolicy, fun owner => if owner = "alice" then 1 else 0, 1, 1⟩

theorem issued_transfer_projection :
    transferView "release-v2" transferPolicy (afterManaged pre issue) = issuedTransfer := by
  unfold transferView F.project issuedTransfer
  congr 1
  · funext owner
    change C.lookupLast (S.accountKey transferPolicy.asset owner)
      (A.updateRows pre.balances issue.asset issue.accountOwner (M.signedAmount issue)) = _
    rw [A.updateRows_lookup _ _ _ _ unique]
    simp [pre, transferPolicy, issue, ManagedAssetLifecycleRefinementV2.issueCommand,
      M.signedAmount, ManagedAssetLifecycleRefinementV2.isIssue, C.lookupLast,
      S.accountKey, C.amountKey, eq_comm]
  · change amountForAsset (A.updateRows pre.balances issue.asset issue.accountOwner _) transferPolicy.asset = _
    rw [A.updateRows_total _ _ _ _ unique]
    decide

/-- Reusing the old sibling is a different outcome on a reachable model history. -/
theorem fresh_transfer_accepts_and_frozen_transfer_rejects :
    (T.transition transferRoots (AssetTransferRefinementV2.baseContext "alice")
      (transferView "release-v2" transferPolicy (afterManaged pre issue)) transfer).verdict = .accepted ∧
    (T.transition transferRoots (AssetTransferRefinementV2.baseContext "alice")
      (transferView "release-v2" transferPolicy pre) transfer).verdict =
        .rejected .insufficientBalance := by
  rw [issued_transfer_projection]
  decide

theorem wrong_owner_has_no_issued_balance :
    (transferView "release-v2" transferPolicy (afterManaged pre issue)).balance "mallory" = 0 := by
  rw [issued_transfer_projection]
  decide

theorem managed_filter_retains_selected_value_and_frames_unmanaged_rows :
    selectRows ["ORD"] pre.balances = [] ∧
      managedView "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy pre =
        A.project "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy [] 0 := by
  constructor
  · decide
  · symm
    exact managed_projection_filter _ _ ["ORD"] pre.balances 0 (by decide) unique

theorem issued_lane_accounts_match_supply : AccountsMatchSupply (afterManaged pre issue) :=
  afterManaged_accounts_match_supply pre keys issue canonical (by decide) unique account_supply_equality

end Controls

end Proofs.AssetLaneSharedProjectionV2
