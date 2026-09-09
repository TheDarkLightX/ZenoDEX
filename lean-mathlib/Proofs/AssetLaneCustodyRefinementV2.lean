import Proofs.AssetTransferFiniteAccountingV2
import Proofs.ManagedAssetRegisteredAccountingV2

/-!
# Finite-row lift for the custody-capable ABI V2 asset lane

`State` observes `AssetLaneCustodyStateV2`: `transferState` observes the existing
`transfer_state` module release, policy list, balance rows and complete supply
rows; `originRegistry` observes its ordered asset keys; `managedPolicies` and
`custody` observe the corresponding lists. Supply amounts and physical totals
are derived from these rows, never supplied as independent observations.

The origin registry's remaining fields, policy authentication, resource limits,
canonical bytes/roots, completed journals and outer coordinator rejection are
outside this projection. The selected V2 leaf model owns authorization and its
rejection order. This file proves a constructed row lift, not universal Python,
Rust, codec, guest, global admission or publication refinement. The zero-retaining
formal supply carrier is reused for its row algebra, without a wire conversion.
-/

set_option warningAsError true

namespace Proofs.AssetLaneCustodyRefinementV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

namespace T
export AssetTransferRefinementV2 (Policy Command Context RootModel Verdict transition
  rejected_effects_empty ordinaryPolicy baseCommand baseContext EffectEnvelope)
end T
namespace M
export ManagedAssetLifecycleRefinementV2 (Policy Command Context RootModel Verdict transition
  signedAmount rejected_effects_empty ordinaryPolicy issueCommand issueContext burnCommand
  contextFor occurrence burnCommandKind lifecycleRoots)
end M
namespace A
export ManagedAssetFiniteAccountingV2 (updateRows updateRows_total project)
end A
namespace F
export AssetTransferFiniteAccountingV2 (project transferRows transferRows_totals
  accepted_distinct accepted_selected_asset)
end F
namespace S
export AssetTransferSparseTablesV1 (Unique PositiveAccounts accounts)
end S

structure TransferRows where
  moduleReleaseId : String
  policies : List T.Policy
  balances : List AmountRow
  supplies : List V1SupplyRow
  deriving DecidableEq, Repr

structure State where
  transferState : TransferRows
  originRegistry : List Asset
  managedPolicies : List M.Policy
  custody : List AmountRow
  deriving DecidableEq, Repr

def physicalFor (state : State) (asset : Asset) : Int :=
  amountForAsset state.transferState.balances asset + amountForAsset state.custody asset

def supplyAt (state : State) (asset : Asset) : Int :=
  supplyFor (numericRows state.transferState.supplies) asset

def PhysicalBalanced (state : State) : Prop :=
  ∀ asset, physicalFor state asset = supplyAt state asset

/-- Input-only representation conditions. This does not assert leaf acceptance. -/
structure RowsRepresentable (state : State) : Prop where
  supplyUnique : SourceAssetKeysUnique state.transferState.supplies
  supplyOrdered : SourceAssetKeysOrdered state.transferState.supplies
  supplyBounded : SourceRowsU128 state.transferState.supplies
  registryKeys : state.originRegistry = state.transferState.supplies.map V1SupplyRow.asset
  policyKeys : state.transferState.policies.map (fun policy => policy.asset) = state.originRegistry
  managedCovered : ∀ policy ∈ state.managedPolicies, policy.asset ∈ state.originRegistry
  balanceUnique : S.Unique state.transferState.balances
  balancePositive : S.PositiveAccounts state.transferState.balances
  custodyUnique : S.Unique state.custody
  custodyShape : ∀ row ∈ state.custody,
    row.custodyDomain ≠ S.accounts ∧ 0 < row.amountAtoms ∧ FitsU128 row.amountAtoms
  holdingsCovered : ∀ row ∈ state.transferState.balances ++ state.custody,
    row.asset ∈ state.originRegistry
  balanced : PhysicalBalanced state

def transferView (state : State) (policy : T.Policy) : AssetTransferRefinementV2.TransferState :=
  F.project state.transferState.moduleReleaseId policy state.transferState.balances
    (supplyAt state policy.asset)

def managedView (state : State) (policy : M.Policy) : ManagedAssetLifecycleRefinementV2.LifecycleState :=
  A.project state.transferState.moduleReleaseId policy state.transferState.balances
    (supplyAt state policy.asset)

def transferPost (state : State) (policy : T.Policy) (command : T.Command) : State :=
  { state with transferState := { state.transferState with
      balances := F.transferRows (transferView state policy) command state.transferState.balances } }

def managedPost (state : State) (asset owner : String) (deltaAtoms : Int) : State :=
  { state with transferState := { state.transferState with
      balances := A.updateRows state.transferState.balances asset owner deltaAtoms
      supplies := adjustComplete asset deltaAtoms state.transferState.supplies } }

/-- Project exact lane rows into an independently supplied global frame. -/
def globalView (state : State) (frame : GlobalState) : GlobalState :=
  { frame with balances := state.transferState.balances
               supplies := numericRows state.transferState.supplies
               custody := state.custody }

/-- The complete-row successor projects to the existing sparse global update;
all global frame fields, including claimant liability rows, are retained. -/
theorem managed_global_projection (pre : State) (frame : GlobalState)
    (asset owner : String) (deltaAtoms : Int)
    (unique : SourceAssetKeysUnique pre.transferState.supplies)
    (ordered : SourceAssetKeysOrdered pre.transferState.supplies)
    (registered : asset ∈ pre.transferState.supplies.map V1SupplyRow.asset) :
    globalView (managedPost pre asset owner deltaAtoms) frame =
      ManagedAssetRegisteredAccountingV2.accountingPost (globalView pre frame)
        asset owner deltaAtoms := by
  unfold globalView managedPost ManagedAssetRegisteredAccountingV2.accountingPost
  simp only
  rw [registered_supply_adjust_commutes _ asset deltaAtoms unique ordered registered]

/-- Physical conservation follows from actual account-row and complete-supply
updates for every asset. The signed delta covers both issue and burn. -/
theorem managed_physical_lift (pre : State) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique pre.transferState.balances)
    (supplyUnique : SourceAssetKeysUnique pre.transferState.supplies)
    (registered : asset ∈ pre.transferState.supplies.map V1SupplyRow.asset)
    (balanced : PhysicalBalanced pre) :
    PhysicalBalanced (managedPost pre asset owner deltaAtoms) ∧
      (managedPost pre asset owner deltaAtoms).custody = pre.custody ∧
      (managedPost pre asset owner deltaAtoms).transferState.supplies.map V1SupplyRow.asset =
        pre.transferState.supplies.map V1SupplyRow.asset := by
  constructor
  · intro query
    change amountForAsset (A.updateRows pre.transferState.balances asset owner deltaAtoms) query +
        amountForAsset pre.custody query =
      supplyFor (numericRows (adjustComplete asset deltaAtoms pre.transferState.supplies)) query
    rw [A.updateRows_total _ asset owner deltaAtoms unique query,
      adjustComplete_lookup _ asset deltaAtoms supplyUnique registered query]
    have prior := balanced query
    dsimp only [physicalFor, supplyAt] at prior
    by_cases selected : asset = query
    · subst query; simp only [if_true]; omega
    · simp only [if_neg selected, if_neg (Ne.symm selected), Int.add_zero]
      exact prior
  · exact ⟨rfl, adjustComplete_keys asset deltaAtoms pre.transferState.supplies⟩

theorem transfer_physical_lift (pre : State) (policy : T.Policy) (command : T.Command)
    (unique : S.Unique pre.transferState.balances)
    (distinct : command.sender ≠ command.recipient) (balanced : PhysicalBalanced pre) :
    PhysicalBalanced (transferPost pre policy command) ∧
      (transferPost pre policy command).custody = pre.custody ∧
      (transferPost pre policy command).transferState.supplies = pre.transferState.supplies := by
  constructor
  · intro asset
    change amountForAsset (F.transferRows (transferView pre policy) command
        pre.transferState.balances) asset + amountForAsset pre.custody asset = supplyAt pre asset
    rw [F.transferRows_totals _ command _ unique distinct]
    exact balanced asset
  · exact ⟨rfl, rfl⟩

def transferStep (roots : T.RootModel) (context : T.Context) (pre : State)
    (policy : T.Policy) (command : T.Command) : T.Verdict × State :=
  match (T.transition roots context (transferView pre policy) command).verdict with
  | .accepted => (.accepted, transferPost pre policy command)
  | .rejected code => (.rejected code, pre)

def managedStep (roots : M.RootModel) (context : M.Context) (pre : State)
    (policy : M.Policy) (command : M.Command) : M.Verdict × State :=
  match (M.transition roots context (managedView pre policy) command).verdict with
  | .accepted => (.accepted, managedPost pre command.asset command.accountOwner (M.signedAmount command))
  | .rejected code => (.rejected code, pre)

/-- The selected transfer's actual guards justify the row lift and the exact
selected-policy post observation; no successor totals are premises. -/
theorem accepted_transfer_lift {roots : T.RootModel} {context : T.Context} {pre : State}
    {policy : T.Policy} {command : T.Command} (admitted : RowsRepresentable pre)
    (accepted : (T.transition roots context (transferView pre policy) command).verdict = .accepted) :
    transferView (transferStep roots context pre policy command).2 policy =
      (T.transition roots context (transferView pre policy) command).post ∧
    PhysicalBalanced (transferStep roots context pre policy command).2 ∧
    (transferStep roots context pre policy command).2.custody = pre.custody ∧
    (transferStep roots context pre policy command).2.transferState.supplies =
      pre.transferState.supplies := by
  simp only [transferStep, accepted]
  constructor
  · exact (AssetTransferFiniteAccountingV2.accepted_materialization admitted.balanceUnique accepted).symm
  · exact transfer_physical_lift pre policy command admitted.balanceUnique
      (F.accepted_distinct accepted) admitted.balanced

/-- A selected managed policy and the actual unknown-asset guard establish
registered membership. Existing finite materialization supplies the exact post. -/
theorem accepted_managed_lift {roots : M.RootModel} {context : M.Context} {pre : State}
    {policy : M.Policy} {command : M.Command} (admitted : RowsRepresentable pre)
    (selectedPolicy : policy ∈ pre.managedPolicies)
    (accepted : (M.transition roots context (managedView pre policy) command).verdict = .accepted) :
    managedView (managedStep roots context pre policy command).2 policy =
      (M.transition roots context (managedView pre policy) command).post ∧
    PhysicalBalanced (managedStep roots context pre policy command).2 ∧
    (managedStep roots context pre policy command).2.custody = pre.custody ∧
    (managedStep roots context pre policy command).2.transferState.supplies.map V1SupplyRow.asset =
      pre.transferState.supplies.map V1SupplyRow.asset := by
  have selected : command.asset = policy.asset :=
    ManagedAssetLifecycleRefinementV2.accepted_authorization_guard accepted
      (code := .unknownAsset) (by decide)
  have registered : command.asset ∈ pre.transferState.supplies.map V1SupplyRow.asset := by
    rw [selected, ← admitted.registryKeys]
    exact admitted.managedCovered policy selectedPolicy
  simp only [managedStep, accepted]
  constructor
  · change A.project pre.transferState.moduleReleaseId policy
        (A.updateRows pre.transferState.balances command.asset command.accountOwner (M.signedAmount command))
        (supplyFor (numericRows (adjustComplete command.asset (M.signedAmount command)
          pre.transferState.supplies)) policy.asset) = _
    rw [adjustComplete_lookup _ command.asset (M.signedAmount command) admitted.supplyUnique
      registered policy.asset, if_pos selected.symm]
    exact (ManagedAssetFiniteAccountingV2.accepted_materialization admitted.balanceUnique accepted).symm
  · exact managed_physical_lift pre command.asset command.accountOwner (M.signedAmount command)
      admitted.balanceUnique admitted.supplyUnique registered admitted.balanced

theorem rejected_transfer_noop {roots : T.RootModel} {context : T.Context} {pre : State}
    {policy : T.Policy} {command : T.Command} {code : AssetTransferRefinementV2.RejectCode}
    (rejected : (T.transition roots context (transferView pre policy) command).verdict = .rejected code) :
    transferStep roots context pre policy command = (.rejected code, pre) ∧
      (T.transition roots context (transferView pre policy) command).effects =
        Proofs.AssetTransferRefinementV2.EffectEnvelope.empty := by
  exact ⟨by simp [transferStep, rejected], T.rejected_effects_empty rejected⟩

theorem rejected_managed_noop {roots : M.RootModel} {context : M.Context} {pre : State}
    {policy : M.Policy} {command : M.Command} {code : ManagedAssetLifecycleRefinementV2.RejectCode}
    (rejected : (M.transition roots context (managedView pre policy) command).verdict = .rejected code) :
    managedStep roots context pre policy command = (.rejected code, pre) ∧
      (M.transition roots context (managedView pre policy) command).effects =
        Proofs.AssetTransferRefinementV2.EffectEnvelope.empty := by
  exact ⟨by simp [managedStep, rejected], M.rejected_effects_empty rejected⟩

namespace Controls

def policy : T.Policy :=
  { T.ordinaryPolicy with asset := "ORD", assetOriginRoot := some "origin-ord", transferFeeAtoms := 2 }

def pre : State :=
  { transferState := ⟨"release-v2",
      [{ policy with asset := "AUD" }, { policy with asset := "EUR" }, policy],
      [⟨"dave", "EUR", "accounts", 7⟩, ⟨"alice", "ORD", "accounts", 100⟩,
        ⟨"bob", "ORD", "accounts", 15⟩],
      [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 120⟩]⟩
    originRegistry := ["AUD", "EUR", "ORD"]
    managedPolicies := [M.ordinaryPolicy]
    custody := [⟨"vault", "ORD", "escrow", 5⟩] }

theorem legal_custody_state_representable : RowsRepresentable pre := by
  constructor
  · unfold SourceAssetKeysUnique; decide
  · unfold SourceAssetKeysOrdered; decide
  · simp [SourceRowsU128, pre, FitsU128, maxU128]
  · rfl
  · rfl
  · decide
  · unfold S.Unique; decide
  · simp [S.PositiveAccounts, pre, S.accounts, AssetTransferRefinementV1.IsU128,
      AssetTransferRefinementV1.u128Max]
  · unfold S.Unique; decide
  · simp [pre, S.accounts, FitsU128, maxU128]
  · decide
  · intro asset
    by_cases ordinary : asset = "ORD"
    · subst asset; decide
    · by_cases euro : asset = "EUR"
      · subst asset; decide
      · simp [physicalFor, supplyAt, pre, amountForAsset, numericRows,
          nonzeroRow, toNumericRow, supplyFor, Ne.symm ordinary, Ne.symm euro]

/-- The required source is excluded by the historical accounts-only invariant. -/
theorem accounts_only_excludes_legal_state :
    amountForAsset pre.transferState.balances "ORD" = 115 ∧ supplyAt pre "ORD" = 120 ∧
      physicalFor pre "ORD" = 120 := by decide

def transfer : T.Command :=
  { T.baseCommand "alice" "bob" 10 with
    asset := "ORD"
    assetOriginRoot := some "origin-ord"
    maxFeeAtoms := 2 }

def issue : M.Command := { M.issueCommand with amountAtoms := 7 }
def burn : M.Command := { M.burnCommand with accountOwner := "alice", amountAtoms := 7 }
def burnContext : M.Context :=
  M.contextFor (M.occurrence M.burnCommandKind "burn-body" "alice" "burn-grant" "occ-burn")
def roots : T.RootModel := ⟨fun _ => "abstract-custody-root"⟩

/-- Three actual V2 leaf guards accept a legal source with nonzero custody. -/
theorem legal_custody_commands_accept :
    (transferStep roots (T.baseContext "alice") pre policy transfer).1 = .accepted ∧
    (managedStep M.lifecycleRoots M.issueContext pre M.ordinaryPolicy issue).1 = .accepted ∧
    (managedStep M.lifecycleRoots burnContext pre M.ordinaryPolicy burn).1 = .accepted := by decide

/-- Zero retained supply is legal, and complete-key support survives issue and
full burn even when its numeric global row disappears. -/
def dormant : State :=
  { pre with
    transferState := { pre.transferState with
      balances := []
      supplies := [⟨"AUD", 0⟩, ⟨"EUR", 0⟩, ⟨"ORD", 0⟩] }
    custody := [] }

theorem dormant_state_representable : RowsRepresentable dormant := by
  constructor
  · unfold SourceAssetKeysUnique; decide
  · unfold SourceAssetKeysOrdered; decide
  · simp [SourceRowsU128, dormant, FitsU128, maxU128]
  · rfl
  · rfl
  · decide
  · unfold S.Unique; decide
  · simp [S.PositiveAccounts, dormant]
  · unfold S.Unique; decide
  · simp [dormant]
  · decide
  · intro asset
    simp [physicalFor, supplyAt, dormant, amountForAsset, numericRows, nonzeroRow, supplyFor]

theorem dormant_issue_burn_support :
    (managedStep M.lifecycleRoots M.issueContext dormant M.ordinaryPolicy issue).1 = .accepted ∧
    (managedStep M.lifecycleRoots burnContext (managedPost dormant "ORD" "alice" 7)
      M.ordinaryPolicy burn).1 = .accepted ∧
    (managedPost (managedPost dormant "ORD" "alice" 7) "ORD" "alice" (-7)).transferState.supplies =
      dormant.transferState.supplies ∧
    numericRows dormant.transferState.supplies = [] ∧
    dormant.originRegistry = ["AUD", "EUR", "ORD"] := by
  have issuedBalances : A.updateRows [] "ORD" "alice" 7 = [⟨"alice", "ORD", "accounts", 7⟩] := by
    simp [A.updateRows, CanonicalEpochEconomicRowsV1.lookupLast,
      AssetTransferSparseTablesV1.accountKey, AssetTransferSparseTablesV1.putAmount,
      AssetTransferSparseTablesV1.makeAmount, AssetTransferSparseTablesV1.eraseKey,
      S.accounts, CanonicalEpochEconomicRowsV1.sortOn]
  constructor
  · decide
  · constructor
    · simp only [managedPost, dormant, issuedBalances]
      decide
    · exact ⟨by decide, by decide, rfl⟩

/-- Keeping the scalar total while changing its custody owner violates the
required full-row frame. Dropping custody violates physical conservation. -/
theorem custody_substitution_and_deletion_detected :
    [({ owner := "mallory", asset := "ORD", custodyDomain := "escrow", amountAtoms := 5 } : AmountRow)]
      ≠ pre.custody ∧
    physicalFor { pre with custody := [] } "ORD" ≠ supplyAt pre "ORD" := by decide

end Controls
end Proofs.AssetLaneCustodyRefinementV2
