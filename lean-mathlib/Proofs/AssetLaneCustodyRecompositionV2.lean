import Proofs.AssetLaneCustodyTraceV2
import Proofs.AssetLaneFiniteRecompositionV2

/-!
Connect the custody trace to the coordinator's managed-row construction:
filter the shared source for the managed leaf, retain its unmanaged complement,
and merge the complete post rows. Reuse the existing partition algebra.

The equality covers each modeled step's verdict and complete state, and the
endpoint of every admitted finite history, including zero supply identities.
Both constructions are Lean models. Runtime object/source binding, projection
rejection order, codecs, resources, roots, receipts and authority remain outside
this theorem.
-/
set_option warningAsError true

namespace Proofs.AssetLaneCustodyRecompositionV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1
open AssetLaneCustodyRefinementV2

namespace R
export AssetLaneFiniteRecompositionV2 (recomposeBalances recomposeSupplies
  selectSupplies managed_balance_recompose managed_complete_supply_recompose)
end R
namespace H
export AssetLaneSharedProjectionV2 (selectRows full_managed_filter_projection)
end H
namespace Trace
export AssetLaneCustodyTraceV2 (Action Ready step run step_preserves_rows
  step_fixed_frame run_preserves_rows)
end Trace

def managedAssets (pre : State) : List Asset :=
  pre.managedPolicies.map (fun policy => policy.asset)

def filteredView (pre : State) (policy : M.Policy) :
    ManagedAssetLifecycleRefinementV2.LifecycleState :=
  A.project pre.transferState.moduleReleaseId policy
    (H.selectRows (managedAssets pre) pre.transferState.balances)
    (supplyFor (numericRows (R.selectSupplies (managedAssets pre)
      pre.transferState.supplies)) policy.asset)

def recomposedPost (pre : State) (asset owner : String) (deltaAtoms : Int) : State :=
  { pre with transferState := { pre.transferState with
      balances := R.recomposeBalances (managedAssets pre) pre.transferState.balances
        asset owner deltaAtoms
      supplies := R.recomposeSupplies (managedAssets pre) pre.transferState.supplies
        asset deltaAtoms } }

theorem selected_supply_numeric_rows (assets : List Asset) (rows : List V1SupplyRow) :
    numericRows (R.selectSupplies assets rows) =
      (numericRows rows).filter (fun row => decide (row.asset ∈ assets)) := by
  simp [numericRows, R.selectSupplies, List.filter_map, List.filter_filter,
    Function.comp_def, toNumericRow, Bool.and_comm]

theorem filtered_view_eq {pre : State} {policy : M.Policy}
    (admitted : RowsRepresentable pre) (selectedPolicy : policy ∈ pre.managedPolicies) :
    filteredView pre policy = managedView pre policy := by
  unfold filteredView
  rw [selected_supply_numeric_rows]
  exact H.full_managed_filter_projection _ _ _ _ _
    (List.mem_map.mpr ⟨policy, selectedPolicy, rfl⟩) admitted.balanceUnique

/-- Full state equality, stronger than equality of physical or numeric totals. -/
theorem recomposed_post_eq {pre : State} {asset owner : String} {deltaAtoms : Int}
    (admitted : RowsRepresentable pre) (selected : asset ∈ managedAssets pre) :
    recomposedPost pre asset owner deltaAtoms = managedPost pre asset owner deltaAtoms := by
  have balances := R.managed_balance_recompose (managedAssets pre)
    pre.transferState.balances asset owner deltaAtoms admitted.balanceUnique
    (fun row member => (admitted.balancePositive row member).1) selected
  have supplies := R.managed_complete_supply_recompose (managedAssets pre)
    pre.transferState.supplies asset deltaAtoms admitted.supplyUnique admitted.supplyOrdered selected
  simp only [recomposedPost, managedPost, balances, supplies]

def managedStep (roots : M.RootModel) (context : M.Context) (pre : State)
    (policy : M.Policy) (command : M.Command) : M.Verdict × State :=
  match (M.transition roots context (filteredView pre policy) command).verdict with
  | .accepted => (.accepted, recomposedPost pre command.asset command.accountOwner
      (M.signedAmount command))
  | .rejected code => (.rejected code, pre)

/-- Acceptance establishes the selected command asset; rejection retains the
exact input. No premise assumes that the command will be accepted. -/
theorem managed_step_eq {roots : M.RootModel} {context : M.Context} {pre : State}
    {policy : M.Policy} {command : M.Command} (admitted : RowsRepresentable pre)
    (selectedPolicy : policy ∈ pre.managedPolicies) :
    managedStep roots context pre policy command =
      AssetLaneCustodyRefinementV2.managedStep roots context pre policy command := by
  unfold managedStep AssetLaneCustodyRefinementV2.managedStep
  rw [filtered_view_eq admitted selectedPolicy]
  cases verdict : (M.transition roots context (managedView pre policy) command).verdict with
  | accepted =>
    have selected : command.asset = policy.asset :=
      ManagedAssetLifecycleRefinementV2.accepted_authorization_guard verdict
        (code := .unknownAsset) (by decide)
    rw [recomposed_post_eq admitted
      (List.mem_map.mpr ⟨policy, selectedPolicy, selected.symm⟩)]
  | rejected _ => rfl

def step (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (pre : State) : Trace.Action → State
  | .transfer context policy command => (transferStep transferRoots context pre policy command).2
  | .managed context policy command => (managedStep managedRoots context pre policy command).2

theorem step_eq (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    {pre : State} {action : Trace.Action} (admitted : RowsRepresentable pre)
    (ready : Trace.Ready pre action) :
    step transferRoots managedRoots pre action = Trace.step transferRoots managedRoots pre action := by
  cases action with
  | transfer _ _ _ => rfl
  | managed _ _ _ => exact congrArg Prod.snd (managed_step_eq admitted ready.1)

def run (transferRoots : T.RootModel) (managedRoots : M.RootModel) :
    State → List Trace.Action → State
  | pre, [] => pre
  | pre, action :: rest => run transferRoots managedRoots
      (step transferRoots managedRoots pre action) rest

/-- Source admission is needed only initially. Existing preservation derives
every successor's premises, so mixed rejected/accepted histories also coincide. -/
theorem run_eq (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (actions : List Trace.Action) {pre : State} (admitted : RowsRepresentable pre)
    (ready : ∀ action ∈ actions, Trace.Ready pre action) :
    run transferRoots managedRoots pre actions = Trace.run transferRoots managedRoots pre actions := by
  induction actions generalizing pre with
  | nil => rfl
  | cons first rest ih =>
    simp only [run, Trace.run]
    rw [step_eq transferRoots managedRoots admitted (ready first List.mem_cons_self)]
    apply ih (Trace.step_preserves_rows transferRoots managedRoots admitted
      (ready first List.mem_cons_self))
    intro next member
    have frame := Trace.step_fixed_frame transferRoots managedRoots pre first
    have readyNext := ready next (List.mem_cons_of_mem first member)
    cases next <;> simpa only [Trace.Ready, frame.2.1, frame.2.2.2.1] using readyNext

theorem run_preserves_rows (transferRoots : T.RootModel) (managedRoots : M.RootModel)
    (actions : List Trace.Action) {pre : State} (admitted : RowsRepresentable pre)
    (ready : ∀ action ∈ actions, Trace.Ready pre action) :
    RowsRepresentable (run transferRoots managedRoots pre actions) := by
  rw [run_eq transferRoots managedRoots actions admitted ready]
  exact Trace.run_preserves_rows transferRoots managedRoots actions admitted ready

end Proofs.AssetLaneCustodyRecompositionV2
