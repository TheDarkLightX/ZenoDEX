import Proofs.ManagedAssetFiniteAccountingV2
import Proofs.RegisteredSupplyViewV1

/-!
# Constructed registered physical accounting and accepted-leaf relation

This is a physical-accounting projection: only balances and supplies change;
actual custody and reserves remain in the owned equation. Claimant liabilities
are not additional physical holdings. Existing roots and metadata are copied;
their global-successor validity is outside this physical projection.

All numeric supply keys must be covered by the input carried keys. A wider
global state with uncovered assets is outside this theorem's domain; no rows
are silently discarded. This construction grants no authentication, resource,
receipt, complete coordinator, publisher, or universal runtime refinement claim.
-/

set_option warningAsError true

namespace Proofs.ManagedAssetRegisteredAccountingV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
  RegisteredSupplySupportV1 RegisteredSupplyUpdateV1 RegisteredSupplyViewV1
  ManagedAssetFiniteAccountingV2

def accountingPost (pre : GlobalState) (asset owner : String) (deltaAtoms : Int) : GlobalState :=
  { pre with balances := updateRows pre.balances asset owner deltaAtoms
             supplies := adjustSparse asset deltaAtoms pre.supplies }

/-- Matched physical balance and supply updates preserve ownership for every
asset, including all unchanged custody and reserves. -/
theorem accountingPost_owned (pre : GlobalState) (keys : List Asset)
    (asset owner : String) (deltaAtoms : Int)
    (canonical : CanonicalView ⟨keys, pre.supplies⟩) (registered : asset ∈ keys)
    (unique : S.Unique pre.balances) (owned : OwnedMatchesSupply pre) :
    OwnedMatchesSupply (accountingPost pre asset owner deltaAtoms) := by
  intro other
  have numeric := arbitrary_view_adjust_lookup ⟨keys, pre.supplies⟩ canonical
    asset deltaAtoms registered other
  dsimp only at numeric
  have previous := owned other
  unfold ownedFor at previous
  change amountForAsset (updateRows pre.balances asset owner deltaAtoms) other +
    amountForAsset pre.custody other + amountForAsset pre.reserves other =
      supplyFor (adjustSparse asset deltaAtoms pre.supplies) other
  rw [updateRows_total pre.balances asset owner deltaAtoms unique other, numeric]
  have sameDelta : (if asset = other then deltaAtoms else 0) =
      (if other = asset then deltaAtoms else 0) := by simp only [eq_comm]
  rw [sameDelta]
  omega

/-- The computed physical post retains covered canonical support and the
complete zero-inclusive identities under the unchanged carried keys. -/
theorem accountingPost_support (pre : GlobalState) (keys : List Asset)
    (asset owner : String) (deltaAtoms : Int)
    (canonical : CanonicalView ⟨keys, pre.supplies⟩) (registered : asset ∈ keys) :
    CanonicalView ⟨keys, (accountingPost pre asset owner deltaAtoms).supplies⟩ ∧
      numericRows (adjustComplete asset deltaAtoms (decode ⟨keys, pre.supplies⟩)) =
        (accountingPost pre asset owner deltaAtoms).supplies ∧
      decode ⟨keys, (accountingPost pre asset owner deltaAtoms).supplies⟩ =
        adjustComplete asset deltaAtoms (decode ⟨keys, pre.supplies⟩) ∧
      (decode ⟨keys, (accountingPost pre asset owner deltaAtoms).supplies⟩).map
        V1SupplyRow.asset = keys := by
  exact ⟨arbitrary_view_adjust_canonical _ canonical asset deltaAtoms registered,
    arbitrary_view_adjust_commutes _ canonical asset deltaAtoms registered,
    arbitrary_view_adjust_roundtrip _ canonical asset deltaAtoms registered,
    decode_registered_keys_exact _⟩

/-- The actual accepted guard selects the policy asset; the independently
computed physical post projects to the actual selected-policy leaf post. -/
theorem accepted_accounting_materialization {pre : GlobalState} {keys : List Asset}
    {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy}
    {command : M.Command} (canonical : CanonicalView ⟨keys, pre.supplies⟩)
    (registered : policy.asset ∈ keys) (unique : S.Unique pre.balances)
    (accepted : (M.transition roots ctx
      (project release policy pre.balances (supplyFor pre.supplies policy.asset)) command).verdict =
        .accepted) :
    project release policy
        (accountingPost pre command.asset command.accountOwner (M.signedAmount command)).balances
        (supplyFor (accountingPost pre command.asset command.accountOwner
          (M.signedAmount command)).supplies policy.asset) =
      (M.transition roots ctx
        (project release policy pre.balances (supplyFor pre.supplies policy.asset)) command).post := by
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  have member : command.asset ∈ keys := selected ▸ registered
  have numeric := arbitrary_view_adjust_lookup ⟨keys, pre.supplies⟩ canonical
    command.asset (M.signedAmount command) member policy.asset
  rw [accepted_materialization unique accepted]
  change project release policy (updateRows pre.balances command.asset command.accountOwner _)
      (supplyFor (adjustSparse command.asset (M.signedAmount command) pre.supplies) policy.asset) = _
  rw [numeric]
  simp only [selected, if_true]

theorem accepted_accounting_owned {pre : GlobalState} {keys : List Asset}
    {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy}
    {command : M.Command} (canonical : CanonicalView ⟨keys, pre.supplies⟩)
    (registered : policy.asset ∈ keys) (unique : S.Unique pre.balances)
    (owned : OwnedMatchesSupply pre)
    (accepted : (M.transition roots ctx
      (project release policy pre.balances (supplyFor pre.supplies policy.asset)) command).verdict =
        .accepted) :
    OwnedMatchesSupply
      (accountingPost pre command.asset command.accountOwner (M.signedAmount command)) := by
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  exact accountingPost_owned pre keys command.asset command.accountOwner _ canonical
    (selected ▸ registered) unique owned

/-- Existing accepted finite-row bounds transfer to the computed physical
projection through materialization; no successor admission is assumed. -/
theorem accepted_accounting_well_formed {pre : GlobalState} {keys : List Asset}
    {roots : M.RootModel} {ctx : M.Context} {release : String} {policy : M.Policy}
    {command : M.Command} (canonical : CanonicalView ⟨keys, pre.supplies⟩)
    (registered : policy.asset ∈ keys) (unique : S.Unique pre.balances)
    (nonnegative : ∀ row ∈ pre.balances, 0 ≤ row.amountAtoms)
    (preAdmitted : M.StateWellFormed
      (project release policy pre.balances (supplyFor pre.supplies policy.asset)))
    (commandAdmitted : M.CommandWellFormed command)
    (accepted : (M.transition roots ctx
      (project release policy pre.balances (supplyFor pre.supplies policy.asset)) command).verdict =
        .accepted) :
    M.StateWellFormed (project release policy
      (accountingPost pre command.asset command.accountOwner (M.signedAmount command)).balances
      (supplyFor (accountingPost pre command.asset command.accountOwner
        (M.signedAmount command)).supplies policy.asset)) := by
  rw [accepted_accounting_materialization canonical registered unique accepted]
  exact accepted_preserves_state_well_formed unique nonnegative preAdmitted commandAdmitted accepted

/-! ## Physical frames, accepted model controls, and conservation falsifiers -/

def controlKeys : List Asset := ["AUD", "EUR", "ORD"]

def controlPre : GlobalState :=
  { staticGlobalState with
    balances := ManagedAssetFiniteAccountingV2.exampleRows
    supplies := [⟨"EUR", 7⟩, ⟨"ORD", 4⟩]
    custody := [⟨"vault", "ORD", "custody", 1⟩]
    reserves := [⟨"reserve", "ORD", "reserves", 2⟩] }

theorem control_canonical : CanonicalView ⟨controlKeys, controlPre.supplies⟩ :=
  canonical_encode [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 4⟩]
    (by unfold SourceAssetKeysUnique; decide) (by unfold SourceAssetKeysOrdered; decide)

theorem control_unique : S.Unique controlPre.balances := by unfold S.Unique; decide

theorem control_owned : OwnedMatchesSupply controlPre := by
  intro asset
  by_cases ordinary : asset = "ORD"
  · subst asset; decide
  · by_cases euro : asset = "EUR"
    · subst asset; decide
    · simp [ownedFor, amountForAsset, supplyFor, controlPre,
        ManagedAssetFiniteAccountingV2.exampleRows, Ne.symm ordinary, Ne.symm euro]

def controlIssue : M.Command :=
  { ManagedAssetLifecycleRefinementV2.issueCommand with amountAtoms := 1 }

theorem control_leaf_pre_well_formed : M.StateWellFormed
    (project "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy controlPre.balances
      (supplyFor controlPre.supplies "ORD")) :=
  ManagedAssetFiniteAccountingV2.example_pre_well_formed

theorem issue_and_burn_acceptance_control :
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.issueContext
      (project "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy controlPre.balances
        (supplyFor controlPre.supplies "ORD")) controlIssue).verdict = .accepted ∧
    (M.transition ManagedAssetLifecycleRefinementV2.lifecycleRoots
      ManagedAssetLifecycleRefinementV2.burnContext
      (project "release-v2" ManagedAssetLifecycleRefinementV2.ordinaryPolicy controlPre.balances
        (supplyFor controlPre.supplies "ORD")) ManagedAssetFiniteAccountingV2.exampleBurn).verdict =
          .accepted := by
  decide

theorem matched_issue_burn_owned_control :
    OwnedMatchesSupply (accountingPost controlPre "ORD" "alice" 1) ∧
      OwnedMatchesSupply (accountingPost controlPre "ORD" "bob" (-1)) := by
  exact ⟨accountingPost_owned controlPre controlKeys "ORD" "alice" 1 control_canonical
      (by decide) control_unique control_owned,
    accountingPost_owned controlPre controlKeys "ORD" "bob" (-1) control_canonical
      (by decide) control_unique control_owned⟩

theorem nonzero_custody_reserves_and_dormant_identity_control :
    amountForAsset controlPre.custody "ORD" = 1 ∧
      amountForAsset controlPre.reserves "ORD" = 2 ∧
      amountForAsset controlPre.balances "EUR" = 7 ∧
      amountForAsset (accountingPost controlPre "ORD" "bob" (-1)).balances "EUR" = 7 ∧
      decode ⟨controlKeys, (accountingPost controlPre "ORD" "bob" (-1)).supplies⟩ =
        [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"ORD", 3⟩] ∧
      (accountingPost controlPre "ORD" "bob" (-1)).custody = controlPre.custody ∧
      (accountingPost controlPre "ORD" "bob" (-1)).reserves = controlPre.reserves := by
  have euro : amountForAsset (accountingPost controlPre "ORD" "bob" (-1)).balances "EUR" = 7 := by
    change amountForAsset (updateRows controlPre.balances "ORD" "bob" (-1)) "EUR" = 7
    rw [updateRows_total controlPre.balances "ORD" "bob" (-1) control_unique "EUR"]
    decide
  exact ⟨by decide, by decide, by decide, euro, by decide, by decide, by decide⟩

theorem mismatched_delta_falsifies_owned_control :
    ¬ OwnedMatchesSupply
      { controlPre with balances := updateRows controlPre.balances "ORD" "bob" 1
                        supplies := adjustSparse "ORD" 2 controlPre.supplies } := by
  intro owned
  have actual := owned "ORD"
  have accounts := updateRows_total controlPre.balances "ORD" "bob" 1 control_unique "ORD"
  change amountForAsset (updateRows controlPre.balances "ORD" "bob" 1) "ORD" + 1 + 2 = 6
    at actual
  rw [accounts] at actual
  change (1 + 1 : Int) + 1 + 2 = 6 at actual
  omega

theorem lost_custody_falsifies_owned_control :
    ¬ OwnedMatchesSupply { accountingPost controlPre "ORD" "bob" (-1) with custody := [] } := by
  intro owned
  have actual := owned "ORD"
  have accounts := updateRows_total controlPre.balances "ORD" "bob" (-1) control_unique "ORD"
  change amountForAsset (updateRows controlPre.balances "ORD" "bob" (-1)) "ORD" + 0 + 2 = 3
    at actual
  rw [accounts] at actual
  change (1 + -1 : Int) + 0 + 2 = 3 at actual
  omega

end Proofs.ManagedAssetRegisteredAccountingV2
