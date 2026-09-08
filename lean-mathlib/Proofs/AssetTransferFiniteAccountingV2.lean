import Proofs.ManagedAssetFiniteAccountingV2

/-!
# V2 transfer materialization from finite account rows

Balances and the selected account total are observations of one finite table.
The actual V2 aggregated deltas are applied once per distinct V2 role, including
fee-owner aliases. This is a pure arithmetic construction; validation and reject
scan order remain owned by the actual V2 transition. V1-labelled helpers supply
integer table algebra only. Row ceilings, parser/codec and Unicode collation
correspondence, authentic roots, and global runtime refinement are external.
-/
set_option warningAsError true

namespace Proofs.AssetTransferFiniteAccountingV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace F
export Proofs.ManagedAssetFiniteAccountingV2 (updateRows updateRows_unique
  updateRows_lookup updateRows_total updateRows_positive)
end F
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (lookupLast amountKey sortOn sortOn_perm)
end C
namespace S
export Proofs.AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey balanceWire)
end S
namespace T
export Proofs.AssetTransferRefinementV2 (TransferState Policy Command RootModel Context
  StateWellFormed IsU128 transition acceptedState accepted_post_and_effects
  accepted_pre_balance_guard accepted_balances_u128 accepted_balance_eq
  indicator delta postBalance roleOrder insertPrincipal sortPrincipals orderedRoles
  mem_insert_principal mem_sort_principals sender_mem_ordered_roles
  recipient_mem_ordered_roles fee_owner_mem_ordered_roles delta_untouched
  sumOver occ sumOver_delta)
end T

attribute [local instance] lexOrd

def project (moduleReleaseId : String) (policy : T.Policy)
    (rows : List AmountRow) (supplyAtoms : Int) : T.TransferState :=
  ⟨moduleReleaseId, policy, fun owner => C.lookupLast (S.accountKey policy.asset owner) rows,
    supplyAtoms, amountForAsset rows policy.asset⟩

/-- Tail-first arithmetic fold; unique keys make each role's update independent. -/
def updateRoles (rows : List AmountRow) (asset : String) (delta : String → Int) :
    List String → List AmountRow
  | [] => rows
  | owner :: rest => F.updateRows (updateRoles rows asset delta rest) asset owner (delta owner)

def transferRows (pre : T.TransferState) (command : T.Command)
    (rows : List AmountRow) : List AmountRow :=
  updateRoles rows command.asset (T.delta pre command) (T.orderedRoles pre command)

theorem insert_principal_unique (owner : String) (roles : List String)
    (unique : roles.Nodup) (absent : owner ∉ roles) :
    (T.insertPrincipal owner roles).Nodup := by
  induction roles with
  | nil => simp [T.insertPrincipal]
  | cons head rest ih =>
      have parts := List.nodup_cons.mp unique
      have missing : owner ≠ head ∧ owner ∉ rest := by simpa using absent
      by_cases before : owner ≤ head
      · simpa [T.insertPrincipal, before] using List.nodup_cons.mpr ⟨absent, unique⟩
      · simp only [T.insertPrincipal, if_neg before]
        apply List.nodup_cons.mpr
        constructor
        · rw [T.mem_insert_principal]
          exact fun member => member.elim (fun same => missing.1 same.symm) parts.1
        · exact ih parts.2 missing.2

theorem sort_principals_unique (roles : List String) (unique : roles.Nodup) :
    (T.sortPrincipals roles).Nodup := by
  induction roles with
  | nil => simp [T.sortPrincipals]
  | cons head rest ih =>
      have parts := List.nodup_cons.mp unique
      apply insert_principal_unique head (T.sortPrincipals rest) (ih parts.2)
      simpa only [T.mem_sort_principals] using parts.1

theorem ordered_roles_unique (pre : T.TransferState) (command : T.Command)
    (distinct : command.sender ≠ command.recipient) :
    (T.orderedRoles pre command).Nodup := by
  apply sort_principals_unique
  unfold T.roleOrder
  split
  · simpa using distinct
  · rename_i separate
    have sender : command.sender ≠ pre.policy.feeOwner :=
      fun same => separate (Or.inl same.symm)
    have recipient : command.recipient ≠ pre.policy.feeOwner :=
      fun same => separate (Or.inr same.symm)
    simp [distinct, sender, recipient]

theorem insert_principal_ordered (owner : String) (roles : List String)
    (ordered : roles.Pairwise (· ≤ ·)) :
    (T.insertPrincipal owner roles).Pairwise (· ≤ ·) := by
  induction roles with
  | nil => simp [T.insertPrincipal]
  | cons head rest ih =>
      have parts := List.pairwise_cons.mp ordered
      by_cases before : owner ≤ head
      · rw [T.insertPrincipal, if_pos before]
        apply List.pairwise_cons.mpr
        constructor
        · intro next member
          rcases List.mem_cons.mp member with rfl | later
          · exact before
          · exact String.le_trans before (parts.1 next later)
        · exact ordered
      · rw [T.insertPrincipal, if_neg before]
        apply List.pairwise_cons.mpr
        constructor
        · intro next member
          rcases (T.mem_insert_principal next owner rest).mp member with same | later
          · rw [same]
            exact (String.le_total owner head).resolve_left before
          · exact parts.1 next later
        · exact ih parts.2

theorem ordered_roles_ordered (pre : T.TransferState) (command : T.Command) :
    (T.orderedRoles pre command).Pairwise (· ≤ ·) := by
  have sorted : ∀ roles : List String, (T.sortPrincipals roles).Pairwise (· ≤ ·) := by
    intro roles
    induction roles with
    | nil => simp [T.sortPrincipals]
    | cons head rest ih => exact insert_principal_ordered head _ ih
  exact sorted _

theorem occ_zero (owner : String) (roles : List String) (absent : owner ∉ roles) :
    T.occ owner roles = 0 := by
  induction roles with
  | nil => rfl
  | cons head rest ih =>
      have missing : owner ≠ head ∧ owner ∉ rest := by simpa using absent
      simp only [T.occ, if_neg (Ne.symm missing.1), ih missing.2, Int.add_zero]

theorem occ_one (owner : String) (roles : List String) (unique : roles.Nodup)
    (member : owner ∈ roles) : T.occ owner roles = 1 := by
  induction roles with
  | nil => simp at member
  | cons head rest ih =>
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | later
      · subst owner
        simp [T.occ, occ_zero head rest parts.1]
      · have different : head ≠ owner := fun same => parts.1 (same.symm ▸ later)
        simp only [T.occ, if_neg different, Int.zero_add]
        exact ih parts.2 later

theorem ordered_deltas_sum_zero (pre : T.TransferState) (command : T.Command)
    (distinct : command.sender ≠ command.recipient) :
    T.sumOver (T.delta pre command) (T.orderedRoles pre command) = 0 := by
  have unique := ordered_roles_unique pre command distinct
  rw [T.sumOver_delta,
    occ_one command.sender _ unique (T.sender_mem_ordered_roles pre command),
    occ_one command.recipient _ unique (T.recipient_mem_ordered_roles pre command),
    occ_one pre.policy.feeOwner _ unique (T.fee_owner_mem_ordered_roles pre command)]
  omega

theorem update_roles_unique (rows : List AmountRow) (asset : String)
    (delta : String → Int) (roles : List String) (unique : S.Unique rows) :
    S.Unique (updateRoles rows asset delta roles) := by
  induction roles with
  | nil => exact unique
  | cons head rest ih => exact F.updateRows_unique _ asset head _ ih

theorem update_roles_lookup (rows : List AmountRow) (asset : String)
    (delta : String → Int) (roles : List String) (unique : S.Unique rows)
    (rolesUnique : roles.Nodup) (queryAsset queryOwner : String) :
    C.lookupLast (S.accountKey queryAsset queryOwner) (updateRoles rows asset delta roles) =
      C.lookupLast (S.accountKey queryAsset queryOwner) rows +
        (if asset = queryAsset ∧ queryOwner ∈ roles then delta queryOwner else 0) := by
  induction roles with
  | nil => simp [updateRoles]
  | cons head rest ih =>
      have parts := List.nodup_cons.mp rolesUnique
      rw [updateRoles, F.updateRows_lookup _ asset head _
        (update_roles_unique rows asset delta rest unique)]
      by_cases sameAsset : asset = queryAsset
      · subst queryAsset
        by_cases sameOwner : head = queryOwner
        · subst head
          rw [if_pos ⟨rfl, rfl⟩, ih parts.2]
          simp [parts.1]
        · rw [if_neg (by simpa only [true_and] using sameOwner), ih parts.2]
          simp only [true_and, List.mem_cons, Ne.symm sameOwner, false_or]
      · rw [if_neg (fun both => sameAsset both.1), ih parts.2]
        simp only [sameAsset, false_and, if_false, Int.add_zero]

theorem update_roles_total (rows : List AmountRow) (asset : String)
    (delta : String → Int) (roles : List String) (unique : S.Unique rows)
    (query : String) :
    amountForAsset (updateRoles rows asset delta roles) query =
      amountForAsset rows query + (if asset = query then T.sumOver delta roles else 0) := by
  induction roles with
  | nil => simp [updateRoles, T.sumOver]
  | cons head rest ih =>
      rw [updateRoles, F.updateRows_total _ asset head _
        (update_roles_unique rows asset delta rest unique), ih]
      by_cases selected : asset = query
      · simp only [if_pos selected, T.sumOver]
        omega
      · simp only [if_neg selected, Int.add_zero]

theorem update_roles_positive (rows : List AmountRow) (asset : String)
    (delta : String → Int) (roles : List String) (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows) (rolesUnique : roles.Nodup)
    (bounded : ∀ owner ∈ roles,
      T.IsU128 (C.lookupLast (S.accountKey asset owner) rows + delta owner)) :
    S.PositiveAccounts (updateRoles rows asset delta roles) := by
  induction roles with
  | nil => exact positive
  | cons head rest ih =>
      have parts := List.nodup_cons.mp rolesUnique
      have tailBounds := fun owner member => bounded owner (List.mem_cons_of_mem head member)
      apply F.updateRows_positive _ asset head _ (ih parts.2 tailBounds)
      rw [update_roles_lookup rows asset delta rest unique parts.2 asset head]
      simpa only [true_and, if_neg parts.1, Int.add_zero] using
        bounded head List.mem_cons_self

theorem transferRows_unique (pre : T.TransferState) (command : T.Command)
    (rows : List AmountRow) (unique : S.Unique rows) :
    S.Unique (transferRows pre command rows) :=
  update_roles_unique rows command.asset _ _ unique

/-- Exact account-level equation, including every unrelated asset and owner. -/
theorem transferRows_lookup (pre : T.TransferState) (command : T.Command)
    (rows : List AmountRow) (unique : S.Unique rows)
    (distinct : command.sender ≠ command.recipient) (queryAsset queryOwner : String) :
    C.lookupLast (S.accountKey queryAsset queryOwner) (transferRows pre command rows) =
      C.lookupLast (S.accountKey queryAsset queryOwner) rows +
        (if command.asset = queryAsset then T.delta pre command queryOwner else 0) := by
  rw [transferRows, update_roles_lookup rows command.asset _ _ unique
    (ordered_roles_unique pre command distinct)]
  by_cases selected : command.asset = queryAsset
  · simp only [selected, true_and, if_true]
    by_cases member : queryOwner ∈ T.orderedRoles pre command
    · rw [if_pos member]
    · have sender : queryOwner ≠ command.sender := by
        intro same
        exact member (same ▸ T.sender_mem_ordered_roles pre command)
      have recipient : queryOwner ≠ command.recipient := by
        intro same
        exact member (same ▸ T.recipient_mem_ordered_roles pre command)
      have fee : queryOwner ≠ pre.policy.feeOwner := by
        intro same
        exact member (same ▸ T.fee_owner_mem_ordered_roles pre command)
      rw [if_neg member, T.delta_untouched sender recipient fee]
  · simp only [selected, false_and, if_false]

/-- Conservation is derived over the materialized finite table for all assets. -/
theorem transferRows_totals (pre : T.TransferState) (command : T.Command)
    (rows : List AmountRow) (unique : S.Unique rows)
    (distinct : command.sender ≠ command.recipient) (query : String) :
    amountForAsset (transferRows pre command rows) query = amountForAsset rows query := by
  rw [transferRows, update_roles_total rows command.asset _ _ unique,
    ordered_deltas_sum_zero pre command distinct]
  simp

theorem accepted_selected_asset {roots : T.RootModel} {ctx : T.Context}
    {pre : T.TransferState} {command : T.Command}
    (accepted : (T.transition roots ctx pre command).verdict = .accepted) :
    command.asset = pre.policy.asset :=
  T.accepted_pre_balance_guard accepted (code := .unknownAsset) (by decide)

theorem accepted_distinct {roots : T.RootModel} {ctx : T.Context}
    {pre : T.TransferState} {command : T.Command}
    (accepted : (T.transition roots ctx pre command).verdict = .accepted) :
    command.sender ≠ command.recipient :=
  T.accepted_pre_balance_guard accepted (code := .selfTransfer) (by decide)

/-- Every actual post balance and its finite total rehydrate from the rows.
The supply argument is unchanged, as in the accepted V2 leaf. -/
theorem accepted_materialization {roots : T.RootModel} {ctx : T.Context}
    {moduleReleaseId : String} {policy : T.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : T.Command} (unique : S.Unique rows)
    (accepted : (T.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    (T.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).post =
      project moduleReleaseId policy
        (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows)
        supplyAtoms := by
  have selected : command.asset = policy.asset := accepted_selected_asset accepted
  have distinct := accepted_distinct accepted
  rw [(T.accepted_post_and_effects accepted).1]
  symm
  unfold project T.acceptedState
  congr 1
  · funext owner
    rw [transferRows_lookup _ command rows unique distinct policy.asset owner]
    simp only [selected, if_true]
    rfl
  · exact transferRows_totals _ command rows unique distinct policy.asset

theorem accepted_rows_preserve_accounts {roots : T.RootModel} {ctx : T.Context}
    {moduleReleaseId : String} {policy : T.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : T.Command} (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows)
    (preAdmitted : T.StateWellFormed (project moduleReleaseId policy rows supplyAtoms))
    (accepted : (T.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    S.Unique (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows) ∧
    S.PositiveAccounts
      (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows) := by
  have selected : command.asset = policy.asset := accepted_selected_asset accepted
  have distinct := accepted_distinct accepted
  constructor
  · exact transferRows_unique _ command rows unique
  · apply update_roles_positive rows command.asset _ _ unique positive
      (ordered_roles_unique _ command distinct)
    intro owner _
    have bounded := T.accepted_balances_u128 preAdmitted accepted owner
    rw [T.accepted_balance_eq accepted owner] at bounded
    simpa only [T.postBalance, project, selected] using bounded

theorem accepted_project_well_formed {roots : T.RootModel} {ctx : T.Context}
    {moduleReleaseId : String} {policy : T.Policy} {rows : List AmountRow}
    {supplyAtoms : Int} {command : T.Command} (unique : S.Unique rows)
    (preAdmitted : T.StateWellFormed (project moduleReleaseId policy rows supplyAtoms))
    (accepted : (T.transition roots ctx
      (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted) :
    T.StateWellFormed (project moduleReleaseId policy
      (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows)
      supplyAtoms) := by
  have bounded := T.accepted_balances_u128 preAdmitted accepted
  rw [(T.accepted_post_and_effects accepted).1] at bounded
  rw [← accepted_materialization unique accepted, (T.accepted_post_and_effects accepted).1]
  exact ⟨bounded, preAdmitted.supply, preAdmitted.accountTotal,
    preAdmitted.accountCover, preAdmitted.fee, preAdmitted.decimals⟩

/-! Concrete accepted creation/deletion, aliases, and falsification controls. -/
namespace Controls
open AssetTransferRefinementV2 (feePolicy feeCommand baseContext baseCommand ordinaryPolicy u128Max)

def rows : List AmountRow :=
  [⟨"dave", "ALT", "accounts", 7⟩, ⟨"alice", "USD", "accounts", 32⟩]
def pre : T.TransferState := project "release-v2" feePolicy rows 32
def roots : T.RootModel := ⟨fun _ => "abstract-control-root"⟩
def output : List AmountRow :=
  [⟨"dave", "ALT", "accounts", 7⟩, ⟨"bob", "USD", "accounts", 30⟩,
    ⟨"m_treasury", "USD", "accounts", 2⟩]

theorem source_unique : S.Unique rows := by
  unfold S.Unique rows
  decide

theorem source_positive : S.PositiveAccounts rows := by
  simp [S.PositiveAccounts, rows, AssetTransferSparseTablesV1.accounts,
    AssetTransferRefinementV1.IsU128, AssetTransferRefinementV1.u128Max]

theorem pre_well_formed : T.StateWellFormed pre := by
  constructor
  · intro owner
    by_cases alice : owner = "alice"
    · subst owner; decide
    · simp [pre, project, rows, feePolicy, ordinaryPolicy,
        C.lookupLast, C.amountKey, S.accountKey, alice, T.IsU128, u128Max]
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem accepted_fee_transfer :
    (T.transition roots (baseContext "alice") pre feeCommand).verdict = .accepted := by decide

theorem exact_creation_and_zero_deletion : transferRows pre feeCommand rows = output := by
  simp +decide [transferRows, updateRoles, F.updateRows, pre, project,
    rows, output, feeCommand, baseCommand, feePolicy,
    ordinaryPolicy, T.delta, T.indicator, T.orderedRoles, T.roleOrder,
    T.sortPrincipals, T.insertPrincipal, C.lookupLast, C.amountKey, S.accountKey,
    AssetTransferSparseTablesV1.putAmount, AssetTransferSparseTablesV1.makeAmount,
    AssetTransferSparseTablesV1.eraseKey, AssetTransferSparseTablesV1.accounts,
    C.sortOn, S.balanceWire, List.mergeSort,
    List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem accepted_source_and_result_accounts :
    S.Unique rows ∧ S.PositiveAccounts rows ∧
    S.Unique (transferRows pre feeCommand rows) ∧
    S.PositiveAccounts (transferRows pre feeCommand rows) :=
  ⟨source_unique, source_positive, accepted_rows_preserve_accounts source_unique source_positive
    pre_well_formed accepted_fee_transfer⟩

def aliasPre (feeOwner : String) : T.TransferState :=
  project "release-v2" { feePolicy with feeOwner := feeOwner } rows 32

theorem fee_owner_aliases_update_once :
    (T.transition roots (baseContext "alice") (aliasPre "alice") feeCommand).verdict = .accepted ∧
    (T.transition roots (baseContext "alice") (aliasPre "bob") feeCommand).verdict = .accepted ∧
    C.lookupLast (S.accountKey "USD" "alice")
      (transferRows (aliasPre "alice") feeCommand rows) = 2 ∧
    C.lookupLast (S.accountKey "USD" "bob")
      (transferRows (aliasPre "alice") feeCommand rows) = 30 ∧
    C.lookupLast (S.accountKey "USD" "alice")
      (transferRows (aliasPre "bob") feeCommand rows) = 0 ∧
    C.lookupLast (S.accountKey "USD" "bob")
      (transferRows (aliasPre "bob") feeCommand rows) = 32 := by
  have observed (feeOwner owner : String) := transferRows_lookup (aliasPre feeOwner)
    feeCommand rows source_unique (by decide) "USD" owner
  exact ⟨by decide, by decide, observed "alice" "alice", observed "alice" "bob",
    observed "bob" "alice", observed "bob" "bob"⟩

theorem unrelated_asset_unchanged :
    C.lookupLast (S.accountKey "ALT" "dave") (transferRows pre feeCommand rows) = 7 ∧
    amountForAsset (transferRows pre feeCommand rows) "ALT" = 7 ∧
    amountForAsset (transferRows pre feeCommand rows) "USD" = 32 :=
  ⟨transferRows_lookup pre feeCommand rows source_unique (by decide) "ALT" "dave",
    transferRows_totals pre feeCommand rows source_unique (by decide) "ALT",
    transferRows_totals pre feeCommand rows source_unique (by decide) "USD"⟩

def frozenRecipient : List AmountRow :=
  [⟨"dave", "ALT", "accounts", 7⟩, ⟨"m_treasury", "USD", "accounts", 2⟩]
def lostFee : List AmountRow :=
  [⟨"dave", "ALT", "accounts", 7⟩, ⟨"bob", "USD", "accounts", 30⟩]
def crossAssetMutation : List AmountRow :=
  [⟨"dave", "ALT", "accounts", 6⟩, ⟨"bob", "USD", "accounts", 30⟩,
    ⟨"m_treasury", "USD", "accounts", 2⟩]

theorem frozen_recipient_falsifies_materialization :
    (project "release-v2" feePolicy frozenRecipient 32).balance "bob" ≠
      (T.transition roots (baseContext "alice") pre feeCommand).post.balance "bob" := by decide

theorem lost_fee_falsifies_finite_total :
    amountForAsset lostFee "USD" ≠
      (T.transition roots (baseContext "alice") pre feeCommand).post.accountTotalAtoms := by decide

theorem cross_asset_mutation_falsifies_frame :
    amountForAsset crossAssetMutation "ALT" ≠ amountForAsset rows "ALT" := by decide

end Controls

end Proofs.AssetTransferFiniteAccountingV2
