import Proofs.AssetLaneFiniteRecompositionV2

/-!
Exact finite cardinality changes of the existing account-row update and
coordinator recomposition. Presence is measured at the full account key;
creating a new owner row differs from replacing another owner's funded row.

The results derive row bounds from data. They do not model complete resource,
byte, codec, authentication or Python/Rust outcome admission.
-/
set_option warningAsError true

namespace Proofs.AssetLaneFiniteRowGrowthV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace S
export AssetTransferSparseTablesV1 (Unique PositiveAccounts accountKey accounts
  eraseKey eraseKey_absent putAmount balanceWire)
end S
namespace C
export CanonicalEpochEconomicRowsV1 (AmountKey amountKey lookupLast lookupLast_absent
  sortOn sortOn_perm)
end C
namespace A
export ManagedAssetFiniteAccountingV2 (project updateRows updateRows_unique)
end A
namespace R
export AssetLaneFiniteRecompositionV2 (AccountsDomain recomposeBalances managed_balance_recompose)
end R
namespace M
export ManagedAssetLifecycleRefinementV2 (Policy RootModel Context Command transition
  signedAmount accepted_authorization_guard)
end M

attribute [local instance] lexOrd

theorem eraseKey_length (key : C.AmountKey) (rows : List AmountRow) (unique : S.Unique rows) :
    (S.eraseKey key rows).length + (if key ∈ rows.map C.amountKey then 1 else 0) = rows.length := by
  induction rows with
  | nil => simp [S.eraseKey]
  | cons row rows ih =>
      have parts := List.nodup_cons.mp unique
      have count := ih parts.2
      by_cases same : C.amountKey row = key
      · have absent : key ∉ rows.map C.amountKey := by simpa only [← same] using parts.1
        simp [S.eraseKey, same, absent] at count ⊢
        omega
      · by_cases present : key ∈ rows.map C.amountKey
        · simp [S.eraseKey, same, Ne.symm same, present] at count ⊢
          omega
        · simp [S.eraseKey, same, Ne.symm same, present] at count ⊢
          omega

theorem putAmount_length (key : C.AmountKey) (rows : List AmountRow) (atoms : Int)
    (unique : S.Unique rows) :
    (S.putAmount key atoms rows).length + (if key ∈ rows.map C.amountKey then 1 else 0) =
      rows.length + (if atoms ≠ 0 then 1 else 0) := by
  have count := eraseKey_length key rows unique
  by_cases zero : atoms = 0
  · simpa [S.putAmount, zero] using count
  · simp only [S.putAmount, if_neg zero, List.length_cons, if_pos zero]
    omega

/-- Exact insertion/replacement/deletion cardinality, without a post bound. -/
theorem updateRows_length (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) :
    (A.updateRows rows asset owner deltaAtoms).length +
        (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) =
      rows.length +
        (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) := by
  unfold A.updateRows
  rw [(C.sortOn_perm S.balanceWire _).length_eq]
  exact putAmount_length _ rows _ unique

/-- The same exact count applies to the independently constructed aggregate. -/
theorem recomposeBalances_length (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) (unique : S.Unique rows)
    (accounts : R.AccountsDomain rows) (selected : asset ∈ managed) :
    (R.recomposeBalances managed rows asset owner deltaAtoms).length +
        (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) =
      rows.length +
        (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) := by
  rw [R.managed_balance_recompose managed rows asset owner deltaAtoms unique accounts selected]
  exact updateRows_length rows asset owner deltaAtoms unique

/-- A numeric capacity test is equivalent to the source-derived count; its
successful result is never assumed. -/
theorem recomposeBalances_capacity_iff (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) (capacity : Nat) (unique : S.Unique rows)
    (accounts : R.AccountsDomain rows) (selected : asset ∈ managed) :
    (R.recomposeBalances managed rows asset owner deltaAtoms).length ≤ capacity ↔
      rows.length +
        (if C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 then 1 else 0) ≤
      capacity + (if S.accountKey asset owner ∈ rows.map C.amountKey then 1 else 0) := by
  have count := recomposeBalances_length managed rows asset owner deltaAtoms unique accounts selected
  omega

theorem lookupLast_member (rows : List AmountRow) (row : AmountRow) (unique : S.Unique rows)
    (member : row ∈ rows) : C.lookupLast (C.amountKey row) rows = row.amountAtoms := by
  induction rows with
  | nil => contradiction
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | tailMember
      · simp only [C.lookupLast, if_neg parts.1, if_true]
      · have present : C.amountKey row ∈ tail.map C.amountKey :=
          List.mem_map.mpr ⟨row, tailMember, rfl⟩
        simp only [C.lookupLast, if_pos present]
        exact ih parts.2 tailMember

/-- On canonical nonzero account rows, zero lookup means this owner key is
absent, even if other owners of the same asset are funded. -/
theorem account_lookup_zero_iff_absent (rows : List AmountRow) (asset owner : String)
    (unique : S.Unique rows) (positive : S.PositiveAccounts rows) :
    C.lookupLast (S.accountKey asset owner) rows = 0 ↔
      S.accountKey asset owner ∉ rows.map C.amountKey := by
  constructor
  · intro zero present
    obtain ⟨row, member, same⟩ := List.mem_map.mp present
    have value := lookupLast_member rows row unique member
    rw [same, zero] at value
    exact (positive row member).2.2 value.symm
  · exact C.lookupLast_absent _ rows

private theorem present_of_nonzero (rows : List AmountRow) (asset owner : String)
    (nonzero : C.lookupLast (S.accountKey asset owner) rows ≠ 0) :
    S.accountKey asset owner ∈ rows.map C.amountKey := by
  by_cases present : S.accountKey asset owner ∈ rows.map C.amountKey
  · exact present
  · exact False.elim (nonzero (C.lookupLast_absent _ rows present))

theorem dormant_issue_length (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) (positive : S.PositiveAccounts rows)
    (dormant : C.lookupLast (S.accountKey asset owner) rows = 0) (issue : 0 < deltaAtoms) :
    (A.updateRows rows asset owner deltaAtoms).length = rows.length + 1 := by
  have absent := (account_lookup_zero_iff_absent rows asset owner unique positive).mp dormant
  have nonzero : deltaAtoms ≠ 0 := by omega
  have count := updateRows_length rows asset owner deltaAtoms unique
  simpa only [if_neg absent, dormant, Int.zero_add, if_pos nonzero, Nat.add_zero] using count

theorem funded_issue_length (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (unique : S.Unique rows) (funded : 0 < C.lookupLast (S.accountKey asset owner) rows)
    (issue : 0 < deltaAtoms) :
    (A.updateRows rows asset owner deltaAtoms).length = rows.length := by
  have present := present_of_nonzero rows asset owner (by omega)
  have nonzero : C.lookupLast (S.accountKey asset owner) rows + deltaAtoms ≠ 0 := by omega
  have count := updateRows_length rows asset owner deltaAtoms unique
  simp only [if_pos present, if_pos nonzero] at count
  omega

theorem full_burn_length (rows : List AmountRow) (asset owner : String) (unique : S.Unique rows)
    (funded : 0 < C.lookupLast (S.accountKey asset owner) rows) :
    (A.updateRows rows asset owner (-C.lookupLast (S.accountKey asset owner) rows)).length + 1 =
      rows.length := by
  have present := present_of_nonzero rows asset owner (by omega)
  have count := updateRows_length rows asset owner (-C.lookupLast (S.accountKey asset owner) rows) unique
  have zero : C.lookupLast (S.accountKey asset owner) rows +
      -C.lookupLast (S.accountKey asset owner) rows = 0 := by omega
  simpa only [if_pos present, zero, ne_eq, not_true_eq_false, if_false,
    Nat.add_zero] using count

theorem zero_update_removes_key (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (zero : C.lookupLast (S.accountKey asset owner) rows + deltaAtoms = 0) :
    S.accountKey asset owner ∉ (A.updateRows rows asset owner deltaAtoms).map C.amountKey := by
  intro member
  have raw := ((C.sortOn_perm S.balanceWire
    (S.putAmount (S.accountKey asset owner)
      (C.lookupLast (S.accountKey asset owner) rows + deltaAtoms) rows)).map C.amountKey).mem_iff.mp member
  apply S.eraseKey_absent (S.accountKey asset owner) rows
  simpa only [zero, S.putAmount, if_true] using raw

/-- Reissuing to the same deleted account key restores exactly one row. -/
theorem full_burn_then_reissue_length (rows : List AmountRow) (asset owner : String)
    (deltaAtoms : Int) (unique : S.Unique rows)
    (funded : 0 < C.lookupLast (S.accountKey asset owner) rows) (issue : 0 < deltaAtoms) :
    let burned := A.updateRows rows asset owner (-C.lookupLast (S.accountKey asset owner) rows)
    S.accountKey asset owner ∉ burned.map C.amountKey ∧
      (A.updateRows burned asset owner deltaAtoms).length = rows.length := by
  dsimp only
  have absent := zero_update_removes_key rows asset owner
    (-C.lookupLast (S.accountKey asset owner) rows) (by omega)
  have zero := C.lookupLast_absent (S.accountKey asset owner) _ absent
  have uniqueBurned := A.updateRows_unique rows asset owner
    (-C.lookupLast (S.accountKey asset owner) rows) unique
  have count := updateRows_length _ asset owner deltaAtoms uniqueBurned
  have nonzero : deltaAtoms ≠ 0 := by omega
  simp only [if_neg absent, zero, Int.zero_add, if_pos nonzero, Nat.add_zero] at count
  exact ⟨absent, count.trans (full_burn_length rows asset owner unique funded)⟩

/-- At any source capacity, a dormant owner adds one row, a funded owner
keeps the row count on issue, and a full account burn frees one row. -/
theorem recompose_at_capacity (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) (capacity : Nat) (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows) (selected : asset ∈ managed)
    (atCapacity : rows.length = capacity) (issue : 0 < deltaAtoms) :
    (C.lookupLast (S.accountKey asset owner) rows = 0 →
      (R.recomposeBalances managed rows asset owner deltaAtoms).length = capacity + 1) ∧
    (0 < C.lookupLast (S.accountKey asset owner) rows →
      (R.recomposeBalances managed rows asset owner deltaAtoms).length = capacity) ∧
    (0 < C.lookupLast (S.accountKey asset owner) rows →
      (R.recomposeBalances managed rows asset owner
        (-C.lookupLast (S.accountKey asset owner) rows)).length + 1 = capacity) := by
  have accounts : R.AccountsDomain rows := fun row member => (positive row member).1
  rw [R.managed_balance_recompose managed rows asset owner deltaAtoms unique accounts selected,
    R.managed_balance_recompose managed rows asset owner
      (-C.lookupLast (S.accountKey asset owner) rows) unique accounts selected]
  constructor
  · intro dormant
    rw [dormant_issue_length rows asset owner deltaAtoms unique positive dormant issue, atCapacity]
  constructor
  · intro funded
    rw [funded_issue_length rows asset owner deltaAtoms unique funded issue, atCapacity]
  · intro funded
    rw [full_burn_length rows asset owner unique funded, atCapacity]

/-- The real row ceiling is instantiated only here; no 4096-row fixture is
materialized and no post-capacity premise is introduced. -/
theorem dormant_issue_at_4096_exceeds (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) (unique : S.Unique rows)
    (positive : S.PositiveAccounts rows) (selected : asset ∈ managed)
    (atCapacity : rows.length = 4096) (issue : 0 < deltaAtoms)
    (dormant : C.lookupLast (S.accountKey asset owner) rows = 0) :
    (R.recomposeBalances managed rows asset owner deltaAtoms).length = 4097 ∧
      ¬ (R.recomposeBalances managed rows asset owner deltaAtoms).length ≤ 4096 := by
  have count := (recompose_at_capacity managed rows asset owner deltaAtoms 4096 unique positive
    selected atCapacity issue).1 dormant
  exact ⟨count, by omega⟩

/-- Prior V2 acceptance binds the policy asset before the exact aggregate
row-count law is applied. This is not a complete runtime resource outcome. -/
theorem accepted_managed_recomposition_length {managed : List Asset} {rows : List AmountRow}
    {release : String} {policy : M.Policy} {supplyAtoms : Int}
    {roots : M.RootModel} {ctx : M.Context} {command : M.Command}
    (unique : S.Unique rows) (accounts : R.AccountsDomain rows)
    (selectedPolicy : policy.asset ∈ managed)
    (accepted : (M.transition roots ctx (A.project release policy
      (AssetLaneSharedProjectionV2.selectRows managed rows) supplyAtoms) command).verdict = .accepted) :
    command.asset = policy.asset ∧ command.asset ∈ managed ∧
      (R.recomposeBalances managed rows command.asset command.accountOwner (M.signedAmount command)).length +
        (if S.accountKey policy.asset command.accountOwner ∈ rows.map C.amountKey then 1 else 0) =
      rows.length +
        (if C.lookupLast (S.accountKey policy.asset command.accountOwner) rows +
          M.signedAmount command ≠ 0 then 1 else 0) := by
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  have member : command.asset ∈ managed := selected ▸ selectedPolicy
  have count := recomposeBalances_length managed rows command.asset command.accountOwner
    (M.signedAmount command) unique accounts member
  exact ⟨selected, member, by simpa only [selected] using count⟩

end Proofs.AssetLaneFiniteRowGrowthV2
