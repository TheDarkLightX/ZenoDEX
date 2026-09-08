import Proofs.AssetLaneSharedProjectionV2

/-!
The managed leaf updates its filtered finite tables. The coordinator appends
that post to the unmanaged pre complement and sorts. These independently
defined constructions equal the existing full finite updates, including the
complete supply identities whose numeric amount is zero.

This is row recomposition over Int. Resource, codec, root and authority
admission, and equality of full runtime outcomes, remain separate obligations.
-/
set_option warningAsError true

namespace Proofs.AssetLaneFiniteRecompositionV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
open RegisteredSupplySupportV1 RegisteredSupplyUpdateV1 RegisteredSupplyViewV1

namespace A
export ManagedAssetFiniteAccountingV2 (project updateRows updateRows_unique accepted_materialization)
end A
namespace C
export CanonicalEpochEconomicRowsV1 (amountKey lookupLast sortOn sortOn_perm
  sortOn_ordered mem_sortOn)
end C
namespace S
export AssetTransferSparseTablesV1 (accounts accountKey balanceWire makeAmount
  eraseKey putAmount Unique PositiveAccounts putAmount_unique)
end S
namespace H
export AssetLaneSharedProjectionV2 (selectRows selectRows_lookup full_managed_filter_projection)
end H
namespace M
export ManagedAssetLifecycleRefinementV2 (Policy RootModel Context Command transition
  signedAmount accepted_authorization_guard)
end M

attribute [local instance] lexOrd

def AccountsDomain (rows : List AmountRow) : Prop :=
  ∀ row ∈ rows, row.custodyDomain = S.accounts

def outsideBalances (managed : List Asset) (rows : List AmountRow) : List AmountRow :=
  rows.filter (fun row => !decide (row.asset ∈ managed))

def mergeBalances (managed : List Asset) (pre leafPost : List AmountRow) : List AmountRow :=
  C.sortOn S.balanceWire (outsideBalances managed pre ++ leafPost)

def recomposeBalances (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) : List AmountRow :=
  mergeBalances managed rows (A.updateRows (H.selectRows managed rows) asset owner deltaAtoms)

def selectSupplies (managed : List Asset) (rows : List V1SupplyRow) : List V1SupplyRow :=
  rows.filter (fun row => decide (row.asset ∈ managed))

def outsideSupplies (managed : List Asset) (rows : List V1SupplyRow) : List V1SupplyRow :=
  rows.filter (fun row => !decide (row.asset ∈ managed))

def mergeSupplies (managed : List Asset) (pre leafPost : List V1SupplyRow) : List V1SupplyRow :=
  C.sortOn V1SupplyRow.asset (outsideSupplies managed pre ++ leafPost)

def recomposeSupplies (managed : List Asset) (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) : List V1SupplyRow :=
  mergeSupplies managed rows (adjustComplete asset deltaAtoms (selectSupplies managed rows))

theorem member_eq_of_unique_keys {α β : Type} (key : α → β) (rows : List α)
    (unique : (rows.map key).Nodup) {left right : α}
    (leftMember : left ∈ rows) (rightMember : right ∈ rows)
    (same : key left = key right) : left = right := by
  induction rows with
  | nil => contradiction
  | cons head tail ih =>
      have parts := List.nodup_cons.mp unique
      rcases List.mem_cons.mp leftMember with rfl | leftTail
      · rcases List.mem_cons.mp rightMember with rfl | rightTail
        · rfl
        · exact False.elim (parts.1 (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
      · rcases List.mem_cons.mp rightMember with rfl | rightTail
        · exact False.elim (parts.1 (List.mem_map.mpr ⟨left, leftTail, same⟩))
        · exact ih parts.2 leftTail rightTail

/-- Comparison ties are resolved using actual member keys, not global key
injectivity on all possible amount rows. -/
theorem sortOn_eq_of_perm_keys {α β : Type} [Ord β] [Std.TransOrd β]
    [Std.LawfulEqOrd β] (key : α → β) (left right : List α)
    (perm : left.Perm right) (unique : (right.map key).Nodup)
    (ordered : right.Pairwise (fun a b => (compare (key a) (key b)).isLE = true)) :
    C.sortOn key left = right := by
  apply List.Perm.eq_of_pairwise
    (l₁ := C.sortOn key left) (l₂ := right)
  · intro a b ma mb ab ba
    apply member_eq_of_unique_keys key right unique
      (perm.mem_iff.mp ((C.sortOn_perm key left).mem_iff.mp ma)) mb
    exact Std.LawfulEqOrd.eq_of_compare (Std.OrientedCmp.isLE_antisymm ab ba)
  · exact C.sortOn_ordered key left
  · exact ordered
  · exact (C.sortOn_perm key left).trans perm

theorem balance_wire_keys_unique (rows : List AmountRow)
    (unique : S.Unique rows) (accounts : AccountsDomain rows) :
    (rows.map S.balanceWire).Nodup := by
  apply List.pairwise_map.mpr
  have pairs : rows.Pairwise (fun a b => C.amountKey a ≠ C.amountKey b) :=
    List.pairwise_map.mp unique
  apply pairs.imp_of_mem
  intro a b ma mb different same
  apply different
  have coords := Prod.mk.inj same
  simp only [C.amountKey, accounts a ma, accounts b mb, coords.1, coords.2]

theorem putAmount_accounts (rows : List AmountRow) (asset owner : String) (atoms : Int)
    (accounts : AccountsDomain rows) :
    AccountsDomain (S.putAmount (S.accountKey asset owner) atoms rows) := by
  intro row member
  unfold S.putAmount at member
  split at member
  · exact accounts row (List.mem_filter.mp member).1
  · rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact accounts row (List.mem_filter.mp member).1

theorem updateRows_accounts (rows : List AmountRow) (asset owner : String) (deltaAtoms : Int)
    (accounts : AccountsDomain rows) : AccountsDomain (A.updateRows rows asset owner deltaAtoms) := by
  intro row member
  exact putAmount_accounts rows asset owner _ accounts row
    ((C.sortOn_perm S.balanceWire _).mem_iff.mp member)

theorem balances_partition (managed : List Asset) (rows : List AmountRow) :
    (outsideBalances managed rows ++ H.selectRows managed rows).Perm rows :=
  List.perm_append_comm.trans (List.filter_append_perm _ rows)

theorem erase_unmanaged (managed : List Asset) (rows : List AmountRow) (asset owner : String)
    (selected : asset ∈ managed) :
    S.eraseKey (S.accountKey asset owner) (outsideBalances managed rows) =
      outsideBalances managed rows := by
  apply List.filter_eq_self.mpr
  intro row member
  have outside : row.asset ∉ managed := by simpa using (List.mem_filter.mp member).2
  have different : C.amountKey row ≠ S.accountKey asset owner := by
    intro same
    have sameAsset : row.asset = asset := congrArg (fun key => key.2.1) same
    apply outside
    simpa only [sameAsset] using selected
  simpa using different

theorem erased_balance_partition (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (selected : asset ∈ managed) :
    (outsideBalances managed rows ++
      S.eraseKey (S.accountKey asset owner) (H.selectRows managed rows)).Perm
        (S.eraseKey (S.accountKey asset owner) rows) := by
  have partition := (balances_partition managed rows).filter
    (fun row => C.amountKey row != S.accountKey asset owner)
  change (S.eraseKey (S.accountKey asset owner)
    (outsideBalances managed rows ++ H.selectRows managed rows)).Perm _ at partition
  rw [show S.eraseKey (S.accountKey asset owner)
      (outsideBalances managed rows ++ H.selectRows managed rows) =
      S.eraseKey (S.accountKey asset owner) (outsideBalances managed rows) ++
        S.eraseKey (S.accountKey asset owner) (H.selectRows managed rows) by
      exact List.filter_append _ _] at partition
  rw [erase_unmanaged managed rows asset owner selected] at partition
  exact partition

theorem put_balance_partition (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (atoms : Int) (selected : asset ∈ managed) :
    (outsideBalances managed rows ++
      S.putAmount (S.accountKey asset owner) atoms (H.selectRows managed rows)).Perm
        (S.putAmount (S.accountKey asset owner) atoms rows) := by
  have partition := erased_balance_partition managed rows asset owner selected
  unfold S.putAmount
  split
  · exact partition
  · exact List.perm_middle.trans (partition.cons _)

/-- The coordinator's full finite balance list equals one full-table update. -/
theorem managed_balance_recompose (managed : List Asset) (rows : List AmountRow)
    (asset owner : String) (deltaAtoms : Int) (unique : S.Unique rows)
    (accounts : AccountsDomain rows) (selected : asset ∈ managed) :
    recomposeBalances managed rows asset owner deltaAtoms =
      A.updateRows rows asset owner deltaAtoms := by
  have lookup := H.selectRows_lookup managed rows asset owner selected unique
  have partition := put_balance_partition managed rows asset owner
    (C.lookupLast (S.accountKey asset owner) rows + deltaAtoms) selected
  unfold recomposeBalances mergeBalances
  apply sortOn_eq_of_perm_keys S.balanceWire
  · unfold A.updateRows
    rw [lookup]
    exact ((C.sortOn_perm S.balanceWire _).append_left _).trans
      (partition.trans (C.sortOn_perm S.balanceWire _).symm)
  · exact balance_wire_keys_unique _ (A.updateRows_unique rows asset owner deltaAtoms unique)
      (updateRows_accounts rows asset owner deltaAtoms accounts)
  · exact C.sortOn_ordered S.balanceWire _

theorem supplies_partition (managed : List Asset) (rows : List V1SupplyRow) :
    (outsideSupplies managed rows ++ selectSupplies managed rows).Perm rows :=
  List.perm_append_comm.trans (List.filter_append_perm _ rows)

theorem complete_unmanaged (managed : List Asset) (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (selected : asset ∈ managed) :
    adjustComplete asset deltaAtoms (outsideSupplies managed rows) =
      outsideSupplies managed rows := by
  apply adjustComplete_of_absent
  intro row member same
  have outside : row.asset ∉ managed := by simpa using (List.mem_filter.mp member).2
  apply outside
  simpa only [same] using selected

/-- Complete supply recomposition retains zero identities and exact row order. -/
theorem managed_complete_supply_recompose (managed : List Asset) (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (ordered : SourceAssetKeysOrdered rows) (selected : asset ∈ managed) :
    recomposeSupplies managed rows asset deltaAtoms = adjustComplete asset deltaAtoms rows := by
  have partition := (supplies_partition managed rows).map
    (fun row => if row.asset = asset then ⟨row.asset, row.amountAtoms + deltaAtoms⟩ else row)
  change (adjustComplete asset deltaAtoms
    (outsideSupplies managed rows ++ selectSupplies managed rows)).Perm _ at partition
  rw [show adjustComplete asset deltaAtoms
      (outsideSupplies managed rows ++ selectSupplies managed rows) =
      adjustComplete asset deltaAtoms (outsideSupplies managed rows) ++
        adjustComplete asset deltaAtoms (selectSupplies managed rows) by
      exact List.map_append] at partition
  rw [complete_unmanaged managed rows asset deltaAtoms selected] at partition
  unfold recomposeSupplies mergeSupplies
  apply sortOn_eq_of_perm_keys V1SupplyRow.asset _ _ partition
  · exact adjustComplete_unique unique asset deltaAtoms
  · have pairs := List.pairwise_map.mp (adjustComplete_ordered ordered asset deltaAtoms)
    apply pairs.imp
    intro a b less
    change (compareOfLessAndEq a.asset b.asset).isLE = true
    simp [compareOfLessAndEq, less]

/-- Whole numeric support equality, complete decoding and identity retention
follow for arbitrary covered canonical input views. -/
theorem managed_recomposition_support (view : SupportView) (managed : List Asset)
    (asset : Asset) (deltaAtoms : Int) (canonical : CanonicalView view)
    (covered : ∀ key ∈ managed, key ∈ view.registeredAssetKeys) (selected : asset ∈ managed) :
    numericRows (recomposeSupplies managed (decode view) asset deltaAtoms) =
        adjustSparse asset deltaAtoms view.numericSupplyRows ∧
      recomposeSupplies managed (decode view) asset deltaAtoms =
        decode ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ ∧
      (recomposeSupplies managed (decode view) asset deltaAtoms).map V1SupplyRow.asset =
        view.registeredAssetKeys ∧
      CanonicalView
        ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ := by
  have source := decoded_unique_ordered view canonical
  have registered := covered asset selected
  rw [managed_complete_supply_recompose managed (decode view) asset deltaAtoms
    source.1 source.2 selected]
  have keys : (adjustComplete asset deltaAtoms (decode view)).map V1SupplyRow.asset =
      view.registeredAssetKeys := by
    rw [adjustComplete_keys, decode_registered_keys_exact]
  exact ⟨arbitrary_view_adjust_commutes view canonical asset deltaAtoms registered,
    (arbitrary_view_adjust_roundtrip view canonical asset deltaAtoms registered).symm,
    keys, arbitrary_view_adjust_canonical view canonical asset deltaAtoms registered⟩

/-- Actual selected-policy V2 model acceptance supplies the selected asset;
the reconstructed full rows project to that model's exact post. -/
theorem accepted_managed_recomposition {view : SupportView} {managed : List Asset}
    {rows : List AmountRow} {release : String} {policy : M.Policy}
    {roots : M.RootModel} {ctx : M.Context} {command : M.Command}
    (canonical : CanonicalView view)
    (covered : ∀ key ∈ managed, key ∈ view.registeredAssetKeys)
    (selectedPolicy : policy.asset ∈ managed) (unique : S.Unique rows)
    (accounts : AccountsDomain rows)
    (accepted : (M.transition roots ctx
      (A.project release policy (H.selectRows managed rows)
        (supplyFor (view.numericSupplyRows.filter (fun row => decide (row.asset ∈ managed)))
          policy.asset)) command).verdict = .accepted) :
    A.project release policy
        (recomposeBalances managed rows command.asset command.accountOwner (M.signedAmount command))
        (supplyFor (numericRows (recomposeSupplies managed (decode view)
          command.asset (M.signedAmount command))) policy.asset) =
      (M.transition roots ctx
        (A.project release policy (H.selectRows managed rows)
          (supplyFor (view.numericSupplyRows.filter (fun row => decide (row.asset ∈ managed)))
            policy.asset)) command).post := by
  rw [H.full_managed_filter_projection release policy managed rows view.numericSupplyRows
    selectedPolicy unique] at accepted ⊢
  have selected : command.asset = policy.asset :=
    M.accepted_authorization_guard accepted (code := .unknownAsset) (by decide)
  have member : command.asset ∈ managed := selected ▸ selectedPolicy
  rw [managed_balance_recompose managed rows command.asset command.accountOwner _
    unique accounts member,
    (managed_recomposition_support view managed command.asset _ canonical covered member).1,
    A.accepted_materialization unique accepted,
    arbitrary_view_adjust_lookup view canonical command.asset _ (covered _ member) policy.asset]
  simp only [selected, if_true]

namespace Controls

def managed : List Asset := ["GBP", "USD"]

def balances : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"frank", "VND", "accounts", 11⟩]

def complete : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 0⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def expectedIssue : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"alice", "USD", "accounts", 2⟩,
   ⟨"frank", "VND", "accounts", 11⟩]

def expectedReissue : List AmountRow :=
  [⟨"carol", "EUR", "accounts", 7⟩, ⟨"dana", "GBP", "accounts", 3⟩,
   ⟨"erin", "JPY", "accounts", 5⟩, ⟨"bob", "USD", "accounts", 1⟩,
   ⟨"frank", "VND", "accounts", 11⟩]

theorem balances_unique : S.Unique balances := by unfold S.Unique; decide
theorem balances_accounts : AccountsDomain balances := by simp [AccountsDomain, balances, S.accounts]
theorem complete_unique : SourceAssetKeysUnique complete := by unfold SourceAssetKeysUnique; decide
theorem complete_ordered : SourceAssetKeysOrdered complete := by unfold SourceAssetKeysOrdered; decide

theorem literal_issue_balances : recomposeBalances managed balances "USD" "alice" 2 = expectedIssue := by
  rw [managed_balance_recompose managed balances "USD" "alice" 2 balances_unique
    balances_accounts (by decide)]
  simp +decide [A.updateRows, balances, expectedIssue, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.makeAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem literal_full_burn_balances :
    recomposeBalances managed expectedIssue "USD" "alice" (-2) = balances := by
  rw [managed_balance_recompose managed expectedIssue "USD" "alice" (-2)
    (by unfold S.Unique; decide) (by simp [AccountsDomain, expectedIssue, S.accounts]) (by decide)]
  simp +decide [A.updateRows, balances, expectedIssue, C.amountKey, S.accountKey,
    S.putAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

theorem literal_reissue_balances :
    recomposeBalances managed balances "USD" "bob" 1 = expectedReissue := by
  rw [managed_balance_recompose managed balances "USD" "bob" 1 balances_unique
    balances_accounts (by decide)]
  simp +decide [A.updateRows, balances, expectedReissue, C.lookupLast, C.amountKey, S.accountKey,
    S.putAmount, S.makeAmount, S.eraseKey, S.accounts, C.sortOn, S.balanceWire,
    List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq, List.take, List.drop]

def issuedComplete : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 2⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

def reissuedComplete : List V1SupplyRow :=
  [⟨"AUD", 0⟩, ⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩,
   ⟨"USD", 1⟩, ⟨"VND", 11⟩, ⟨"ZZZ", 0⟩]

theorem literal_supply_lifecycle :
    recomposeSupplies managed complete "USD" 2 = issuedComplete ∧
      recomposeSupplies managed issuedComplete "USD" (-2) = complete ∧
      recomposeSupplies managed complete "USD" 1 = reissuedComplete := by
  constructor
  · rw [managed_complete_supply_recompose managed complete "USD" 2 complete_unique
      complete_ordered (by decide)]
    decide
  constructor
  · rw [managed_complete_supply_recompose managed issuedComplete "USD" (-2)
      (by unfold SourceAssetKeysUnique; decide) (by unfold SourceAssetKeysOrdered; decide) (by decide)]
    decide
  · rw [managed_complete_supply_recompose managed complete "USD" 1 complete_unique
      complete_ordered (by decide)]
    decide

theorem constructed_full_burn_and_reissue :
    recomposeBalances managed (recomposeBalances managed balances "USD" "alice" 2)
        "USD" "alice" (-2) = balances ∧
      recomposeBalances managed
        (recomposeBalances managed (recomposeBalances managed balances "USD" "alice" 2)
          "USD" "alice" (-2)) "USD" "bob" 1 = expectedReissue ∧
      recomposeSupplies managed (recomposeSupplies managed complete "USD" 2) "USD" (-2) =
        complete ∧
      recomposeSupplies managed
        (recomposeSupplies managed (recomposeSupplies managed complete "USD" 2) "USD" (-2))
        "USD" 1 = reissuedComplete := by
  rw [literal_issue_balances, literal_full_burn_balances, literal_reissue_balances,
    literal_supply_lifecycle.1, literal_supply_lifecycle.2.1, literal_supply_lifecycle.2.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem numeric_and_dormant_identity_control :
    numericRows issuedComplete = [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"USD", 2⟩, ⟨"VND", 11⟩] ∧
      numericRows complete = [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"VND", 11⟩] ∧
      numericRows reissuedComplete =
        [⟨"EUR", 7⟩, ⟨"GBP", 3⟩, ⟨"JPY", 5⟩, ⟨"USD", 1⟩, ⟨"VND", 11⟩] ∧
      issuedComplete.map V1SupplyRow.asset = complete.map V1SupplyRow.asset ∧
      reissuedComplete.map V1SupplyRow.asset = complete.map V1SupplyRow.asset := by decide

theorem missing_unmanaged_and_other_managed_rows_falsify :
    recomposeBalances managed balances "USD" "alice" 2 ≠ H.selectRows managed expectedIssue ∧
      recomposeBalances managed balances "USD" "alice" 2 ≠
        expectedIssue.filter (fun row => row.asset != "GBP") := by
  rw [literal_issue_balances]
  decide

/-- Zero-row loss can leave numeric equality unchanged while losing identity. -/
theorem missing_zero_identity_falsifies_complete_only :
    numericRows (issuedComplete.filter (fun row => row.asset != "AUD")) =
        numericRows issuedComplete ∧
      recomposeSupplies managed complete "USD" 2 ≠
        issuedComplete.filter (fun row => row.asset != "AUD") := by
  rw [literal_supply_lifecycle.1]
  decide

theorem duplicated_zero_identity_and_supply_order_falsify :
    numericRows (issuedComplete ++ [⟨"AUD", 0⟩]) = numericRows issuedComplete ∧
      ¬ SourceAssetKeysUnique (issuedComplete ++ [⟨"AUD", 0⟩]) ∧
      recomposeSupplies managed complete "USD" 2 ≠ issuedComplete ++ [⟨"AUD", 0⟩] ∧
      recomposeSupplies managed complete "USD" 2 ≠ issuedComplete.reverse := by
  rw [literal_supply_lifecycle.1]
  unfold SourceAssetKeysUnique
  decide

def duplicatedFundedRow : List AmountRow :=
  expectedIssue.take 4 ++ [⟨"alice", "USD", "accounts", 2⟩] ++ expectedIssue.drop 4

theorem duplicated_funded_row_falsifies :
    recomposeBalances managed balances "USD" "alice" 2 ≠ duplicatedFundedRow ∧
      ¬ S.Unique duplicatedFundedRow ∧ amountForAsset duplicatedFundedRow "USD" = 4 := by
  rw [literal_issue_balances]
  unfold S.Unique
  decide

def wrongOwner : List AmountRow :=
  expectedIssue.map (fun row => if row.asset = "USD" then { row with owner := "mallory" } else row)

theorem wrong_key_and_order_falsify :
    recomposeBalances managed balances "USD" "alice" 2 ≠ wrongOwner ∧
      amountForAsset wrongOwner "USD" = 2 ∧
      recomposeBalances managed balances "USD" "alice" 2 ≠ expectedIssue.reverse := by
  rw [literal_issue_balances]
  decide

theorem outside_selected_asset_breaks_recomposition :
    recomposeBalances ["USD"] [⟨"carol", "EUR", "accounts", 7⟩] "EUR" "carol" 1 ≠
      A.updateRows [⟨"carol", "EUR", "accounts", 7⟩] "EUR" "carol" 1 := by
  simp +decide [recomposeBalances, mergeBalances, outsideBalances, H.selectRows, A.updateRows,
    C.lookupLast, C.amountKey, S.accountKey, S.putAmount, S.makeAmount, S.eraseKey, S.accounts,
    C.sortOn, S.balanceWire, List.mergeSort, List.MergeSort.Internal.splitInTwo,
    List.splitAt_eq, List.take, List.drop]

/-- Unknown insertion breaks numeric correspondence; empty-key decoding is
still vacuous and must not be offered as the distinguishing control. -/
theorem unknown_numeric_insertion_and_empty_decode :
    numericRows (adjustComplete "NEW" 1 []) ≠ adjustSparse "NEW" 1 [] ∧
      decode ⟨[], adjustSparse "NEW" 1 []⟩ = adjustComplete "NEW" 1 [] := by decide

end Controls

end Proofs.AssetLaneFiniteRecompositionV2
