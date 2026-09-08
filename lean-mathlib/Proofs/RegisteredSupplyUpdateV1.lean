import Proofs.RegisteredSupplySupportV1

/-!
# Independent complete and sparse registered-supply updates

The complete update models the zero-retaining supply-row map. The independent
numeric update computes the old aggregate plus a signed delta and performs an
ordered insert, replacement, or zero deletion. Their correspondence is scoped
to canonical complete rows and an already registered selected asset.

Registered keys are observations of the original complete carrier. This file
adds no committed state field, authority witness, serialization, root, or wire
conversion. It proves no runtime refinement or accepted lifecycle continuation.

The input sparse rows are `numericRows C` for explicit complete source rows C.
Starting from arbitrary policy keys P and sparse rows N still requires a
separate encode-after-decode completeness lemma under exact support coverage,
uniqueness, and order. The algebra quantifies all signed integers; command I128
admission remains external. Output U128 admission is proved from source bounds
and the computed selected quantity.
-/

set_option warningAsError true

namespace Proofs
namespace RegisteredSupplyUpdateV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2 RegisteredSupplySupportV1

/-- The leaf update retains every source row, including a selected row at zero. -/
def adjustComplete (asset : Asset) (deltaAtoms : Int) (rows : List V1SupplyRow) :
    List V1SupplyRow :=
  rows.map (fun row =>
    if row.asset = asset then ⟨row.asset, row.amountAtoms + deltaAtoms⟩ else row)

/-- Set a numeric quantity in lexical key order, deleting the selected row at
zero. On canonical inputs this inserts at most one row and preserves all other
rows. This definition does not call either representation conversion. -/
def setSparse (asset : Asset) (amountAtoms : Int) : List SupplyRow → List SupplyRow
  | [] => if amountAtoms = 0 then [] else [⟨asset, amountAtoms⟩]
  | row :: rows =>
      if row.asset = asset then
        if amountAtoms = 0 then rows else ⟨asset, amountAtoms⟩ :: rows
      else if asset < row.asset then
        if amountAtoms = 0 then row :: rows else ⟨asset, amountAtoms⟩ :: row :: rows
      else
        row :: setSparse asset amountAtoms rows

/-- The numeric update derives its new quantity from the actual prior lookup. -/
def adjustSparse (asset : Asset) (deltaAtoms : Int) (rows : List SupplyRow) :
    List SupplyRow :=
  setSparse asset (supplyFor rows asset + deltaAtoms) rows

def SourceAssetKeysOrdered (rows : List V1SupplyRow) : Prop :=
  (rows.map V1SupplyRow.asset).Pairwise (· < ·)

def NumericAssetKeysOrdered (rows : List SupplyRow) : Prop :=
  (rows.map SupplyRow.asset).Pairwise (· < ·)

theorem adjustComplete_keys (asset : Asset) (deltaAtoms : Int)
    (rows : List V1SupplyRow) :
    (adjustComplete asset deltaAtoms rows).map V1SupplyRow.asset =
      rows.map V1SupplyRow.asset := by
  simp only [adjustComplete, List.map_map]
  apply List.map_congr_left
  intro row _
  dsimp
  split <;> rfl

theorem adjustComplete_unique {rows : List V1SupplyRow}
    (unique : SourceAssetKeysUnique rows) (asset : Asset) (deltaAtoms : Int) :
    SourceAssetKeysUnique (adjustComplete asset deltaAtoms rows) := by
  unfold SourceAssetKeysUnique
  rw [adjustComplete_keys]
  exact unique

theorem adjustComplete_ordered {rows : List V1SupplyRow}
    (ordered : SourceAssetKeysOrdered rows) (asset : Asset) (deltaAtoms : Int) :
    SourceAssetKeysOrdered (adjustComplete asset deltaAtoms rows) := by
  unfold SourceAssetKeysOrdered
  rw [adjustComplete_keys]
  exact ordered

theorem adjustComplete_of_absent {rows : List V1SupplyRow} {asset : Asset}
    (absent : ∀ row ∈ rows, row.asset ≠ asset) (deltaAtoms : Int) :
    adjustComplete asset deltaAtoms rows = rows := by
  unfold adjustComplete
  calc
    _ = List.map id rows := by
      apply List.map_congr_left
      intro row member
      simp [absent row member]
    _ = rows := List.map_id rows

theorem numericRows_cons (row : V1SupplyRow) (rows : List V1SupplyRow) :
    numericRows (row :: rows) =
      if row.amountAtoms = 0 then numericRows rows
      else toNumericRow row :: numericRows rows := by
  by_cases zero : row.amountAtoms = 0 <;> simp [numericRows, nonzeroRow, zero]

theorem numericRows_member_source {rows : List V1SupplyRow} {row : SupplyRow}
    (member : row ∈ numericRows rows) :
    ∃ source ∈ rows, toNumericRow source = row := by
  obtain ⟨source, filtered, same⟩ := List.mem_map.mp member
  exact ⟨source, (List.mem_filter.mp filtered).1, same⟩

theorem setSparse_before (asset : Asset) (amountAtoms : Int)
    (rows : List SupplyRow) (before : ∀ row ∈ rows, asset < row.asset) :
    setSparse asset amountAtoms rows =
      if amountAtoms = 0 then rows else ⟨asset, amountAtoms⟩ :: rows := by
  cases rows with
  | nil => rfl
  | cons row rows =>
      have less : asset < row.asset := before row (by simp)
      have different : row.asset ≠ asset := by
        intro same
        rw [same] at less
        exact String.lt_irrefl asset less
      simp [setSparse, different, less]

/-- Independent updates have exactly the same numeric rows for a selected
registered asset in unique, lexically ordered complete rows. Bounds are not
needed for this representation equality over integers. -/
theorem registered_supply_adjust_commutes (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (ordered : SourceAssetKeysOrdered rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset) :
    numericRows (adjustComplete asset deltaAtoms rows) =
      adjustSparse asset deltaAtoms (numericRows rows) := by
  induction rows with
  | nil => simp at registered
  | cons row rows ih =>
      have keys : row.asset ∉ rows.map V1SupplyRow.asset ∧
          SourceAssetKeysUnique rows := by
        simpa only [SourceAssetKeysUnique, List.map_cons, List.nodup_cons] using unique
      have order : (∀ key ∈ rows.map V1SupplyRow.asset, row.asset < key) ∧
          SourceAssetKeysOrdered rows := by
        simpa only [SourceAssetKeysOrdered, List.map_cons, List.pairwise_cons] using ordered
      by_cases selected : row.asset = asset
      · have absent : ∀ next ∈ rows, next.asset ≠ asset := by
          intro next member same
          apply keys.1
          exact List.mem_map.mpr ⟨next, member, same.trans selected.symm⟩
        have unchanged := adjustComplete_of_absent absent deltaAtoms
        have amount : supplyFor (numericRows (row :: rows)) asset = row.amountAtoms := by
          rw [supplyFor_numericRows_preserved]
          have lookup := source_supplyFor_eq_member_of_unique unique
            (show row ∈ row :: rows by simp)
          simpa only [selected] using lookup
        have before : ∀ next ∈ numericRows rows, asset < next.asset := by
          intro next member
          obtain ⟨source, sourceMember, rfl⟩ := numericRows_member_source member
          exact selected ▸ order.1 source.asset (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
        unfold adjustSparse
        rw [amount]
        change numericRows ((if row.asset = asset then
            ⟨row.asset, row.amountAtoms + deltaAtoms⟩ else row) ::
            adjustComplete asset deltaAtoms rows) = _
        rw [if_pos selected, unchanged, numericRows_cons, numericRows_cons]
        by_cases oldZero : row.amountAtoms = 0
        · rw [if_pos oldZero, setSparse_before asset (row.amountAtoms + deltaAtoms)
            (numericRows rows) before]
          simp only [toNumericRow, selected]
        · rw [if_neg oldZero]
          simp [setSparse, toNumericRow, selected]
      · have registeredTail : asset ∈ rows.map V1SupplyRow.asset := by
          simpa [List.map_cons, Ne.symm selected] using registered
        have headLess : row.asset < asset := order.1 asset registeredTail
        have notBefore : ¬ asset < row.asset := String.lt_asymm headLess
        have amount : supplyFor (numericRows (row :: rows)) asset =
            supplyFor (numericRows rows) asset := by
          rw [supplyFor_numericRows_preserved, supplyFor_numericRows_preserved]
          change (if row.asset = asset then row.amountAtoms else 0) +
            supplyFor (sourceRowsAsNumeric rows) asset =
              supplyFor (sourceRowsAsNumeric rows) asset
          simp only [if_neg selected, Int.zero_add]
        change numericRows ((if row.asset = asset then
            ⟨row.asset, row.amountAtoms + deltaAtoms⟩ else row) ::
            adjustComplete asset deltaAtoms rows) = _
        rw [if_neg selected, numericRows_cons, ih keys.2 order.2 registeredTail]
        unfold adjustSparse
        rw [amount, numericRows_cons]
        by_cases oldZero : row.amountAtoms = 0
        · simp only [oldZero, ↓reduceIte]
        · simp [oldZero, setSparse, toNumericRow, selected, notBefore]

theorem adjustComplete_other_lookup (rows : List V1SupplyRow)
    (asset other : Asset) (deltaAtoms : Int) (different : other ≠ asset) :
    supplyFor (sourceRowsAsNumeric (adjustComplete asset deltaAtoms rows)) other =
      supplyFor (sourceRowsAsNumeric rows) other := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change
        (if (if row.asset = asset then
            (⟨row.asset, row.amountAtoms + deltaAtoms⟩ : V1SupplyRow) else row).asset = other
          then (if row.asset = asset then
            (⟨row.asset, row.amountAtoms + deltaAtoms⟩ : V1SupplyRow) else row).amountAtoms
          else 0) +
            supplyFor (sourceRowsAsNumeric (adjustComplete asset deltaAtoms rows)) other =
        (if row.asset = other then row.amountAtoms else 0) +
            supplyFor (sourceRowsAsNumeric rows) other
      rw [ih]
      by_cases selected : row.asset = asset
      · have headDifferent : row.asset ≠ other := by
          intro same
          exact different (same.symm.trans selected)
        simp only [if_pos selected, if_neg headDifferent]
      · simp only [if_neg selected]

theorem adjustComplete_selected_lookup (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset) :
    supplyFor (numericRows (adjustComplete asset deltaAtoms rows)) asset =
      supplyFor (numericRows rows) asset + deltaAtoms := by
  obtain ⟨row, member, same⟩ := List.mem_map.mp registered
  have newMember : (⟨row.asset, row.amountAtoms + deltaAtoms⟩ : V1SupplyRow) ∈
      adjustComplete asset deltaAtoms rows := by
    apply List.mem_map.mpr
    exact ⟨row, member, by simp [same]⟩
  have pre : supplyFor (numericRows rows) asset = row.amountAtoms := by
    rw [supplyFor_numericRows_preserved]
    exact same ▸ source_supplyFor_eq_member_of_unique unique member
  have post : supplyFor (numericRows (adjustComplete asset deltaAtoms rows)) asset =
      row.amountAtoms + deltaAtoms := by
    rw [supplyFor_numericRows_preserved]
    exact same ▸ source_supplyFor_eq_member_of_unique
      (adjustComplete_unique unique asset deltaAtoms) newMember
  rw [post, pre]

/-- Exactly one registered source key changes the aggregate supply lookup. -/
theorem adjustComplete_lookup (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset) (other : Asset) :
    supplyFor (numericRows (adjustComplete asset deltaAtoms rows)) other =
      supplyFor (numericRows rows) other + (if other = asset then deltaAtoms else 0) := by
  by_cases same : other = asset
  · subst other
    simpa using adjustComplete_selected_lookup rows asset deltaAtoms unique registered
  · rw [supplyFor_numericRows_preserved, supplyFor_numericRows_preserved,
      adjustComplete_other_lookup rows asset other deltaAtoms same]
    simp only [if_neg same, Int.add_zero]

/-- Sparse lookup has the same signed delta at the selected registered asset
and zero delta at every other asset, including assets outside the carried keys. -/
theorem registered_supply_adjust_lookup (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (ordered : SourceAssetKeysOrdered rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset) (other : Asset) :
    supplyFor (adjustSparse asset deltaAtoms (numericRows rows)) other =
      supplyFor (numericRows rows) other + (if other = asset then deltaAtoms else 0) := by
  rw [← registered_supply_adjust_commutes rows asset deltaAtoms unique ordered registered]
  exact adjustComplete_lookup rows asset deltaAtoms unique registered other

/-- The complete update stays in U128 from pre-quantities and the computed
selected post-quantity. No post-state admission is a premise. -/
theorem adjustComplete_u128 (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (bounded : SourceRowsU128 rows)
    (newBound : FitsU128 (supplyFor (numericRows rows) asset + deltaAtoms)) :
    SourceRowsU128 (adjustComplete asset deltaAtoms rows) := by
  intro output member
  obtain ⟨row, sourceMember, rfl⟩ := List.mem_map.mp member
  by_cases selected : row.asset = asset
  · simp only [if_pos selected]
    have lookup : supplyFor (numericRows rows) asset = row.amountAtoms := by
      rw [supplyFor_numericRows_preserved]
      exact selected ▸ source_supplyFor_eq_member_of_unique unique sourceMember
    simpa only [lookup] using newBound
  · simpa only [if_neg selected] using bounded row sourceMember

/-- Decoding the computed sparse output with the unchanged original keys
recovers the complete updated rows, including a selected identity at zero. -/
theorem registered_supply_adjust_roundtrip (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (ordered : SourceAssetKeysOrdered rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset) :
    decode ⟨rows.map V1SupplyRow.asset,
      adjustSparse asset deltaAtoms (numericRows rows)⟩ =
        adjustComplete asset deltaAtoms rows := by
  have view : (⟨rows.map V1SupplyRow.asset,
      adjustSparse asset deltaAtoms (numericRows rows)⟩ : SupportView) =
        encode (adjustComplete asset deltaAtoms rows) := by
    unfold encode
    rw [adjustComplete_keys,
      registered_supply_adjust_commutes rows asset deltaAtoms unique ordered registered]
  rw [view]
  exact decode_encode _ (adjustComplete_unique unique asset deltaAtoms)

/-- The sparse output satisfies nonzero U128 row admission and retains canonical
unique lexical key order. These conclusions are derived from computed rows. -/
theorem registered_supply_adjust_sparse_admitted (rows : List V1SupplyRow)
    (asset : Asset) (deltaAtoms : Int) (unique : SourceAssetKeysUnique rows)
    (ordered : SourceAssetKeysOrdered rows)
    (registered : asset ∈ rows.map V1SupplyRow.asset)
    (bounded : SourceRowsU128 rows)
    (newBound : FitsU128 (supplyFor (numericRows rows) asset + deltaAtoms)) :
    SparseSupplyRowsAdmitted (adjustSparse asset deltaAtoms (numericRows rows)) ∧
      ((adjustSparse asset deltaAtoms (numericRows rows)).map SupplyRow.asset).Nodup ∧
      NumericAssetKeysOrdered (adjustSparse asset deltaAtoms (numericRows rows)) := by
  rw [← registered_supply_adjust_commutes rows asset deltaAtoms unique ordered registered]
  exact ⟨encoded_numeric_support_admitted
      (adjustComplete_u128 rows asset deltaAtoms unique bounded newBound),
    encoded_numeric_keys_unique (adjustComplete_unique unique asset deltaAtoms),
    encoded_numeric_keys_pairwise_of_source _ (· < ·)
      (adjustComplete_ordered ordered asset deltaAtoms)⟩

/-! ## Finite controls for the exact theorem domain -/

def dormantRows : List V1SupplyRow := [⟨"USD", 0⟩]

theorem dormant_rows_admitted :
    SourceAssetKeysUnique dormantRows ∧ SourceAssetKeysOrdered dormantRows ∧
      SourceRowsU128 dormantRows ∧ "USD" ∈ dormantRows.map V1SupplyRow.asset := by
  have bounded : SourceRowsU128 dormantRows := by
    intro row member
    have same : row = ⟨"USD", 0⟩ := by simpa [dormantRows] using member
    subst row
    exact zero_fits_u128
  exact ⟨by unfold SourceAssetKeysUnique; decide,
    by unfold SourceAssetKeysOrdered; decide, bounded, by decide⟩

theorem lifecycle_control_quantities_fit :
    FitsI128 7 ∧ FitsI128 (-7) ∧ FitsI128 2 ∧
      FitsU128 7 ∧ FitsU128 0 ∧ FitsU128 2 := by
  unfold FitsI128 FitsU128
  decide

/-- Given one dormant registered asset, issue, full burn, and reissue retain
its complete identity while creating, deleting, and recreating numeric support. -/
theorem zero_issue_full_burn_reissue_control :
    let complete1 := adjustComplete "USD" 7 dormantRows
    let sparse1 := adjustSparse "USD" 7 (numericRows dormantRows)
    let complete2 := adjustComplete "USD" (-7) complete1
    let sparse2 := adjustSparse "USD" (-7) sparse1
    let complete3 := adjustComplete "USD" 2 complete2
    let sparse3 := adjustSparse "USD" 2 sparse2
    complete1 = [⟨"USD", 7⟩] ∧ sparse1 = [⟨"USD", 7⟩] ∧
      complete2 = dormantRows ∧ sparse2 = [] ∧
      complete3 = [⟨"USD", 2⟩] ∧ sparse3 = [⟨"USD", 2⟩] ∧
      decode ⟨["USD"], sparse2⟩ = dormantRows ∧
      decode ⟨["USD"], sparse3⟩ = complete3 := by
  decide

/-- Unregistered numeric insertion falsifies the support equality. Empty-key
decode equality still holds vacuously, so it cannot establish this obligation. -/
theorem unknown_asset_requires_membership_control :
    numericRows (adjustComplete "USD" 1 []) ≠
      adjustSparse "USD" 1 (numericRows []) ∧
    decode ⟨[], adjustSparse "USD" 1 []⟩ =
      adjustComplete "USD" 1 (decode ⟨[], []⟩) := by
  decide

theorem duplicate_keys_break_update_control :
    numericRows (adjustComplete "USD" 1 duplicateRows) ≠
      adjustSparse "USD" 1 (numericRows duplicateRows) ∧
      decode (encode duplicateRows) ≠ duplicateRows := by
  decide

theorem unordered_keys_break_update_control :
    let rows : List V1SupplyRow := [⟨"USD", 0⟩, ⟨"EUR", 1⟩]
    numericRows (adjustComplete "USD" 1 rows) ≠
      adjustSparse "USD" 1 (numericRows rows) := by
  decide

/-- The mathematical operations are total over Int. Their out-of-range outputs
have no sparse U128 admission; a runtime must reject them at its existing gate. -/
theorem overflow_and_underflow_outside_admitted_range_control :
    ¬ FitsU128 (maxU128 + 1) ∧ ¬ FitsU128 (-1) ∧
      ¬ SparseSupplyRowsAdmitted
        (adjustSparse "USD" 1 [⟨"USD", maxU128⟩]) ∧
      ¬ SparseSupplyRowsAdmitted (adjustSparse "USD" (-1) []) := by
  have overflow : ¬ SparseSupplyRowsAdmitted
      (adjustSparse "USD" 1 [⟨"USD", maxU128⟩]) := by
    intro admitted
    have rowMember : (⟨"USD", maxU128 + 1⟩ : SupplyRow) ∈
        adjustSparse "USD" 1 [⟨"USD", maxU128⟩] := by decide
    have bounded : FitsU128 (maxU128 + 1) := (admitted _ rowMember).1
    unfold FitsU128 at bounded
    omega
  have underflow : ¬ SparseSupplyRowsAdmitted (adjustSparse "USD" (-1) []) := by
    intro admitted
    have rowMember : (⟨"USD", -1⟩ : SupplyRow) ∈
        adjustSparse "USD" (-1) [] := by decide
    have bounded : FitsU128 (-1) := (admitted _ rowMember).1
    unfold FitsU128 at bounded
    omega
  exact ⟨by unfold FitsU128; omega, by unfold FitsU128; omega, overflow, underflow⟩

end RegisteredSupplyUpdateV1
end Proofs
