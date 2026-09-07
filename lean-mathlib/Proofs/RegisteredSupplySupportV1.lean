import Proofs.GlobalEconomicStateRefinementV2

/-!
# Version-explicit registered-asset support bridge

This file is a small formal representation bridge.  It keeps a complete
ordered list of registered asset keys beside numeric supply rows whose
amounts are nonzero.  Encoding filters only the numeric support; decoding
reconstructs one source row for every retained registered key by using the
existing GlobalEconomicStateRefinementV2.supplyFor function.

The registeredAssetKeys field is an observed representation field only; it
does not grant registration, policy, or other authority.

The source row type is a versioned formal carrier with the two fields needed
for this bridge.  The bridge does not alter a V1 wire state, compute a
serialization or root, or establish a runtime, Python, Rust, or V3
refinement.  Zero numeric supply therefore remains visible through its
registered key even when it is absent from numericSupplyRows.
-/

set_option warningAsError true

namespace Proofs
namespace RegisteredSupplySupportV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

structure V1SupplyRow where
  asset : Asset
  amountAtoms : Int
  deriving DecidableEq, Repr

structure SupportView where
  registeredAssetKeys : List Asset
  numericSupplyRows : List SupplyRow
  deriving DecidableEq, Repr

def toNumericRow (row : V1SupplyRow) : SupplyRow :=
  ⟨row.asset, row.amountAtoms⟩

def sourceRowsAsNumeric (rows : List V1SupplyRow) : List SupplyRow :=
  rows.map toNumericRow

def nonzeroRow (row : V1SupplyRow) : Bool :=
  decide (row.amountAtoms ≠ 0)

def numericRows (rows : List V1SupplyRow) : List SupplyRow :=
  (rows.filter nonzeroRow).map toNumericRow

def encode (rows : List V1SupplyRow) : SupportView :=
  { registeredAssetKeys := rows.map V1SupplyRow.asset
    numericSupplyRows := numericRows rows }

def decode (view : SupportView) : List V1SupplyRow :=
  view.registeredAssetKeys.map (fun asset =>
    ⟨asset, supplyFor view.numericSupplyRows asset⟩)

def SourceRowsU128 (rows : List V1SupplyRow) : Prop :=
  ∀ row ∈ rows, FitsU128 row.amountAtoms

def SourceAssetKeysUnique (rows : List V1SupplyRow) : Prop :=
  (rows.map V1SupplyRow.asset).Nodup

def NumericSupportAdmitted (view : SupportView) : Prop :=
  SparseSupplyRowsAdmitted view.numericSupplyRows

theorem encode_registered_keys_exact (rows : List V1SupplyRow) :
    (encode rows).registeredAssetKeys = rows.map V1SupplyRow.asset := rfl

theorem encode_registered_key_length (rows : List V1SupplyRow) :
    (encode rows).registeredAssetKeys.length = rows.length := by
  simp [encode]

theorem encode_numeric_key_length_no_increase (rows : List V1SupplyRow) :
    (encode rows).numericSupplyRows.length ≤ rows.length := by
  unfold encode numericRows
  rw [List.length_map]
  exact List.length_filter_le nonzeroRow rows

theorem decode_registered_key_length (view : SupportView) :
    (decode view).length = view.registeredAssetKeys.length := by
  simp [decode]

theorem decode_registered_keys_exact (view : SupportView) :
    (decode view).map V1SupplyRow.asset = view.registeredAssetKeys := by
  simp [decode, Function.comp_def]

theorem supplyFor_numericRows_preserved (rows : List V1SupplyRow) (asset : Asset) :
    supplyFor (numericRows rows) asset =
      supplyFor (sourceRowsAsNumeric rows) asset := by
  induction rows with
  | nil =>
      rfl
  | cons row rows ih =>
      by_cases zero : row.amountAtoms = 0
      · have numeric : numericRows (row :: rows) = numericRows rows := by
          simp [numericRows, nonzeroRow, zero]
        rw [numeric]
        change supplyFor (numericRows rows) asset =
          (if row.asset = asset then row.amountAtoms else 0) +
            supplyFor (sourceRowsAsNumeric rows) asset
        simp [zero, ih]
      · have numeric : numericRows (row :: rows) =
            toNumericRow row :: numericRows rows := by
          simp [numericRows, nonzeroRow, zero]
        rw [numeric]
        change (if row.asset = asset then row.amountAtoms else 0) +
            supplyFor (numericRows rows) asset =
          (if row.asset = asset then row.amountAtoms else 0) +
            supplyFor (sourceRowsAsNumeric rows) asset
        rw [ih]

theorem source_supplyFor_zero_of_absent {rows : List V1SupplyRow} {asset : Asset}
    (absent : ∀ row ∈ rows, row.asset ≠ asset) :
    supplyFor (sourceRowsAsNumeric rows) asset = 0 := by
  induction rows with
  | nil =>
      rfl
  | cons row rows ih =>
      have head : row.asset ≠ asset := absent row (by simp)
      have tail : ∀ next ∈ rows, next.asset ≠ asset := by
        intro next member
        exact absent next (by simp [member])
      change (if row.asset = asset then row.amountAtoms else 0) +
        supplyFor (sourceRowsAsNumeric rows) asset = 0
      rw [if_neg head, ih tail]
      rfl

theorem source_supplyFor_eq_member_of_unique {rows : List V1SupplyRow}
    {row : V1SupplyRow} (unique : SourceAssetKeysUnique rows)
    (member : row ∈ rows) :
    supplyFor (sourceRowsAsNumeric rows) row.asset = row.amountAtoms := by
  induction rows generalizing row with
  | nil =>
      simp at member
  | cons head tail ih =>
      have parts : head.asset ∉ tail.map V1SupplyRow.asset ∧
          SourceAssetKeysUnique tail := by
        simpa only [SourceAssetKeysUnique, List.map_cons, List.nodup_cons] using unique
      simp only [List.mem_cons] at member
      rcases member with headMember | member
      · subst row
        change (if head.asset = head.asset then head.amountAtoms else 0) +
          supplyFor (sourceRowsAsNumeric tail) head.asset = head.amountAtoms
        rw [if_pos rfl]
        have absent : ∀ next ∈ tail, next.asset ≠ head.asset := by
          intro next nextMember same
          apply parts.1
          exact List.mem_map.mpr ⟨next, nextMember, same⟩
        rw [source_supplyFor_zero_of_absent absent]
        omega
      · change (if head.asset = row.asset then head.amountAtoms else 0) +
          supplyFor (sourceRowsAsNumeric tail) row.asset = row.amountAtoms
        have headDifferent : head.asset ≠ row.asset := by
          intro same
          apply parts.1
          exact List.mem_map.mpr ⟨row, member, same.symm⟩
        rw [if_neg headDifferent]
        simpa using ih parts.2 member

theorem decode_encode (rows : List V1SupplyRow) (unique : SourceAssetKeysUnique rows) :
    decode (encode rows) = rows := by
  unfold decode encode
  rw [List.map_map]
  change List.map (fun row =>
      ⟨row.asset, supplyFor (numericRows rows) row.asset⟩) rows = rows
  have mapped : List.map (fun row =>
      ⟨row.asset, supplyFor (numericRows rows) row.asset⟩) rows =
      List.map id rows := by
    apply List.map_congr_left
    intro row member
    cases row with
    | mk asset amountAtoms =>
        dsimp
        congr 1
        rw [supplyFor_numericRows_preserved rows asset]
        exact source_supplyFor_eq_member_of_unique unique member
  exact mapped.trans (List.map_id rows)

theorem filtered_source_keys_unique {rows : List V1SupplyRow}
    (unique : SourceAssetKeysUnique rows) :
    ((rows.filter nonzeroRow).map V1SupplyRow.asset).Nodup := by
  induction rows with
  | nil =>
      simp
  | cons row rows ih =>
      have parts : row.asset ∉ rows.map V1SupplyRow.asset ∧
          SourceAssetKeysUnique rows := by
        simpa only [SourceAssetKeysUnique, List.map_cons, List.nodup_cons] using unique
      by_cases keep : nonzeroRow row = true
      · simp only [List.filter_cons, keep, ↓reduceIte, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro member
          obtain ⟨tailRow, filteredMember, same⟩ := List.mem_map.mp member
          have sourceMember := (List.mem_filter.mp filteredMember).1
          apply parts.1
          exact List.mem_map.mpr ⟨tailRow, sourceMember, same⟩
        · exact ih parts.2
      · simp only [List.filter_cons, keep]
        exact ih parts.2

theorem encoded_numeric_keys_unique {rows : List V1SupplyRow}
    (unique : SourceAssetKeysUnique rows) :
    ((encode rows).numericSupplyRows.map SupplyRow.asset).Nodup := by
  unfold encode numericRows
  simpa only [List.map_map, Function.comp_def, toNumericRow] using
    filtered_source_keys_unique unique

theorem encoded_numeric_keys_sublist (rows : List V1SupplyRow) :
    ((encode rows).numericSupplyRows.map SupplyRow.asset).Sublist
      (rows.map V1SupplyRow.asset) := by
  have filtered_sublist :
      (rows.filter nonzeroRow).Sublist rows := by
    induction rows with
    | nil =>
        exact List.Sublist.refl []
    | cons row rows ih =>
        by_cases keep : nonzeroRow row = true
        · rw [List.filter_cons, if_pos keep]
          exact List.Sublist.cons₂ row ih
        · rw [List.filter_cons, if_neg keep]
          exact List.Sublist.cons row ih
  unfold encode numericRows
  simpa only [List.map_map, Function.comp_def, toNumericRow] using
    List.Sublist.map (fun row : V1SupplyRow => row.asset) filtered_sublist

theorem encoded_numeric_keys_pairwise_of_source
    (rows : List V1SupplyRow) (R : Asset → Asset → Prop)
    (ordered : List.Pairwise R (rows.map V1SupplyRow.asset)) :
    List.Pairwise R ((encode rows).numericSupplyRows.map SupplyRow.asset) := by
  exact List.Pairwise.sublist (encoded_numeric_keys_sublist rows) ordered

theorem encoded_numeric_support_nonzero (rows : List V1SupplyRow) :
    ∀ row ∈ (encode rows).numericSupplyRows, row.amountAtoms ≠ 0 := by
  intro row member
  unfold encode numericRows at member
  obtain ⟨source, filtered, rfl⟩ := List.mem_map.mp member
  exact by simpa [nonzeroRow] using (List.mem_filter.mp filtered).2

theorem encoded_numeric_support_admitted {rows : List V1SupplyRow}
    (bounded : SourceRowsU128 rows) :
    NumericSupportAdmitted (encode rows) := by
  intro row member
  unfold encode numericRows at member
  obtain ⟨source, filtered, rfl⟩ := List.mem_map.mp member
  have parts := List.mem_filter.mp filtered
  exact ⟨bounded source parts.1, by simpa [nonzeroRow] using parts.2⟩

theorem decoded_supply_lookup (view : SupportView) (asset : Asset) :
    ∀ row ∈ decode view, row.asset = asset →
      row.amountAtoms = supplyFor view.numericSupplyRows asset := by
  intro row member same
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
  subst asset
  rfl

theorem decoded_keys_preserve_encoded_keys (rows : List V1SupplyRow) :
    (decode (encode rows)).map V1SupplyRow.asset =
      (encode rows).registeredAssetKeys := by
  exact decode_registered_keys_exact (encode rows)

theorem decode_encode_registered_keys_exact (rows : List V1SupplyRow) :
    (decode (encode rows)).map V1SupplyRow.asset =
      rows.map V1SupplyRow.asset := by
  rw [decoded_keys_preserve_encoded_keys, encode_registered_keys_exact]

/-! ## Minimal countermodels for the representation boundary -/

def zeroRow : V1SupplyRow :=
  ⟨"ZUSD", 0⟩

def zeroRows : List V1SupplyRow :=
  [zeroRow]

def duplicateRows : List V1SupplyRow :=
  [⟨"USD", 2⟩, ⟨"USD", 3⟩]

theorem zero_row_numeric_projection_collides_with_empty :
    (encode zeroRows).numericSupplyRows = (encode []).numericSupplyRows ∧
      (encode zeroRows).registeredAssetKeys ≠ (encode []).registeredAssetKeys := by
  decide

theorem zero_row_roundtrip_keeps_registered_identity :
    decode (encode zeroRows) = zeroRows :=
  decode_encode zeroRows (by unfold SourceAssetKeysUnique; decide)

theorem zero_row_numeric_lookup_is_zero :
    supplyFor (encode zeroRows).numericSupplyRows "ZUSD" = 0 := by
  decide

theorem duplicate_keys_are_not_unique :
    ¬ SourceAssetKeysUnique duplicateRows := by
  simp [SourceAssetKeysUnique, duplicateRows]

theorem duplicate_numeric_lookup_aggregates :
    supplyFor (encode duplicateRows).numericSupplyRows "USD" = 5 := by
  decide

theorem duplicate_roundtrip_is_not_lossless :
    decode (encode duplicateRows) ≠ duplicateRows := by
  decide

end RegisteredSupplySupportV1
