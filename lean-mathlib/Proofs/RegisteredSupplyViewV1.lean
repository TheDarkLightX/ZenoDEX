import Proofs.RegisteredSupplyUpdateV1

/-!
# Completeness and updates for arbitrary covered registered-supply views

The existing support view is read as arbitrary carried policy keys and sparse
numeric rows. Canonicality below contains only input order, uniqueness, nonzero,
and support-coverage conditions. Reconstruction completeness is a conclusion.
The update lifts reuse the independent complete and numeric operations.

Strict order already excludes duplicates; the explicit uniqueness conditions
support existing lookup lemmas. The finite controls do not claim that every
condition is independently necessary. No committed field, wire conversion,
authority witness, or runtime/lifecycle refinement is introduced. Int delta
algebra is separate from external I128 command admission.
-/

set_option warningAsError true

namespace Proofs
namespace RegisteredSupplyViewV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2
  RegisteredSupplySupportV1 RegisteredSupplyUpdateV1

/-- Only explicit input conditions on the existing keys and numeric rows. -/
def CanonicalView (view : SupportView) : Prop :=
  view.registeredAssetKeys.Nodup ∧
    view.registeredAssetKeys.Pairwise (· < ·) ∧
    (view.numericSupplyRows.map SupplyRow.asset).Nodup ∧
    NumericAssetKeysOrdered view.numericSupplyRows ∧
    (∀ row ∈ view.numericSupplyRows, row.amountAtoms ≠ 0) ∧
    (∀ row ∈ view.numericSupplyRows, row.asset ∈ view.registeredAssetKeys)

private def sourceCopy (rows : List SupplyRow) : List V1SupplyRow :=
  rows.map (fun row => ⟨row.asset, row.amountAtoms⟩)

private theorem sourceRowsAsNumeric_sourceCopy (rows : List SupplyRow) :
    sourceRowsAsNumeric (sourceCopy rows) = rows := by
  unfold sourceRowsAsNumeric sourceCopy
  rw [List.map_map]
  change List.map id rows = rows
  exact List.map_id rows

private theorem numeric_lookup_of_unique {rows : List SupplyRow} {row : SupplyRow}
    (unique : (rows.map SupplyRow.asset).Nodup) (member : row ∈ rows) :
    supplyFor rows row.asset = row.amountAtoms := by
  have sourceUnique : SourceAssetKeysUnique (sourceCopy rows) := by
    simpa [SourceAssetKeysUnique, sourceCopy, List.map_map, Function.comp_def] using unique
  have sourceMember : (⟨row.asset, row.amountAtoms⟩ : V1SupplyRow) ∈ sourceCopy rows :=
    List.mem_map.mpr ⟨row, member, rfl⟩
  have lookup := source_supplyFor_eq_member_of_unique sourceUnique sourceMember
  simpa only [sourceRowsAsNumeric_sourceCopy] using lookup

private theorem numeric_lookup_zero_of_absent {rows : List SupplyRow} {asset : Asset}
    (absent : ∀ row ∈ rows, row.asset ≠ asset) : supplyFor rows asset = 0 := by
  rw [← sourceRowsAsNumeric_sourceCopy rows]
  apply source_supplyFor_zero_of_absent
  intro row member
  obtain ⟨numeric, numericMember, rfl⟩ := List.mem_map.mp member
  exact absent numeric numericMember

/-- Decoding preserves the supplied key order and multiplicity exactly. -/
theorem decoded_unique_ordered (view : SupportView) (canonical : CanonicalView view) :
    SourceAssetKeysUnique (decode view) ∧ SourceAssetKeysOrdered (decode view) := by
  unfold SourceAssetKeysUnique SourceAssetKeysOrdered
  rw [decode_registered_keys_exact]
  exact ⟨canonical.1, canonical.2.1⟩

private theorem numericRows_decode_mem_iff (view : SupportView)
    (canonical : CanonicalView view) (row : SupplyRow) :
    row ∈ numericRows (decode view) ↔ row ∈ view.numericSupplyRows := by
  obtain ⟨_, _, unique, _, nonzero, covered⟩ := canonical
  constructor
  · intro member
    obtain ⟨source, filtered, rfl⟩ := List.mem_map.mp member
    have decodedMember := (List.mem_filter.mp filtered).1
    have sourceNonzero : source.amountAtoms ≠ 0 := by
      simpa [nonzeroRow] using (List.mem_filter.mp filtered).2
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp decodedMember
    have keyPresent : key ∈ view.numericSupplyRows.map SupplyRow.asset := by
      by_cases present : key ∈ view.numericSupplyRows.map SupplyRow.asset
      · exact present
      · have absent : ∀ next ∈ view.numericSupplyRows, next.asset ≠ key := by
          intro next nextMember same
          exact present (List.mem_map.mpr ⟨next, nextMember, same⟩)
        exact False.elim (sourceNonzero (numeric_lookup_zero_of_absent absent))
    obtain ⟨original, originalMember, sameKey⟩ := List.mem_map.mp keyPresent
    have lookup : supplyFor view.numericSupplyRows key = original.amountAtoms :=
      sameKey ▸ numeric_lookup_of_unique unique originalMember
    have sameRow : toNumericRow ⟨key, supplyFor view.numericSupplyRows key⟩ = original := by
      rw [lookup]
      cases original
      cases sameKey
      rfl
    rw [sameRow]
    exact originalMember
  · intro member
    let source : V1SupplyRow := ⟨row.asset, row.amountAtoms⟩
    have decodedMember : source ∈ decode view := by
      apply List.mem_map.mpr
      exact ⟨row.asset, covered row member, by
        simp only [numeric_lookup_of_unique unique member]
        rfl⟩
    have sourceNonzero : nonzeroRow source = true := by
      simp [source, nonzeroRow, nonzero row member]
    exact List.mem_map.mpr
      ⟨source, List.mem_filter.mpr ⟨decodedMember, sourceNonzero⟩, rfl⟩

private theorem ordered_rows_eq_of_membership (left right : List SupplyRow)
    (leftOrdered : NumericAssetKeysOrdered left)
    (rightOrdered : NumericAssetKeysOrdered right)
    (members : ∀ row, row ∈ left ↔ row ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons row rows =>
          have impossible := (members row).mpr (by simp)
          simp at impossible
  | cons head tail ih =>
      cases right with
      | nil =>
          have impossible := (members head).mp (by simp)
          simp at impossible
      | cons next rest =>
          have leftParts : (∀ key ∈ tail.map SupplyRow.asset, head.asset < key) ∧
              NumericAssetKeysOrdered tail := by
            simpa only [NumericAssetKeysOrdered, List.map_cons, List.pairwise_cons]
              using leftOrdered
          have rightParts : (∀ key ∈ rest.map SupplyRow.asset, next.asset < key) ∧
              NumericAssetKeysOrdered rest := by
            simpa only [NumericAssetKeysOrdered, List.map_cons, List.pairwise_cons]
              using rightOrdered
          have sameHead : head = next := by
            rcases List.mem_cons.mp ((members head).mp (by simp)) with same | headInRest
            · exact same
            rcases List.mem_cons.mp ((members next).mpr (by simp)) with same | nextInTail
            · exact same.symm
            have forward := leftParts.1 next.asset (List.mem_map.mpr ⟨next, nextInTail, rfl⟩)
            have backward := rightParts.1 head.asset (List.mem_map.mpr ⟨head, headInRest, rfl⟩)
            exact False.elim (String.lt_asymm forward backward)
          subst next
          have leftAbsent : head ∉ tail := by
            intro member
            exact String.lt_irrefl head.asset
              (leftParts.1 head.asset (List.mem_map.mpr ⟨head, member, rfl⟩))
          have rightAbsent : head ∉ rest := by
            intro member
            exact String.lt_irrefl head.asset
              (rightParts.1 head.asset (List.mem_map.mpr ⟨head, member, rfl⟩))
          have tailMembers : ∀ row, row ∈ tail ↔ row ∈ rest := by
            intro row
            by_cases same : row = head
            · subst row
              simp only [leftAbsent, rightAbsent]
            · simpa only [List.mem_cons, same, false_or] using members row
          exact congrArg (List.cons head) (ih rest leftParts.2 rightParts.2 tailMembers)

/-- Re-encoding a decoded arbitrary covered canonical view recovers both its
original carried keys and its exact sparse numeric rows. -/
theorem encode_decode (view : SupportView) (canonical : CanonicalView view) :
    encode (decode view) = view := by
  have decodedOrdered := (decoded_unique_ordered view canonical).2
  have outputOrdered : NumericAssetKeysOrdered (numericRows (decode view)) :=
    encoded_numeric_keys_pairwise_of_source (decode view) (· < ·) decodedOrdered
  have rowsEqual := ordered_rows_eq_of_membership _ _ outputOrdered canonical.2.2.2.1
    (numericRows_decode_mem_iff view canonical)
  unfold encode
  rw [decode_registered_keys_exact, rowsEqual]

theorem numericRows_decode (view : SupportView) (canonical : CanonicalView view) :
    numericRows (decode view) = view.numericSupplyRows :=
  congrArg SupportView.numericSupplyRows (encode_decode view canonical)

/-- Encoding canonical complete rows establishes every canonical-view input
condition, including coverage of nonzero numeric support by the retained keys. -/
theorem canonical_encode (rows : List V1SupplyRow)
    (unique : SourceAssetKeysUnique rows) (ordered : SourceAssetKeysOrdered rows) :
    CanonicalView (encode rows) := by
  have covered : ∀ row ∈ numericRows rows, row.asset ∈ rows.map V1SupplyRow.asset := by
    intro row member
    obtain ⟨source, sourceMember, rfl⟩ := numericRows_member_source member
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  exact ⟨unique, ordered, encoded_numeric_keys_unique unique,
    encoded_numeric_keys_pairwise_of_source rows (· < ·) ordered,
    encoded_numeric_support_nonzero rows, covered⟩

/-- Unique sparse U128 rows give a U128 amount at each decoded key; absent
numeric support contributes the admitted quantity zero. -/
theorem decoded_u128 (view : SupportView) (canonical : CanonicalView view)
    (bounded : SparseSupplyRowsAdmitted view.numericSupplyRows) :
    SourceRowsU128 (decode view) := by
  intro source member
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
  change FitsU128 (supplyFor view.numericSupplyRows key)
  by_cases present : key ∈ view.numericSupplyRows.map SupplyRow.asset
  · obtain ⟨numeric, numericMember, sameKey⟩ := List.mem_map.mp present
    have lookup : supplyFor view.numericSupplyRows key = numeric.amountAtoms :=
      sameKey ▸ numeric_lookup_of_unique canonical.2.2.1 numericMember
    rw [lookup]
    exact (bounded numeric numericMember).1
  · have absent : ∀ numeric ∈ view.numericSupplyRows, numeric.asset ≠ key := by
      intro numeric numericMember same
      exact present (List.mem_map.mpr ⟨numeric, numericMember, same⟩)
    rw [numeric_lookup_zero_of_absent absent]
    exact zero_fits_u128

/-- Independent complete and numeric updates agree on an arbitrary canonical
covered view and a selected carried key. -/
theorem arbitrary_view_adjust_commutes (view : SupportView)
    (canonical : CanonicalView view) (asset : Asset) (deltaAtoms : Int)
    (registered : asset ∈ view.registeredAssetKeys) :
    numericRows (adjustComplete asset deltaAtoms (decode view)) =
      adjustSparse asset deltaAtoms view.numericSupplyRows := by
  have source := decoded_unique_ordered view canonical
  have result := registered_supply_adjust_commutes (decode view) asset deltaAtoms
    source.1 source.2 (by simpa only [decode_registered_keys_exact] using registered)
  simpa only [numericRows_decode view canonical] using result

/-- The original carried keys rehydrate the computed numeric update into the
independently updated complete rows. -/
theorem arbitrary_view_adjust_roundtrip (view : SupportView)
    (canonical : CanonicalView view) (asset : Asset) (deltaAtoms : Int)
    (registered : asset ∈ view.registeredAssetKeys) :
    decode ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ =
      adjustComplete asset deltaAtoms (decode view) := by
  have source := decoded_unique_ordered view canonical
  have result := registered_supply_adjust_roundtrip (decode view) asset deltaAtoms
    source.1 source.2 (by simpa only [decode_registered_keys_exact] using registered)
  simpa only [decode_registered_keys_exact, numericRows_decode view canonical] using result

/-- Every numeric lookup changes by the delta exactly at the selected key. -/
theorem arbitrary_view_adjust_lookup (view : SupportView)
    (canonical : CanonicalView view) (asset : Asset) (deltaAtoms : Int)
    (registered : asset ∈ view.registeredAssetKeys) (other : Asset) :
    supplyFor (adjustSparse asset deltaAtoms view.numericSupplyRows) other =
      supplyFor view.numericSupplyRows other + (if other = asset then deltaAtoms else 0) := by
  have source := decoded_unique_ordered view canonical
  have result := registered_supply_adjust_lookup (decode view) asset deltaAtoms
    source.1 source.2 (by simpa only [decode_registered_keys_exact] using registered) other
  simpa only [numericRows_decode view canonical] using result

theorem encode_adjusted (view : SupportView) (canonical : CanonicalView view)
    (asset : Asset) (deltaAtoms : Int) (registered : asset ∈ view.registeredAssetKeys) :
    encode (adjustComplete asset deltaAtoms (decode view)) =
      ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ := by
  unfold encode
  rw [adjustComplete_keys, decode_registered_keys_exact,
    arbitrary_view_adjust_commutes view canonical asset deltaAtoms registered]

/-- The computed output retains covered canonical support and the same carried
keys, allowing the next update theorem to apply. This closure is algebraic and
does not depend on quantity bounds. -/
theorem arbitrary_view_adjust_canonical (view : SupportView)
    (canonical : CanonicalView view) (asset : Asset) (deltaAtoms : Int)
    (registered : asset ∈ view.registeredAssetKeys) :
    CanonicalView
      ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ := by
  rw [← encode_adjusted view canonical asset deltaAtoms registered]
  have source := decoded_unique_ordered view canonical
  exact canonical_encode _ (adjustComplete_unique source.1 asset deltaAtoms)
    (adjustComplete_ordered source.2 asset deltaAtoms)

/-- Source bounds and the computed selected quantity establish complete U128
and sparse U128 admission together with canonical covered continuation. -/
theorem arbitrary_view_adjust_admitted (view : SupportView)
    (canonical : CanonicalView view) (asset : Asset) (deltaAtoms : Int)
    (registered : asset ∈ view.registeredAssetKeys)
    (bounded : SparseSupplyRowsAdmitted view.numericSupplyRows)
    (newBound : FitsU128 (supplyFor view.numericSupplyRows asset + deltaAtoms)) :
    SourceRowsU128 (adjustComplete asset deltaAtoms (decode view)) ∧
      SparseSupplyRowsAdmitted (adjustSparse asset deltaAtoms view.numericSupplyRows) ∧
      CanonicalView
        ⟨view.registeredAssetKeys, adjustSparse asset deltaAtoms view.numericSupplyRows⟩ ∧
      (adjustComplete asset deltaAtoms (decode view)).map V1SupplyRow.asset =
        view.registeredAssetKeys := by
  have source := decoded_unique_ordered view canonical
  have sourceBounded := decoded_u128 view canonical bounded
  have computedBound : FitsU128 (supplyFor (numericRows (decode view)) asset + deltaAtoms) := by
    simpa only [numericRows_decode view canonical] using newBound
  have completeBounded := adjustComplete_u128 (decode view) asset deltaAtoms source.1
    sourceBounded computedBound
  have sparseResult := registered_supply_adjust_sparse_admitted (decode view) asset deltaAtoms
    source.1 source.2 (by simpa only [decode_registered_keys_exact] using registered)
    sourceBounded computedBound
  have sparseBounded : SparseSupplyRowsAdmitted
      (adjustSparse asset deltaAtoms view.numericSupplyRows) := by
    simpa only [numericRows_decode view canonical] using sparseResult.1
  have keys : (adjustComplete asset deltaAtoms (decode view)).map V1SupplyRow.asset =
      view.registeredAssetKeys := by
    rw [adjustComplete_keys, decode_registered_keys_exact]
  exact ⟨completeBounded, sparseBounded,
    arbitrary_view_adjust_canonical view canonical asset deltaAtoms registered, keys⟩

/-! ## Finite controls for coverage, order, and repeated dormant-key updates -/

def interleavedView : SupportView :=
  ⟨["AUD", "EUR", "GBP", "USD", "ZUSD"], [⟨"EUR", 2⟩, ⟨"USD", 5⟩]⟩

theorem interleaved_view_canonical : CanonicalView interleavedView := by
  have nonzero : ∀ row ∈ interleavedView.numericSupplyRows, row.amountAtoms ≠ 0 := by
    intro row member
    have cases : row = ⟨"EUR", 2⟩ ∨ row = ⟨"USD", 5⟩ := by
      simpa [interleavedView] using member
    rcases cases with rfl | rfl <;> decide
  have covered : ∀ row ∈ interleavedView.numericSupplyRows,
      row.asset ∈ interleavedView.registeredAssetKeys := by
    intro row member
    have cases : row = ⟨"EUR", 2⟩ ∨ row = ⟨"USD", 5⟩ := by
      simpa [interleavedView] using member
    rcases cases with rfl | rfl <;> decide
  exact ⟨by decide, by decide, by decide,
    by unfold NumericAssetKeysOrdered; decide, nonzero, covered⟩

theorem interleaved_view_bounded :
    SparseSupplyRowsAdmitted interleavedView.numericSupplyRows := by
  intro row member
  have cases : row = ⟨"EUR", 2⟩ ∨ row = ⟨"USD", 5⟩ := by
    simpa [interleavedView] using member
  rcases cases with rfl | rfl <;> unfold FitsU128 <;> decide

theorem dormant_keys_before_between_after_support_control :
    decode interleavedView =
      [⟨"AUD", 0⟩, ⟨"EUR", 2⟩, ⟨"GBP", 0⟩, ⟨"USD", 5⟩, ⟨"ZUSD", 0⟩] ∧
      encode (decode interleavedView) = interleavedView := by
  decide

/-- Creating, fully deleting, and recreating an interior numeric key preserves
the dormant keys at both ends and the untouched numeric rows. -/
theorem interleaved_creation_deletion_reissue_control :
    let first := adjustSparse "GBP" 3 interleavedView.numericSupplyRows
    let second := adjustSparse "GBP" (-3) first
    let third := adjustSparse "GBP" 4 second
    first = [⟨"EUR", 2⟩, ⟨"GBP", 3⟩, ⟨"USD", 5⟩] ∧
      second = interleavedView.numericSupplyRows ∧
      third = [⟨"EUR", 2⟩, ⟨"GBP", 4⟩, ⟨"USD", 5⟩] ∧
      decode ⟨interleavedView.registeredAssetKeys, second⟩ = decode interleavedView ∧
      (decode ⟨interleavedView.registeredAssetKeys, first⟩).map V1SupplyRow.asset =
        interleavedView.registeredAssetKeys ∧
      (decode ⟨interleavedView.registeredAssetKeys, third⟩).map V1SupplyRow.asset =
        interleavedView.registeredAssetKeys := by
  decide

/-- Each output canonicality proof is used as the next step's input. -/
theorem interleaved_repeated_canonical_closure_control :
    let first := adjustSparse "GBP" 3 interleavedView.numericSupplyRows
    let second := adjustSparse "GBP" (-3) first
    let third := adjustSparse "GBP" 4 second
    CanonicalView ⟨interleavedView.registeredAssetKeys, first⟩ ∧
      CanonicalView ⟨interleavedView.registeredAssetKeys, second⟩ ∧
      CanonicalView ⟨interleavedView.registeredAssetKeys, third⟩ := by
  have registered : "GBP" ∈ interleavedView.registeredAssetKeys := by decide
  have first := arbitrary_view_adjust_canonical interleavedView interleaved_view_canonical
    "GBP" 3 registered
  have second := arbitrary_view_adjust_canonical _ first "GBP" (-3) registered
  have third := arbitrary_view_adjust_canonical _ second "GBP" 4 registered
  exact ⟨first, second, third⟩

theorem interleaved_computed_quantities_fit_control :
    let first := adjustSparse "GBP" 3 interleavedView.numericSupplyRows
    let second := adjustSparse "GBP" (-3) first
    FitsU128 (supplyFor interleavedView.numericSupplyRows "GBP" + 3) ∧
      FitsU128 (supplyFor first "GBP" - 3) ∧ FitsU128 (supplyFor second "GBP" + 4) ∧
      FitsI128 3 ∧ FitsI128 (-3) ∧ FitsI128 4 := by
  unfold FitsU128 FitsI128
  decide

theorem uncovered_support_breaks_roundtrip_control :
    let view : SupportView := ⟨["EUR"], [⟨"EUR", 2⟩, ⟨"USD", 5⟩]⟩
    encode (decode view) ≠ view := by
  decide

theorem duplicate_numeric_rows_break_roundtrip_control :
    let view : SupportView := ⟨["USD"], [⟨"USD", 2⟩, ⟨"USD", 3⟩]⟩
    encode (decode view) ≠ view := by
  decide

theorem duplicate_carried_keys_break_roundtrip_control :
    let view : SupportView := ⟨["USD", "USD"], [⟨"USD", 5⟩]⟩
    encode (decode view) ≠ view := by
  decide

theorem stored_zero_numeric_row_breaks_roundtrip_control :
    let view : SupportView := ⟨["USD"], [⟨"USD", 0⟩]⟩
    encode (decode view) ≠ view := by
  decide

theorem inconsistent_orders_break_roundtrip_control :
    let reversedKeys : SupportView := ⟨["USD", "EUR"], [⟨"EUR", 2⟩, ⟨"USD", 5⟩]⟩
    let reversedNumeric : SupportView := ⟨["EUR", "USD"], [⟨"USD", 5⟩, ⟨"EUR", 2⟩]⟩
    encode (decode reversedKeys) ≠ reversedKeys ∧
      encode (decode reversedNumeric) ≠ reversedNumeric := by
  decide

/-- An empty input is canonical. An unregistered insertion breaks numeric
correspondence while empty-key decode equality still holds vacuously. -/
theorem unknown_selected_key_support_control :
    let view : SupportView := ⟨[], []⟩
    CanonicalView view ∧
      numericRows (adjustComplete "USD" 1 (decode view)) ≠
        adjustSparse "USD" 1 view.numericSupplyRows ∧
      decode ⟨view.registeredAssetKeys, adjustSparse "USD" 1 view.numericSupplyRows⟩ =
        adjustComplete "USD" 1 (decode view) := by
  have emptyCanonical := canonical_encode [] (by unfold SourceAssetKeysUnique; decide)
    (by unfold SourceAssetKeysOrdered; decide)
  exact ⟨emptyCanonical, unknown_asset_requires_membership_control⟩

end RegisteredSupplyViewV1
end Proofs
