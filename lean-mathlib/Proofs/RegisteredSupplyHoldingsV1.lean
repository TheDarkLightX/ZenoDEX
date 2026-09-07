import Proofs.RegisteredSupplySupportV1
import Proofs.AssetTransferGlobalStateClosureV1

/-!
# Registered supply to holdings bridge

This module connects the complete V1 supply rows carried by an admitted policy
selection state to the filtered numeric support view from
`RegisteredSupplySupportV1`.  The source rows and their complete asset keys
remain authoritative.  The support view is an observed representation and
does not add policy, registry, serialization, root, or runtime authority.

The primitive relation takes local state admission and owned-supply equality as
separate premises.  The stronger global quantity admission predicate excludes
zero supply rows, so it is used only by the invariant/continuation corollaries.
-/

set_option warningAsError true

namespace Proofs
namespace RegisteredSupplyHoldingsV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace R
export Proofs.RegisteredSupplySupportV1
  (V1SupplyRow SupportView toNumericRow sourceRowsAsNumeric nonzeroRow numericRows
   encode decode SourceRowsU128 SourceAssetKeysUnique NumericSupportAdmitted
   decode_encode supplyFor_numericRows_preserved encoded_numeric_keys_sublist
   encoded_numeric_keys_pairwise_of_source encoded_numeric_support_admitted)
end R

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (State StateAdmitted policyKey supplyKey SuppliesAdmitted step)
end K

namespace G
export Proofs.GlobalEconomicStateRefinementV2
  (SupplyRow amountForAsset supplyFor ownedFor OwnedMatchesSupply)
end G

namespace Z
export Proofs.AssetTransferGlobalStateClosureV1
  (StateInvariant continuedState continuedState_invariant continuedState_accepted
   continuedState_rejected)
end Z

namespace X
export Proofs.AssetTransferGlobalSuccessorV1 (Input Admitted result successor)
end X

def sourceRows (state : K.State) : List R.V1SupplyRow :=
  state.economic.supplies.map (fun row => ⟨row.asset, row.amountAtoms⟩)

structure SupportRelation (state : K.State) : Prop where
  sourceKeysUnique : R.SourceAssetKeysUnique (sourceRows state)
  sourceRowsU128 : R.SourceRowsU128 (sourceRows state)
  rawRoundtrip : R.decode (R.encode (sourceRows state)) = sourceRows state
  registeredKeys :
    (R.encode (sourceRows state)).registeredAssetKeys = state.policies.map K.policyKey
  sourceKeysOrdered :
    List.Pairwise (fun left right => compare left right = .lt)
      ((sourceRows state).map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset)
  numericSupportAdmitted : R.NumericSupportAdmitted (R.encode (sourceRows state))
  numericKeysSublist :
    ((R.encode (sourceRows state)).numericSupplyRows.map
      Proofs.GlobalEconomicStateRefinementV2.SupplyRow.asset).Sublist
      ((sourceRows state).map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset)
  numericKeysOrdered :
    List.Pairwise (fun left right => compare left right = .lt)
      ((R.encode (sourceRows state)).numericSupplyRows.map
        Proofs.GlobalEconomicStateRefinementV2.SupplyRow.asset)
  lookupOwned : ∀ asset,
    G.supplyFor (R.encode (sourceRows state)).numericSupplyRows asset =
      G.ownedFor state.economic asset

private theorem source_rows_u128_of_admitted {state : K.State}
    (admitted : K.StateAdmitted state) :
    R.SourceRowsU128 (sourceRows state) := by
  intro row member
  obtain ⟨source, sourceMember, same⟩ := List.mem_map.mp member
  subst row
  exact Proofs.AssetTransferSparseStateAdmissionV1.selected_is_u128_fits_u128
    (admitted.2.2.1.2.2.2 source sourceMember)

private theorem source_keys_unique_of_admitted {state : K.State}
    (admitted : K.StateAdmitted state) :
    R.SourceAssetKeysUnique (sourceRows state) := by
  simpa only [R.SourceAssetKeysUnique, sourceRows, List.map_map, Function.comp_def,
    K.supplyKey, R.V1SupplyRow] using admitted.2.2.1.1

private theorem source_keys_ordered_of_admitted {state : K.State}
    (admitted : K.StateAdmitted state) :
    List.Pairwise (fun left right => compare left right = .lt)
      ((sourceRows state).map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset) := by
  have mapped :
      List.Pairwise (fun left right : Asset => compare left right = .lt)
        (state.economic.supplies.map
          Proofs.GlobalEconomicStateRefinementV2.SupplyRow.asset) := by
    apply (List.pairwise_map).2
    simpa [K.supplyKey] using admitted.2.2.1.2.1
  simpa [sourceRows] using mapped

private theorem registered_keys_of_admitted {state : K.State}
    (admitted : K.StateAdmitted state) :
    (R.encode (sourceRows state)).registeredAssetKeys = state.policies.map K.policyKey := by
  simpa only [R.encode, R.sourceRowsAsNumeric, R.numericRows, sourceRows,
    List.map_map, Function.comp_def, R.toNumericRow, K.supplyKey] using admitted.2.2.2.1.symm

private theorem map_to_numeric_identity (rows : List G.SupplyRow) :
    ((rows.map (fun row : G.SupplyRow =>
      (⟨row.asset, row.amountAtoms⟩ : R.V1SupplyRow))).map R.toNumericRow) = rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [R.toNumericRow, ih]

private theorem lookup_source_rows {state : K.State} (asset : Asset) :
    G.supplyFor (R.encode (sourceRows state)).numericSupplyRows asset =
      G.supplyFor state.economic.supplies asset := by
  change G.supplyFor (R.numericRows (sourceRows state)) asset =
    G.supplyFor state.economic.supplies asset
  rw [R.supplyFor_numericRows_preserved]
  have same : R.sourceRowsAsNumeric (sourceRows state) = state.economic.supplies := by
    unfold R.sourceRowsAsNumeric sourceRows
    exact map_to_numeric_identity state.economic.supplies
  rw [same]

theorem support_relation_of_admitted_owned {state : K.State}
    (admitted : K.StateAdmitted state)
    (owned : G.OwnedMatchesSupply state.economic) : SupportRelation state := by
  let rows := sourceRows state
  have unique : R.SourceAssetKeysUnique rows := by
    dsimp [rows]
    exact source_keys_unique_of_admitted admitted
  have bounded : R.SourceRowsU128 rows := by
    dsimp [rows]
    exact source_rows_u128_of_admitted admitted
  have ordered : List.Pairwise (fun left right => compare left right = .lt)
      (rows.map Proofs.RegisteredSupplySupportV1.V1SupplyRow.asset) := by
    dsimp [rows]
    exact source_keys_ordered_of_admitted admitted
  refine
    { sourceKeysUnique := unique
      sourceRowsU128 := bounded
      rawRoundtrip := ?_
      registeredKeys := ?_
      sourceKeysOrdered := ordered
      numericSupportAdmitted := ?_
      numericKeysSublist := ?_
      numericKeysOrdered := ?_
      lookupOwned := ?_ }
  · exact R.decode_encode rows unique
  · exact registered_keys_of_admitted admitted
  · exact R.encoded_numeric_support_admitted bounded
  · exact R.encoded_numeric_keys_sublist rows
  · exact R.encoded_numeric_keys_pairwise_of_source rows
      (fun left right => compare left right = .lt) ordered
  · intro asset
    calc
      G.supplyFor (R.encode rows).numericSupplyRows asset =
          G.supplyFor state.economic.supplies asset := by
            dsimp [rows]
            exact lookup_source_rows asset
      _ = G.ownedFor state.economic asset := owned asset |>.symm

theorem support_relation_of_invariant {state : K.State}
    (invariant : Z.StateInvariant state) : SupportRelation state :=
  support_relation_of_admitted_owned invariant.state invariant.owned

theorem support_relation_physical {state : K.State}
    (admitted : K.StateAdmitted state)
    (owned : G.OwnedMatchesSupply state.economic)
    (reservesEmpty : state.economic.reserves = []) :
    ∀ asset,
      G.supplyFor (R.encode (sourceRows state)).numericSupplyRows asset =
        G.amountForAsset state.economic.balances asset +
          G.amountForAsset state.economic.custody asset := by
  intro asset
  have relation := support_relation_of_admitted_owned admitted owned
  calc
    G.supplyFor (R.encode (sourceRows state)).numericSupplyRows asset =
        G.ownedFor state.economic asset := relation.lookupOwned asset
    _ = G.amountForAsset state.economic.balances asset +
        G.amountForAsset state.economic.custody asset := by
      unfold G.ownedFor
      rw [reservesEmpty]
      simp [G.amountForAsset]

theorem support_relation_physical_of_invariant {state : K.State}
    (invariant : Z.StateInvariant state) :
    ∀ asset,
      G.supplyFor (R.encode (sourceRows state)).numericSupplyRows asset =
        G.amountForAsset state.economic.balances asset +
          G.amountForAsset state.economic.custody asset := by
  exact support_relation_physical invariant.state invariant.owned
    invariant.reservesEmpty

theorem continued_state_support_relation {input : X.Input}
    (admitted : X.Admitted input) :
    SupportRelation (Z.continuedState input) := by
  exact support_relation_of_invariant
    (Z.continuedState_invariant admitted)

theorem continued_state_support_relation_accepted {input : X.Input}
    (admitted : X.Admitted input)
    (accepted : (K.step input.transfer).verdict = .accepted) :
    SupportRelation (Z.continuedState input) ∧
      Z.continuedState input =
        { (X.result input).post with economic := X.successor input } := by
  exact ⟨continued_state_support_relation admitted,
    Z.continuedState_accepted accepted⟩

theorem continued_state_support_relation_rejected {input : X.Input}
    {code : Proofs.AssetTransferRefinementV1.RejectCode}
    (admitted : X.Admitted input)
    (rejected : (K.step input.transfer).verdict = .rejected code) :
    SupportRelation (Z.continuedState input) ∧
      Z.continuedState input = input.transfer.pre := by
  exact ⟨continued_state_support_relation admitted,
    Z.continuedState_rejected rejected⟩

end RegisteredSupplyHoldingsV1
end Proofs
