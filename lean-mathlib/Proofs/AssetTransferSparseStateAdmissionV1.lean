import Proofs.AssetTransferSparseSupplyV1

/-!
# Sparse ASSET_TRANSFER state-quantity admission

This file lifts the constructed selected-policy sparse transfer into the
`StateQuantitiesAdmitted` predicate for its balance-row update.  An accepted
step obtains positive, u128-bounded and canonical output balance rows from the
actual sparse constructor.  Its per-asset account total is derived from the
constructed update.  Rejected steps are exact no-ops.

The trace fixes one static module-release/policy configuration.  It does not
model publication height or replay changes, authenticate the context, prove
policy-list membership, establish canonical hashing, refine Python, Rust, or a
compiler, or construct a `Verified` record.  The theorems below use the exact
existing state predicates only.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferSparseStateAdmissionV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace S
export Proofs.AssetTransferSparseTablesV1 (Input step CanonicalBalances Unique
  PositiveAccounts accepted_sparse_transfer rejected_step_noop step_frame)
end S

namespace H
export Proofs.AssetTransferSparseTraceV1 (Config Request inputFor run)
end H

namespace P
export Proofs.AssetTransferSparseSupplyV1 (accepted_account_totals
  accepted_preserves_owned_supply rejected_owned_supply)
end P

namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (AmountKey amountKey)
end C

namespace T
export Proofs.AssetTransferRefinementV1 (IsU128 u128Max u128Max_eq_pow)
end T

namespace G
export Proofs.GlobalEconomicStateRefinementV2 (GlobalState AmountRow
  StateQuantitiesAdmitted SparseAmountRowsAdmitted OwnedMatchesSupply
  ClaimantLiabilitiesBacked OpenTerminalLiabilitiesCovered ownedFor liabilityFor
  amountForAsset supplyFor)
end G

/-- The selected sparse table owns keys as `(owner, asset, domain)`, while
global state admission indexes the same coordinates as `(asset, owner, domain)`. -/
def stateAmountKey (row : G.AmountRow) : String × String × String :=
  (row.asset, row.owner, row.custodyDomain)

def ownerFirstToStateKey (key : C.AmountKey) : String × String × String :=
  (key.2.1, key.1, key.2.2)

theorem owner_first_to_state_key_injective :
    Function.Injective ownerFirstToStateKey := by
  intro left right equal
  rcases left with ⟨leftOwner, leftAsset, leftDomain⟩
  rcases right with ⟨rightOwner, rightAsset, rightDomain⟩
  simp only [ownerFirstToStateKey, Prod.mk.injEq] at equal ⊢
  exact ⟨equal.2.1, equal.1, equal.2.2⟩

theorem canonical_balances_state_keys_nodup {rows : List G.AmountRow}
    (canonical : S.CanonicalBalances rows) :
    (rows.map stateAmountKey).Nodup := by
  have sourceKeys : (rows.map C.amountKey).Nodup := canonical.1
  have coordinateMap : rows.map stateAmountKey =
      (rows.map C.amountKey).map ownerFirstToStateKey := by
    simp only [List.map_map]
    rfl
  rw [coordinateMap]
  exact sourceKeys.map ownerFirstToStateKey
    (fun left right unequal equal => unequal (owner_first_to_state_key_injective equal))

theorem selected_is_u128_fits_u128 {amount : Int}
    (bounded : T.IsU128 amount) : FitsU128 amount := by
  simpa only [T.IsU128, T.u128Max_eq_pow, FitsU128, maxU128] using bounded

theorem canonical_balances_sparse_amount_rows_admitted {rows : List G.AmountRow}
    (canonical : S.CanonicalBalances rows) : G.SparseAmountRowsAdmitted rows := by
  intro row member
  have positive := canonical.2.1 row member
  exact ⟨selected_is_u128_fits_u128 positive.2.1, positive.2.2⟩

/-- A constructed sparse step preserves global quantity admission without a
post-state admission premise. -/
theorem step_preserves_state_quantities_admitted {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances)
    (admitted : G.StateQuantitiesAdmitted input.pre) :
    G.StateQuantitiesAdmitted (S.step input).post := by
  cases verdict : (S.step input).verdict with
  | rejected code =>
      rw [(S.rejected_step_noop verdict).1]
      exact admitted
  | accepted =>
      obtain ⟨writerEpoch, height, _, supplyRows, custodyRows, liabilityRows,
        reserveRows, _, custodyKeys, liabilityKeys, reserveKeys, supplyKeys,
        totalFits, terminalKeys, terminalRows, replay, oracle⟩ := admitted
      have acceptedSparse := S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict
      rw [S.step_frame input]
      refine ⟨writerEpoch, height,
        canonical_balances_sparse_amount_rows_admitted acceptedSparse.2.2.1,
        supplyRows, custodyRows, liabilityRows, reserveRows,
        canonical_balances_state_keys_nodup acceptedSparse.2.2.1,
        custodyKeys, liabilityKeys, reserveKeys, supplyKeys, ?_, terminalKeys,
        terminalRows, replay, oracle⟩
      intro asset
      refine ⟨?_, (totalFits asset).2.1, (totalFits asset).2.2⟩
      simp only [G.ownedFor, P.accepted_account_totals canonical.1 verdict]
      exact (totalFits asset).1

/-- Custody, liability, and terminal fields are framed by every sparse step. -/
theorem step_preserves_claimant_liabilities_backed {input : S.Input}
    (backed : G.ClaimantLiabilitiesBacked input.pre) :
    G.ClaimantLiabilitiesBacked (S.step input).post := by
  rw [S.step_frame input]
  simpa only [G.ClaimantLiabilitiesBacked,
    G.OpenTerminalLiabilitiesCovered] using backed

/-- The actual accepted/rejected sparse step preserves owned supply and
claimant-liability backing from their initial predicates. -/
theorem step_preserves_owned_supply_and_claimant_liabilities_backed {input : S.Input}
    (canonical : S.CanonicalBalances input.pre.balances)
    (owned : G.OwnedMatchesSupply input.pre)
    (backed : G.ClaimantLiabilitiesBacked input.pre) :
    G.OwnedMatchesSupply (S.step input).post ∧
      G.ClaimantLiabilitiesBacked (S.step input).post := by
  cases verdict : (S.step input).verdict with
  | rejected code =>
      exact ⟨P.rejected_owned_supply owned verdict,
        step_preserves_claimant_liabilities_backed backed⟩
  | accepted =>
      exact ⟨P.accepted_preserves_owned_supply canonical.1 owned verdict,
        step_preserves_claimant_liabilities_backed backed⟩

/-- The actual sparse trace preserves state-quantity admission from only its
initial canonical-balance and state-admission predicates. -/
theorem run_preserves_state_quantities_admitted (config : H.Config)
    (requests : List H.Request) (pre : G.GlobalState)
    (canonical : S.CanonicalBalances pre.balances)
    (admitted : G.StateQuantitiesAdmitted pre) :
    G.StateQuantitiesAdmitted (H.run config requests pre).post := by
  induction requests generalizing pre with
  | nil => exact admitted
  | cons request requests ih =>
      cases verdict : (S.step (H.inputFor config request pre)).verdict with
      | rejected code =>
          simpa only [H.run, verdict] using ih pre canonical admitted
      | accepted =>
          have nextAdmitted := step_preserves_state_quantities_admitted
            (input := H.inputFor config request pre) canonical admitted
          have nextCanonical :=
            (S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict).2.2.1
          simpa only [H.run, verdict] using
            ih (S.step (H.inputFor config request pre)).post nextCanonical nextAdmitted

/-- The actual sparse trace preserves owned supply and claimant-liability
backing while keeping the static selected-policy frame. -/
theorem run_preserves_owned_supply_and_claimant_liabilities_backed (config : H.Config)
    (requests : List H.Request) (pre : G.GlobalState)
    (canonical : S.CanonicalBalances pre.balances)
    (owned : G.OwnedMatchesSupply pre)
    (backed : G.ClaimantLiabilitiesBacked pre) :
    G.OwnedMatchesSupply (H.run config requests pre).post ∧
      G.ClaimantLiabilitiesBacked (H.run config requests pre).post := by
  induction requests generalizing pre with
  | nil => exact ⟨owned, backed⟩
  | cons request requests ih =>
      cases verdict : (S.step (H.inputFor config request pre)).verdict with
      | rejected code =>
          simpa only [H.run, verdict] using ih pre canonical owned backed
      | accepted =>
          have nextPreserved := step_preserves_owned_supply_and_claimant_liabilities_backed
            (input := H.inputFor config request pre) canonical owned backed
          have nextCanonical :=
            (S.accepted_sparse_transfer canonical.1 canonical.2.1 verdict).2.2.1
          simpa only [H.run, verdict] using ih
            (S.step (H.inputFor config request pre)).post nextCanonical
            nextPreserved.1 nextPreserved.2

end AssetTransferSparseStateAdmissionV1
end Proofs
