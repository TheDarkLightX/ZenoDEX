import Proofs.AssetTransferSparseTraceV1

/-!
Physical per-asset conservation of the constructed sparse transfer. Finite
account-row totals are derived through its actual erase/put/update operations.
The role list is constructed by the existing leaf; no external principal
enumeration or per-step conservation/table equation is assumed.

Custody, reserves and supply rows are unchanged by the accounting projection.
Initial owned-equals-supply therefore implies the same endpoint property.
This does not establish claimant backing, context authentication, complete
route admission, receipt fields or publication. Runtime comparisons are finite
evidence about this row model, not universal Python/Rust execution refinement.
The history corollary retains SparseTrace's fixed module/policy configuration
and does not impose runtime command arity, metadata or epoch-height admission.
-/
namespace Proofs.AssetTransferSparseSupplyV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace S
export Proofs.AssetTransferSparseTablesV1 (Input step leaf localState accounts
  Unique PositiveAccounts CanonicalBalances accountKey makeAmount eraseKey putAmount
  checkedUpdate checkedUpdate_spec checkedUpdate_unique updateRoles finishBalances
  finishBalances_spec checkedBalances accepted_step_shape accepted_sparse_transfer
  perm_sum_int step_frame rejected_step_noop)
end S
namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (AmountKey amountKey amountSum lookupLast
  lookupLast_eq_amountAt amountSum_eq_amountAt sortOn_perm)
end C
namespace T
export Proofs.AssetTransferRefinementV1 (TransferState Command RejectCode delta
  roleOrder sumOver sumOver_delta occ accepted_iff_all_guards)
end T
namespace H
export Proofs.AssetTransferSparseTraceV1 (Config Request inputFor run)
end H

attribute [local instance] lexOrd

theorem amountForAsset_eraseKey (key : C.AmountKey) (rows : List AmountRow) (asset : String) :
    amountForAsset (S.eraseKey key rows) asset = amountForAsset rows asset -
      (if key.2.1 = asset then C.amountSum key rows else 0) := by
  induction rows with
  | nil => simp only [S.eraseKey, List.filter_nil, amountForAsset, List.map_nil,
      List.sum_nil, C.amountSum, ite_self, Int.sub_self]
  | cons row rows ih =>
      by_cases same : C.amountKey row = key
      · have rowAsset : row.asset = key.2.1 := congrArg (fun k => k.2.1) same
        simp only [S.eraseKey, List.filter_cons, bne_iff_ne,
          if_neg (fun (ne : C.amountKey row ≠ key) => ne same)]
        change amountForAsset (S.eraseKey key rows) asset = _
        rw [ih]
        simp only [amountForAsset, List.map_cons, List.sum_cons, C.amountSum,
          if_pos same, rowAsset]
        split <;> omega
      · simp only [S.eraseKey, List.filter_cons, bne_iff_ne, if_pos same]
        change (if row.asset = asset then row.amountAtoms else 0) +
          amountForAsset (S.eraseKey key rows) asset = _
        rw [ih]
        simp only [amountForAsset, List.map_cons, List.sum_cons, C.amountSum,
          if_neg same, Int.zero_add]
        split <;> omega

theorem amountForAsset_putAmount (key : C.AmountKey) (atoms : Int)
    (rows : List AmountRow) (asset : String) :
    amountForAsset (S.putAmount key atoms rows) asset = amountForAsset rows asset +
      (if key.2.1 = asset then atoms - C.amountSum key rows else 0) := by
  unfold S.putAmount
  split
  · rename_i zero
    rw [amountForAsset_eraseKey]
    split <;> omega
  · change (if key.2.1 = asset then atoms else 0) +
      amountForAsset (S.eraseKey key rows) asset = _
    rw [amountForAsset_eraseKey]
    split <;> omega

theorem checkedUpdate_amountForAsset {rows out : List AmountRow} {asset owner : String}
    {delta : Int} (unique : S.Unique rows)
    (accepted : S.checkedUpdate rows asset owner delta = .ok out) (query : String) :
    amountForAsset out query = amountForAsset rows query +
      (if asset = query then delta else 0) := by
  rw [(S.checkedUpdate_spec accepted).1, amountForAsset_putAmount,
    C.lookupLast_eq_amountAt (S.accountKey asset owner) rows unique,
    ← C.amountSum_eq_amountAt]
  change amountForAsset rows query +
    (if asset = query then C.amountSum (S.accountKey asset owner) rows + delta -
      C.amountSum (S.accountKey asset owner) rows else 0) = _
  split <;> omega

theorem updateRoles_amountForAsset {asset : String} {delta : String → Int}
    {owners : List String} {rows out : List AmountRow} (unique : S.Unique rows)
    (accepted : S.updateRoles asset delta owners rows = .ok out) (query : String) :
    amountForAsset out query = amountForAsset rows query +
      (if asset = query then T.sumOver delta owners else 0) := by
  induction owners generalizing rows with
  | nil =>
      cases accepted
      simp only [T.sumOver, ite_self, Int.add_zero]
  | cons owner owners ih =>
      simp only [S.updateRoles] at accepted
      cases update : S.checkedUpdate rows asset owner (delta owner) with
      | error code => simp only [update, Except.bind] at accepted; contradiction
      | ok next =>
          simp only [update, Except.bind] at accepted
          rw [ih (S.checkedUpdate_unique unique update) accepted,
            checkedUpdate_amountForAsset unique update]
          simp only [T.sumOver]
          split <;> omega

/-- Cancellation uses the leaf's own finite role list, including fee aliases. -/
theorem roleOrder_delta_zero (pre : T.TransferState) (cmd : T.Command)
    (distinct : cmd.sender ≠ cmd.recipient) :
    T.sumOver (T.delta pre cmd) (T.roleOrder pre cmd) = 0 := by
  rw [T.sumOver_delta]
  by_cases senderFee : pre.policy.feeOwner = cmd.sender
  · simp only [T.roleOrder, if_pos (Or.inl senderFee)]
    simp only [senderFee, T.occ, if_true, if_neg distinct, if_neg (Ne.symm distinct),
      Int.add_zero, Int.zero_add, Int.mul_one]
    omega
  · by_cases recipientFee : pre.policy.feeOwner = cmd.recipient
    · simp only [T.roleOrder, if_pos (Or.inr recipientFee)]
      simp only [recipientFee, T.occ, if_true, if_neg distinct, if_neg (Ne.symm distinct),
        Int.add_zero, Int.zero_add, Int.mul_one]
      omega
    · have separate : ¬(pre.policy.feeOwner = cmd.sender ∨ pre.policy.feeOwner = cmd.recipient) :=
        fun h => h.elim senderFee recipientFee
      simp only [T.roleOrder, if_neg separate, T.occ, if_true,
        if_neg distinct, if_neg (Ne.symm distinct), if_neg senderFee,
        if_neg (Ne.symm senderFee), if_neg recipientFee, if_neg (Ne.symm recipientFee),
        Int.add_zero, Int.zero_add, Int.mul_one]
      omega

theorem accepted_account_totals {input : S.Input} (unique : S.Unique input.pre.balances)
    (accepted : (S.step input).verdict = .accepted) (asset : String) :
    amountForAsset (S.step input).post.balances asset = amountForAsset input.pre.balances asset := by
  have shape := S.accepted_step_shape accepted
  have checked := shape.2.1
  unfold S.checkedBalances at checked
  cases updates : S.updateRoles input.command.asset (T.delta (S.localState input) input.command)
      (T.roleOrder (S.localState input) input.command) input.pre.balances with
  | error code => simp only [updates, Except.bind] at checked; contradiction
  | ok rows =>
      simp only [updates, Except.bind] at checked
      have equation := updateRoles_amountForAsset unique updates asset
      have distinct := ((T.accepted_iff_all_guards input.context (S.localState input) input.command).mp
        shape.1) .selfTransfer
      rw [roleOrder_delta_zero _ _ distinct] at equation
      simp only [ite_self, Int.add_zero] at equation
      rw [(S.finishBalances_spec checked).1]
      exact (S.perm_sum_int ((C.sortOn_perm _ rows).map _)).trans equation

theorem accepted_owned_totals {input : S.Input} (unique : S.Unique input.pre.balances)
    (accepted : (S.step input).verdict = .accepted) (asset : String) :
    ownedFor (S.step input).post asset = ownedFor input.pre asset := by
  have accounts := accepted_account_totals unique accepted asset
  rw [S.step_frame input]
  simp only [ownedFor, accounts]

theorem step_supply_frame (input : S.Input) (asset : String) :
    supplyFor (S.step input).post.supplies asset = supplyFor input.pre.supplies asset := by
  rw [S.step_frame input]

/-- Conservation follows from the constructed update, without a per-step premise. -/
theorem accepted_preserves_owned_supply {input : S.Input}
    (unique : S.Unique input.pre.balances) (owned : OwnedMatchesSupply input.pre)
    (accepted : (S.step input).verdict = .accepted) : OwnedMatchesSupply (S.step input).post := by
  intro asset
  rw [accepted_owned_totals unique accepted asset, step_supply_frame input asset]
  exact owned asset

theorem accepted_owned_supply_and_canonical {input : S.Input}
    (unique : S.Unique input.pre.balances) (positive : S.PositiveAccounts input.pre.balances)
    (owned : OwnedMatchesSupply input.pre) (accepted : (S.step input).verdict = .accepted) :
    OwnedMatchesSupply (S.step input).post ∧ S.CanonicalBalances (S.step input).post.balances :=
  ⟨accepted_preserves_owned_supply unique owned accepted,
    (S.accepted_sparse_transfer unique positive accepted).2.2.1⟩

theorem rejected_owned_supply {input : S.Input} {code : T.RejectCode}
    (owned : OwnedMatchesSupply input.pre) (rejected : (S.step input).verdict = .rejected code) :
    OwnedMatchesSupply (S.step input).post := by
  rw [(S.rejected_step_noop rejected).1]
  exact owned

/-- Every actual accepted/rejected attempt preserves physical owned supply. -/
theorem history_preserves_owned_supply (config : H.Config) (requests : List H.Request)
    (pre : GlobalState) (canonical : S.CanonicalBalances pre.balances)
    (owned : OwnedMatchesSupply pre) : OwnedMatchesSupply (H.run config requests pre).post := by
  induction requests generalizing pre with
  | nil => exact owned
  | cons request requests ih =>
      cases verdict : (S.step (H.inputFor config request pre)).verdict with
      | rejected code =>
          simpa only [H.run, verdict] using ih pre canonical owned
      | accepted =>
          have one := accepted_owned_supply_and_canonical canonical.1 canonical.2.1 owned verdict
          simpa only [H.run, verdict] using
            ih (S.step (H.inputFor config request pre)).post one.2 one.1

end Proofs.AssetTransferSparseSupplyV1
