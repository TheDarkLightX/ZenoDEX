import Proofs.AssetLaneFiniteEffectPlanV2
import Proofs.AssetTransferFiniteOutcomeV2

/-!
Concrete six-field transfer plans from accepted finite V2 outcomes. Numeric
admission uses GlobalSettlementCoreV2's existing predicate. Strict wire ordering,
tokens and exact field observations are separate properties. The root observer is
an arbitrary byte digest, with no root-syntax or cryptographic authority premise.
Runtime codec, serialized byte bounds, receipt and journal correspondence remain
outside this finite construction.
-/
set_option warningAsError true

namespace Proofs.AssetTransferFiniteEffectPlanV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2 RegisteredSupplySupportV1
open AssetLaneFiniteEffectPlanV2 (effectWire PlanOrdered PlanTokens effect_key_of_wire_unique
  sorted_wire_unique sorted_rows_strict covered_quantities_u128)

namespace FT
export AssetTransferFiniteOutcomeV2 (State Structural CommandAdmission project candidate transition stateRoot
  policyFor policyFor_spec payloadFor accepted_iff accepted_post_effects accepted_selected_leaf
  accepted_accounting accepted_payload_bounds accepted_effects_bind economic_candidate_structural
  ordered_roles_tokens)
end FT
namespace T
export AssetTransferRefinementV2 (Root Context Command Policy TransferState MovementRow movementRows
  orderedRoles delta acceptedPayload occurrenceIds IsU128 IsI128
  sender_mem_ordered_roles recipient_mem_ordered_roles fee_owner_mem_ordered_roles delta_untouched)
end T
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes ValidToken)
end B
namespace C
export CanonicalEpochEconomicRowsV1 (sortOn sortOn_perm mem_sortOn)
end C
namespace S
export AssetTransferSparseTablesV1 (accounts perm_sum_int)
end S

attribute [local instance] lexOrd

def liftMovements (kind : EffectKind) (asset : String) (rows : List T.MovementRow) : List EconomicEffectRow :=
  rows.map (fun row => ⟨kind, row.principal, asset, S.accounts, row.deltaAtoms⟩)

def transferRawRows (pre : T.TransferState) (command : T.Command) : List EconomicEffectRow :=
  liftMovements .accountMovement command.asset (T.acceptedPayload pre command).movements ++
  liftMovements .feeAllocation command.asset (T.acceptedPayload pre command).feeAllocations

def transferConservation (pre post : FT.State) (command : T.Command) : AssetConservationRow :=
  ⟨command.asset, amountForAsset pre.balances command.asset, amountForAsset post.balances command.asset,
    supplyFor (numericRows pre.supplies) command.asset, supplyFor (numericRows post.supplies) command.asset, 0, 0⟩

def transferFees (asset : String) (fee : Int) : List FeeConservationRow :=
  if fee = 0 then [] else [⟨asset, fee, fee, 0⟩]

/-- POST and the selected policy are read from the finite transition's own
inputs and result. Rejection returns the existing empty core plan. -/
def transferPlan (digest : B.Bytes → T.Root) (ctx : T.Context) (pre : FT.State) (command : T.Command) : EffectPlan :=
  let result := FT.transition digest ctx pre command
  match result.verdict with
  | .rejected _ => EffectPlan.empty
  | .accepted =>
    match FT.policyFor pre command.asset with
    | none => EffectPlan.empty
    | some policy =>
      ⟨C.sortOn effectWire (transferRawRows (FT.project pre policy) command),
        [transferConservation pre result.post command], transferFees command.asset policy.transferFeeAtoms,
        [⟨.assetTransfer, FT.stateRoot digest pre, FT.stateRoot digest result.post⟩], T.occurrenceIds ctx, []⟩

theorem transfer_rejected_empty {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} {code : AssetTransferFiniteOutcomeV2.RejectCode}
    (rejected : (FT.transition digest ctx pre command).verdict = .rejected code) :
    transferPlan digest ctx pre command = EffectPlan.empty := by
  simp only [transferPlan, rejected]

theorem movementRows_member (pre : T.TransferState) (command : T.Command) (roles : List String) :
    ∀ row ∈ T.movementRows pre command roles,
      row.principal ∈ roles ∧ row.deltaAtoms = T.delta pre command row.principal ∧ row.deltaAtoms ≠ 0 := by
  induction roles with
  | nil => simp [T.movementRows]
  | cons owner rest ih =>
    intro row member
    unfold T.movementRows at member
    split at member
    · have parts := ih row member
      exact ⟨List.mem_cons_of_mem owner parts.1, parts.2⟩
    · rename_i nonzero
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨List.mem_cons_self, rfl, nonzero⟩
      · have parts := ih row member
        exact ⟨List.mem_cons_of_mem owner parts.1, parts.2⟩

theorem movementRows_principals_unique (pre : T.TransferState) (command : T.Command)
    (roles : List String) (unique : roles.Nodup) :
    ((T.movementRows pre command roles).map (fun row => row.principal)).Nodup := by
  induction roles with
  | nil => simp [T.movementRows]
  | cons owner rest ih =>
    have parts := List.nodup_cons.mp unique
    unfold T.movementRows
    split
    · exact ih parts.2
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih parts.2⟩
      intro member
      obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
      exact parts.1 (same ▸ (movementRows_member pre command rest row rowMember).1)

theorem lift_wire_unique (kind : EffectKind) (asset : String) (rows : List T.MovementRow)
    (unique : (rows.map (fun row => row.principal)).Nodup) :
    ((liftMovements kind asset rows).map effectWire).Nodup := by
  rw [liftMovements, List.map_map]
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp unique).imp
  intro left right different same
  exact different (congrArg (fun wire : String × String × String × String => wire.2.2.1) same)

theorem transfer_raw_unique (pre : T.TransferState) (command : T.Command)
    (distinct : command.sender ≠ command.recipient) :
    ((transferRawRows pre command).map effectWire).Nodup := by
  have movements := lift_wire_unique .accountMovement command.asset _
    (movementRows_principals_unique pre command _
      (AssetTransferFiniteAccountingV2.ordered_roles_unique pre command distinct))
  unfold transferRawRows T.acceptedPayload
  rw [List.map_append, List.nodup_append]
  refine ⟨movements, ?_, ?_⟩
  · split <;> simp [liftMovements]
  · intro left leftMember right rightMember same
    obtain ⟨leftRow, leftIn, leftWire⟩ := List.mem_map.mp leftMember
    obtain ⟨rightRow, rightIn, rightWire⟩ := List.mem_map.mp rightMember
    obtain ⟨leftMove, _, leftEq⟩ := List.mem_map.mp leftIn
    obtain ⟨rightMove, _, rightEq⟩ := List.mem_map.mp rightIn
    rw [← leftWire, ← rightWire, ← leftEq, ← rightEq] at same
    have kinds := congrArg (fun wire : String × String × String × String => wire.1) same
    change EffectKind.accountMovement.code = EffectKind.feeAllocation.code at kinds
    contradiction

theorem transfer_rows_admitted {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    ∀ row ∈ (transferPlan digest ctx pre command).rows, EffectRowAdmitted row := by
  obtain ⟨policy, selected, _, _⟩ := FT.accepted_selected_leaf ⟨fun _ => ""⟩ structural.balanceUnique accepted
  have bounds := FT.accepted_payload_bounds selected accepted
  have feeLower := (structural.policyFee policy (FT.policyFor_spec selected).1).1
  intro row member
  simp only [transferPlan, accepted, selected, C.mem_sortOn, transferRawRows, List.mem_append] at member
  rcases member with member | member
  · simp only [liftMovements] at member
    obtain ⟨movement, movementMember, rfl⟩ := List.mem_map.mp member
    have width := bounds.2.2.1 movement movementMember
    simpa [EffectRowAdmitted] using width
  · change row ∈ liftMovements .feeAllocation command.asset
      (if policy.transferFeeAtoms = 0 then [] else [⟨policy.feeOwner, policy.transferFeeAtoms⟩]) at member
    by_cases zero : policy.transferFeeAtoms = 0
    · simp [zero, liftMovements] at member
    · simp only [zero, if_false, liftMovements, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst row
      have positive : 0 < policy.transferFeeAtoms := by omega
      simpa [EffectRowAdmitted, zero, positive] using bounds.2.2.2

theorem transfer_conservation_admitted {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    AssetConservationAdmitted (transferConservation pre (FT.transition digest ctx pre command).post command) := by
  have before := covered_quantities_u128 pre.balances pre.supplies structural.balancePositive
    structural.supplyUnique structural.supplyU128 structural.accountCover command.asset
  have same := FT.accepted_accounting structural.balanceUnique accepted command.asset
  have zero : FitsU128 0 := by unfold FitsU128; decide
  simp only [transferConservation, AssetConservationAdmitted, same.1, same.2, Int.add_zero, Int.sub_zero]
  exact ⟨before.1, before.1, before.2, before.2, zero, zero, trivial, trivial⟩

theorem transfer_fees_admitted (asset : String) (fee : Int) (bounded : FitsU128 fee) :
    ∀ row ∈ transferFees asset fee, FeeConservationAdmitted row := by
  intro row member
  unfold transferFees at member
  split at member
  · simp only [List.not_mem_nil] at member
  · have same := List.mem_singleton.mp member
    subst row
    exact ⟨bounded, bounded, zero_fits_u128, by simp⟩

private theorem sum_int_append (left right : List Int) : (left ++ right).sum = left.sum + right.sum := by
  induction left with
  | nil => simp
  | cons head rest ih =>
    simp only [List.cons_append, List.sum_cons, ih]
    omega

private theorem sum_zero_rows {α : Type} (rows : List α) : (rows.map (fun _ => (0 : Int))).sum = 0 :=
  AssetTransferSparseTablesV1.sum_map_zero rows _ (fun _ _ => rfl)

theorem transfer_projection {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    ProjectionMatches (transferPlan digest ctx pre command) := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  intro asset
  have issued := S.perm_sum_int
    ((C.sortOn_perm effectWire (transferRawRows (FT.project pre policy) command)).map (issueContribution asset))
  have burned := S.perm_sum_int
    ((C.sortOn_perm effectWire (transferRawRows (FT.project pre policy) command)).map (burnContribution asset))
  change issuedFor asset (C.sortOn effectWire (transferRawRows (FT.project pre policy) command)) =
    issuedFor asset (transferRawRows (FT.project pre policy) command) at issued
  change burnedFor asset (C.sortOn effectWire (transferRawRows (FT.project pre policy) command)) =
    burnedFor asset (transferRawRows (FT.project pre policy) command) at burned
  simp only [transferPlan, accepted, selected]
  rw [issued, burned]
  simp [declaredIssueFor, declaredBurnFor, transferConservation, issuedFor, burnedFor,
    transferRawRows, liftMovements, List.map_map, Function.comp_def, issueContribution, burnContribution,
    sum_int_append, sum_zero_rows]

theorem transfer_fee_projection {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    FeeProjectionMatches (transferPlan digest ctx pre command) := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  intro asset
  have fees := S.perm_sum_int ((C.sortOn_perm effectWire (transferRawRows (FT.project pre policy) command)).map
    (feeAllocationContribution asset))
  change allocatedFeeFor asset (C.sortOn effectWire (transferRawRows (FT.project pre policy) command)) =
    allocatedFeeFor asset (transferRawRows (FT.project pre policy) command) at fees
  simp only [transferPlan, accepted, selected]
  rw [fees]
  by_cases zero : policy.transferFeeAtoms = 0 <;>
    simp [declaredCurrentAllocationsFor, allocatedFeeFor, transferFees, transferRawRows, liftMovements,
      List.map_map, Function.comp_def, feeAllocationContribution, T.acceptedPayload, FT.project,
      AssetTransferFiniteAccountingV2.project, zero, sum_int_append, sum_zero_rows]

theorem transfer_keys_ordered {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    PlanKeysUnique (transferPlan digest ctx pre command) ∧ PlanOrdered (transferPlan digest ctx pre command) := by
  obtain ⟨policy, selected, scalar, _⟩ := FT.accepted_selected_leaf ⟨fun _ => ""⟩ structural.balanceUnique accepted
  have raw := transfer_raw_unique (FT.project pre policy) command (AssetTransferFiniteAccountingV2.accepted_distinct scalar)
  have unique := sorted_wire_unique _ raw
  have keys := effect_key_of_wire_unique _ unique
  have strict := sorted_rows_strict _ raw
  by_cases zero : policy.transferFeeAtoms = 0 <;> cases occurrence : ctx.occurrence <;>
    simp only [transferPlan, accepted, selected, PlanKeysUnique, PlanOrdered, transferFees, zero, if_true, if_false,
      T.occurrenceIds, occurrence] <;> simpa using And.intro keys strict

theorem transfer_items {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    (transferPlan digest ctx pre command).rows.length ≤ 4 ∧
      PlanWithinItemBounds (transferPlan digest ctx pre command) := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  have bounds := FT.accepted_payload_bounds selected accepted
  have count : (C.sortOn effectWire (transferRawRows (FT.project pre policy) command)).length ≤ 4 := by
    rw [(C.sortOn_perm effectWire _).length_eq]
    simp only [transferRawRows, List.length_append, liftMovements, List.length_map]
    exact Nat.le_trans (Nat.add_le_add bounds.1 bounds.2.1) (by decide)
  by_cases zero : policy.transferFeeAtoms = 0 <;> cases occurrence : ctx.occurrence <;>
    simp only [transferPlan, accepted, selected, PlanWithinItemBounds, transferFees, zero, if_true, if_false,
      T.occurrenceIds, occurrence, List.length_cons, List.length_nil] <;> omega

theorem transfer_plan_admitted {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    EffectPlanAdmitted (transferPlan digest ctx pre command) := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  constructor
  · exact transfer_rows_admitted structural accepted
  constructor
  · intro row member
    simp only [transferPlan, accepted, selected, List.mem_singleton] at member
    subst row
    exact transfer_conservation_admitted structural accepted
  constructor
  · intro row member
    simp only [transferPlan, accepted, selected] at member
    exact transfer_fees_admitted command.asset policy.transferFeeAtoms
      (structural.policyFee policy (FT.policyFor_spec selected).1) row member
  exact ⟨transfer_projection accepted, transfer_fee_projection accepted,
    (transfer_items accepted).2, (transfer_keys_ordered structural accepted).1⟩

theorem transfer_asset_token {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) : B.ValidToken command.asset := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  have registered := AssetTransferFiniteOutcomeV2.structural_registered structural selected
  obtain ⟨row, member, same⟩ := List.mem_map.mp registered
  exact same ▸ structural.supplyTokens row member

theorem transfer_plan_tokens {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (structural : FT.Structural pre) (commandAdmitted : FT.CommandAdmission command)
    (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    PlanTokens (transferPlan digest ctx pre command) := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  have assetToken := transfer_asset_token structural accepted
  have feeToken := structural.feeOwnerTokens policy (FT.policyFor_spec selected).1
  have roleTokens := FT.ordered_roles_tokens (FT.project pre policy) command commandAdmitted.2.1 commandAdmitted.2.2 feeToken
  have domainToken : B.ValidToken S.accounts := by unfold B.ValidToken; decide
  constructor
  · intro row member
    simp only [transferPlan, accepted, selected, C.mem_sortOn, transferRawRows, List.mem_append] at member
    rcases member with member | member
    · simp only [liftMovements] at member
      obtain ⟨movement, movementMember, rfl⟩ := List.mem_map.mp member
      exact ⟨roleTokens movement.principal (movementRows_member _ _ _ movement movementMember).1, assetToken, domainToken⟩
    · change row ∈ liftMovements .feeAllocation command.asset
        (if policy.transferFeeAtoms = 0 then [] else [⟨policy.feeOwner, policy.transferFeeAtoms⟩]) at member
      split at member
      · simp [liftMovements] at member
      · simp only [liftMovements, List.map_cons, List.map_nil, List.mem_singleton] at member
        subst row
        exact ⟨feeToken, assetToken, domainToken⟩
  constructor
  · intro row member
    simp only [transferPlan, accepted, selected, List.mem_singleton] at member
    subst row
    exact assetToken
  · intro row member
    simp only [transferPlan, accepted, selected, transferFees] at member
    split at member
    · simp only [List.not_mem_nil] at member
    · have same := List.mem_singleton.mp member
      subst row
      exact assetToken

theorem transfer_accepted_fields {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (accepted : (FT.transition digest ctx pre command).verdict = .accepted) :
    ∃ policy occurrence, FT.policyFor pre command.asset = some policy ∧ ctx.occurrence = some occurrence ∧
      transferPlan digest ctx pre command =
        ⟨C.sortOn effectWire (transferRawRows (FT.project pre policy) command),
          [transferConservation pre (FT.transition digest ctx pre command).post command],
          transferFees command.asset policy.transferFeeAtoms,
          [⟨.assetTransfer, FT.stateRoot digest pre, FT.stateRoot digest (FT.transition digest ctx pre command).post⟩],
          [occurrence.occurrenceId], []⟩ := by
  obtain ⟨policy, occurrence, selected, present, _⟩ := FT.accepted_effects_bind accepted
  exact ⟨policy, occurrence, selected, present,
    by simp only [transferPlan, accepted, selected, T.occurrenceIds, present]⟩

/-! Per-owner attribution, with the zero-filter/coalescing algebra supplied by the parent proof worker. -/

def movementSum (owner : String) (rows : List T.MovementRow) : Int :=
  (rows.map (fun row => if row.principal = owner then row.deltaAtoms else 0)).sum

theorem movement_sum_unique (pre : T.TransferState) (command : T.Command)
    (owners : List String) (unique : owners.Nodup) (owner : String) :
    movementSum owner (T.movementRows pre command owners) =
      if owner ∈ owners then T.delta pre command owner else 0 := by
  induction owners with
  | nil => simp [T.movementRows, movementSum]
  | cons head rest ih =>
      have parts := List.nodup_cons.mp unique
      have tail := ih parts.2
      by_cases same : head = owner
      · subst head
        by_cases zero : T.delta pre command owner = 0
        · simp [T.movementRows, zero, tail]
        · simp only [T.movementRows, if_neg zero, movementSum, List.map_cons, List.sum_cons,
            if_true, List.mem_cons_self]
          change T.delta pre command owner + movementSum owner (T.movementRows pre command rest) = _
          rw [tail, if_neg parts.1]
          simp
      · by_cases zero : T.delta pre command head = 0
        · simp [T.movementRows, zero, tail, Ne.symm same]
        · simp only [T.movementRows, if_neg zero, movementSum, List.map_cons, List.sum_cons,
            if_neg same, Int.zero_add]
          change movementSum owner (T.movementRows pre command rest) = _
          simpa [Ne.symm same] using tail

theorem ordered_movement_sum (pre : T.TransferState) (command : T.Command)
    (distinct : command.sender ≠ command.recipient) (owner : String) :
    movementSum owner (T.movementRows pre command (T.orderedRoles pre command)) =
      T.delta pre command owner := by
  rw [movement_sum_unique pre command _
    (AssetTransferFiniteAccountingV2.ordered_roles_unique pre command distinct)]
  by_cases member : owner ∈ T.orderedRoles pre command
  · exact if_pos member
  · have sender : owner ≠ command.sender := by
      intro same
      exact member (same ▸ T.sender_mem_ordered_roles pre command)
    have recipient : owner ≠ command.recipient := by
      intro same
      exact member (same ▸ T.recipient_mem_ordered_roles pre command)
    have collector : owner ≠ pre.policy.feeOwner := by
      intro same
      exact member (same ▸ T.fee_owner_mem_ordered_roles pre command)
    rw [if_neg member, T.delta_untouched sender recipient collector]

theorem lifted_movement_effect (kind queryKind : EffectKind)
    (asset owner queryAsset domain : String) (movements : List T.MovementRow) :
    AssetTransferSparseTablesV1.rowsEffect queryKind owner queryAsset domain
      (liftMovements kind asset movements) =
        if kind = queryKind ∧ asset = queryAsset ∧ AssetTransferSparseTablesV1.accounts = domain then
          movementSum owner movements else 0 := by
  induction movements with
  | nil => simp [liftMovements, AssetTransferSparseTablesV1.rowsEffect, movementSum]
  | cons row rest ih =>
      simp only [liftMovements, List.map_cons, AssetTransferSparseTablesV1.rowsEffect,
        List.sum_cons] at ih ⊢
      rw [ih]
      simp only [movementSum, List.map_cons, List.sum_cons]
      by_cases key : kind = queryKind ∧ asset = queryAsset ∧ AssetTransferSparseTablesV1.accounts = domain
      · by_cases ownerMatch : row.principal = owner <;>
          simp [key.1, key.2.1, key.2.2, ownerMatch]
      · have mismatch : ¬(kind = queryKind ∧ row.principal = owner ∧ asset = queryAsset ∧
              AssetTransferSparseTablesV1.accounts = domain) := fun all => key ⟨all.1, all.2.2⟩
        simp only [if_neg mismatch, if_neg key, Int.zero_add]

theorem raw_account_effect (pre : T.TransferState) (command : T.Command)
    (distinct : command.sender ≠ command.recipient) (owner asset : String) :
    AssetTransferSparseTablesV1.rowsEffect .accountMovement owner asset AssetTransferSparseTablesV1.accounts
      (AssetTransferFiniteEffectPlanV2.transferRawRows pre command) =
        if command.asset = asset then T.delta pre command owner else 0 := by
  rw [AssetTransferFiniteEffectPlanV2.transferRawRows, AssetTransferSparseTablesV1.rowsEffect_append]
  change AssetTransferSparseTablesV1.rowsEffect .accountMovement owner asset AssetTransferSparseTablesV1.accounts
      (liftMovements .accountMovement command.asset (AssetTransferRefinementV2.acceptedPayload pre command).movements) +
    AssetTransferSparseTablesV1.rowsEffect .accountMovement owner asset AssetTransferSparseTablesV1.accounts
      (liftMovements .feeAllocation command.asset (AssetTransferRefinementV2.acceptedPayload pre command).feeAllocations) = _
  rw [lifted_movement_effect, lifted_movement_effect]
  simp only [AssetTransferRefinementV2.acceptedPayload, true_and, and_true, reduceCtorEq,
    false_and, if_false, Int.add_zero]
  rw [ordered_movement_sum pre command distinct]

theorem transfer_account_effect {digest : AssetLaneFiniteByteAccountingV2.Bytes → String}
    {ctx : AssetTransferRefinementV2.Context} {pre : AssetTransferFiniteOutcomeV2.State}
    {command : T.Command} (unique : AssetTransferSparseTablesV1.Unique pre.balances)
    (accepted : (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).verdict = .accepted)
    (owner asset : String) :
    GlobalEconomicStateRefinementV2.effectFor .accountMovement
      (AssetTransferFiniteEffectPlanV2.transferPlan digest ctx pre command) owner asset AssetTransferSparseTablesV1.accounts =
      CanonicalEpochEconomicRowsV1.lookupLast (AssetTransferSparseTablesV1.accountKey asset owner)
        (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).post.balances -
      CanonicalEpochEconomicRowsV1.lookupLast (AssetTransferSparseTablesV1.accountKey asset owner) pre.balances := by
  obtain ⟨policy, selected, scalar, _⟩ := AssetTransferFiniteOutcomeV2.accepted_selected_leaf
    ⟨fun _ => ""⟩ unique accepted
  have distinct := AssetTransferFiniteAccountingV2.accepted_distinct scalar
  have lookup := AssetTransferFiniteOutcomeV2.accepted_lookup selected unique accepted asset owner
  unfold GlobalEconomicStateRefinementV2.effectFor
  simp only [AssetTransferFiniteEffectPlanV2.transferPlan, accepted, selected]
  change AssetTransferSparseTablesV1.rowsEffect .accountMovement owner asset AssetTransferSparseTablesV1.accounts
    (CanonicalEpochEconomicRowsV1.sortOn AssetTransferSparseTablesV1.effectWire
      (AssetTransferFiniteEffectPlanV2.transferRawRows (AssetTransferFiniteOutcomeV2.project pre policy) command)) = _
  rw [AssetTransferSparseTablesV1.rowsEffect_sortOn, raw_account_effect _ command distinct]
  omega

theorem transfer_fee_effect {digest : AssetLaneFiniteByteAccountingV2.Bytes → String}
    {ctx : AssetTransferRefinementV2.Context} {pre : AssetTransferFiniteOutcomeV2.State}
    {command : T.Command} {policy : AssetTransferRefinementV2.Policy}
    (selected : AssetTransferFiniteOutcomeV2.policyFor pre command.asset = some policy)
    (accepted : (AssetTransferFiniteOutcomeV2.transition digest ctx pre command).verdict = .accepted)
    (owner asset domain : String) :
    GlobalEconomicStateRefinementV2.effectFor .feeAllocation
      (AssetTransferFiniteEffectPlanV2.transferPlan digest ctx pre command) owner asset domain =
        if policy.feeOwner = owner ∧ command.asset = asset ∧ AssetTransferSparseTablesV1.accounts = domain then
          policy.transferFeeAtoms else 0 := by
  unfold GlobalEconomicStateRefinementV2.effectFor
  simp only [AssetTransferFiniteEffectPlanV2.transferPlan, accepted, selected]
  change AssetTransferSparseTablesV1.rowsEffect .feeAllocation owner asset domain
    (CanonicalEpochEconomicRowsV1.sortOn AssetTransferSparseTablesV1.effectWire
      (AssetTransferFiniteEffectPlanV2.transferRawRows (AssetTransferFiniteOutcomeV2.project pre policy) command)) = _
  rw [AssetTransferSparseTablesV1.rowsEffect_sortOn, AssetTransferFiniteEffectPlanV2.transferRawRows,
    AssetTransferSparseTablesV1.rowsEffect_append]
  change AssetTransferSparseTablesV1.rowsEffect .feeAllocation owner asset domain
      (liftMovements .accountMovement command.asset
        (AssetTransferRefinementV2.acceptedPayload (AssetTransferFiniteOutcomeV2.project pre policy) command).movements) +
    AssetTransferSparseTablesV1.rowsEffect .feeAllocation owner asset domain
      (liftMovements .feeAllocation command.asset
        (AssetTransferRefinementV2.acceptedPayload (AssetTransferFiniteOutcomeV2.project pre policy) command).feeAllocations) = _
  rw [lifted_movement_effect, lifted_movement_effect]
  by_cases zero : policy.transferFeeAtoms = 0 <;>
    simp [AssetTransferRefinementV2.acceptedPayload, AssetTransferFiniteOutcomeV2.project,
      AssetTransferFiniteAccountingV2.project, zero, movementSum]
  by_cases key : command.asset = asset ∧ AssetTransferSparseTablesV1.accounts = domain <;>
    by_cases same : policy.feeOwner = owner <;> simp [key, same]

theorem transfer_effect_frame {digest : B.Bytes → T.Root} {ctx : T.Context} {pre : FT.State}
    {command : T.Command} (accepted : (FT.transition digest ctx pre command).verdict = .accepted)
    (kind : EffectKind) (owner asset domain : String)
    (frame : (kind ≠ .accountMovement ∧ kind ≠ .feeAllocation) ∨ command.asset ≠ asset ∨ S.accounts ≠ domain) :
    effectFor kind (transferPlan digest ctx pre command) owner asset domain = 0 := by
  obtain ⟨policy, _, selected, _⟩ := FT.accepted_effects_bind accepted
  unfold effectFor
  simp only [transferPlan, accepted, selected]
  change AssetTransferSparseTablesV1.rowsEffect kind owner asset domain
    (C.sortOn AssetTransferSparseTablesV1.effectWire (transferRawRows (FT.project pre policy) command)) = _
  rw [AssetTransferSparseTablesV1.rowsEffect_sortOn, transferRawRows,
    AssetTransferSparseTablesV1.rowsEffect_append, lifted_movement_effect, lifted_movement_effect]
  have movementKey : ¬(EffectKind.accountMovement = kind ∧ command.asset = asset ∧ S.accounts = domain) := by
    intro key
    rcases frame with kinds | assetMismatch | domainMismatch
    · exact kinds.1 key.1.symm
    · exact assetMismatch key.2.1
    · exact domainMismatch key.2.2
  have feeKey : ¬(EffectKind.feeAllocation = kind ∧ command.asset = asset ∧ S.accounts = domain) := by
    intro key
    rcases frame with kinds | assetMismatch | domainMismatch
    · exact kinds.2 key.1.symm
    · exact assetMismatch key.2.1
    · exact domainMismatch key.2.2
  simp only [if_neg movementKey, if_neg feeKey, Int.zero_add]

end Proofs.AssetTransferFiniteEffectPlanV2
