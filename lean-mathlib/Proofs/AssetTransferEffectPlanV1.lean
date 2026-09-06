import Proofs.AssetTransferPolicySelectionV1

/-!
# Constructed ASSET_TRANSFER V1 effect plans

This model completes the five structural fields that the sparse selected-policy
transfer leaves empty.  The rows remain the actual sparse `projectedPlan` rows;
the constructor adds one account-total conservation row, an optional fee row,
one asset-transfer lane write, one occurrence consumption, and no outbox row.

`CommitmentFields` carries opaque strings.  This file does not establish root
syntax, hashes, authenticated context, replay advancement, journals, receipts,
or a Python/Rust/compiler refinement.  Its admission result is structural and
does not construct `GlobalEconomicStateRefinementV2.Verified`.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferEffectPlanV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (Input Result StateAdmitted policyFor selectedInput lift step accepted_selected_step
   rejected_step_noop selectedInput_state_well_formed policyFor_some)
end K

namespace S
export Proofs.AssetTransferSparseTablesV1
  (Input Result step projectedPlan movementEffects effectWire accounts localState accepted_sparse_transfer
   accepted_step_shape rejected_step_noop step_frame projectedPlan_supply_zero disclosed_tables_refine
   perm_sum_int)
end S

namespace P
export Proofs.AssetTransferSparseSupplyV1 (accepted_account_totals)
end P

namespace T
export Proofs.AssetTransferRefinementV1
  (Policy MovementRow TransferState Command Verdict RejectCode StateWellFormed CommandWellFormed IsU128 IsI128
   transition accepted_iff_all_guards accepted_post_eq accepted_deltas_i128
   accepted_movement_rows_i128 movementRows_mem acceptedEffects roleOrder
   movementRows delta widthAdmitted i128Min i128Max i128Min_eq_pow i128Max_eq_pow
   u128Max_eq_pow)
end T

namespace G
export Proofs.GlobalEconomicStateRefinementV2
  (GlobalState AmountRow SupplyRow amountForAsset supplyFor issueDeltaFor burnDeltaFor)
end G

namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn sortOn_perm sortOn_ordered mem_sortOn)
end C

attribute [local instance] lexOrd

/-- Opaque caller-provided transport fields for the constructed lane record. -/
structure CommitmentFields where
  preLaneRoot : String
  postLaneRoot : String
  occurrenceId : String

/-- The V1 account-total and supply record.  Issue and burn are separately zero. -/
def conservationRow (input : S.Input) : AssetConservationRow :=
  { asset := input.command.asset
    ownedAndCustodiedPreAtoms := G.amountForAsset input.pre.balances input.command.asset
    ownedAndCustodiedPostAtoms :=
      G.amountForAsset (S.step input).post.balances input.command.asset
    supplyPreAtoms := G.supplyFor input.pre.supplies input.command.asset
    supplyPostAtoms := G.supplyFor (S.step input).post.supplies input.command.asset
    authorizedIssueAtoms := 0
    authorizedBurnAtoms := 0 }

/-- The runtime omits a fee annotation when the selected fee is zero. -/
def feeRows (input : S.Input) : List FeeConservationRow :=
  if input.policy.transferFeeAtoms = 0 then []
  else [{ asset := input.command.asset
          feeChargedAtoms := input.policy.transferFeeAtoms
          currentAllocationsAtoms := input.policy.transferFeeAtoms
          carriedResidueAtoms := 0 }]

/-- Complete the sparse selected-policy plan using the runtime's six field shape. -/
def selectedPlan (fields : CommitmentFields) (input : S.Input) : EffectPlan :=
  { S.projectedPlan input with
    assetConservation := [conservationRow input]
    feeConservation := feeRows input
    laneWrites := [{ laneId := .assetTransfer
                     preRoot := fields.preLaneRoot
                     postRoot := fields.postLaneRoot }]
    occurrenceConsumptions := [fields.occurrenceId]
    externalOutboxEnqueue := [] }

/-- Private transport over a previously evaluated policy-selection result. -/
private def completeResult (fields : CommitmentFields) (input : K.Input)
    (output : K.Result) : K.Result :=
  match output.verdict with
  | .accepted =>
      match K.policyFor input.pre.policies input.command.asset with
      | some policy => { output with plan := selectedPlan fields (K.selectedInput input policy) }
      | none => output
  | .rejected _ => output

/-- Evaluate the policy-selection front door, changing only an accepted plan. -/
def complete (fields : CommitmentFields) (input : K.Input) : K.Result :=
  completeResult fields input (K.step input)

theorem selectedPlan_rows (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).rows = (S.projectedPlan input).rows := rfl

theorem selectedPlan_asset_conservation (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).assetConservation = [conservationRow input] := rfl

theorem selectedPlan_fee_conservation (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).feeConservation = feeRows input := rfl

theorem selectedPlan_lane_writes (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).laneWrites =
      [{ laneId := .assetTransfer, preRoot := fields.preLaneRoot, postRoot := fields.postLaneRoot }] := rfl

theorem selectedPlan_occurrences (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).occurrenceConsumptions = [fields.occurrenceId] := rfl

theorem selectedPlan_outbox (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).externalOutboxEnqueue = [] := rfl

theorem selectedPlan_rows_sorted (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).rows.Pairwise
      (fun left right => (compare (S.effectWire left) (S.effectWire right)).isLE = true) := by
  exact C.sortOn_ordered S.effectWire _

private theorem movement_principals_sublist (d : String → Int) (owners : List String) :
    ((T.movementRows d owners).map (fun row => row.principal)).Sublist owners := by
  induction owners with
  | nil => simp [T.movementRows]
  | cons owner owners ih =>
      simp only [T.movementRows]
      split
      · exact List.Sublist.cons owner ih
      · exact List.Sublist.cons₂ owner ih

private theorem role_order_nodup (pre : T.TransferState) (cmd : T.Command)
    (distinct : cmd.sender ≠ cmd.recipient) : (T.roleOrder pre cmd).Nodup := by
  unfold T.roleOrder
  split
  · simp [distinct]
  · rename_i absent
    have hs : cmd.sender ≠ pre.policy.feeOwner := fun h => absent (Or.inl h.symm)
    have hr : cmd.recipient ≠ pre.policy.feeOwner := fun h => absent (Or.inr h.symm)
    simp [distinct, hs, hr]

private theorem movement_effect_keys_nodup (kind : EffectKind) (asset : String)
    (rows : List T.MovementRow)
    (unique : (rows.map (fun row => row.principal)).Nodup) :
    ((S.movementEffects kind asset rows).map EconomicEffectRow.key).Nodup := by
  let key : String → EffectKind × String × String × String :=
    fun owner => (kind, asset, owner, S.accounts)
  have mapped : ((rows.map (fun row => row.principal)).map key).Nodup :=
    List.Pairwise.map key
      (fun _ _ different same => different (congrArg (fun k => k.2.2.1) same)) unique
  simpa only [List.map_map, S.movementEffects, EconomicEffectRow.key, Function.comp_def, key]
    using mapped

private theorem movement_effect_key_kind (kind : EffectKind) (asset : String)
    (rows : List T.MovementRow) (key : EffectKind × String × String × String)
    (member : key ∈ (S.movementEffects kind asset rows).map EconomicEffectRow.key) :
    key.1 = kind := by
  simp only [S.movementEffects, List.map_map, List.mem_map] at member
  obtain ⟨row, _, rfl⟩ := member
  rfl

/-- Accepted sparse rows retain distinct runtime effect keys after sorting. -/
theorem projectedPlan_keys_unique {input : S.Input}
    (accepted : (S.step input).verdict = .accepted) :
    ((S.projectedPlan input).rows.map EconomicEffectRow.key).Nodup := by
  have distinct : input.command.sender ≠ input.command.recipient :=
    ((T.accepted_iff_all_guards input.context (S.localState input) input.command).mp
      (S.accepted_step_shape accepted).1) .selfTransfer
  let effects := T.acceptedEffects (S.localState input) input.command
  have hm : (effects.movements.map (fun row => row.principal)).Nodup :=
    (movement_principals_sublist _ _).nodup (role_order_nodup _ _ distinct)
  have hf : (effects.feeAllocations.map (fun row => row.principal)).Nodup := by
    simp only [effects, T.acceptedEffects]
    split <;> simp
  have raw : ((S.movementEffects .accountMovement input.command.asset effects.movements ++
      S.movementEffects .feeAllocation input.command.asset effects.feeAllocations).map
        EconomicEffectRow.key).Nodup := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨movement_effect_keys_nodup _ _ _ hm, movement_effect_keys_nodup _ _ _ hf, ?_⟩
    intro left leftMem right rightMem same
    have hleft := movement_effect_key_kind _ _ _ left leftMem
    have hright := movement_effect_key_kind _ _ _ right rightMem
    have impossible : EffectKind.accountMovement = .feeAllocation := by
      rw [← hleft, ← hright, same]
    cases impossible
  exact raw.perm ((C.sortOn_perm S.effectWire _).symm.map EconomicEffectRow.key)

private theorem account_rows_allocate_no_fees (asset rowAsset : String)
    (rows : List T.MovementRow) :
    allocatedFeeFor asset (S.movementEffects .accountMovement rowAsset rows) = 0 := by
  unfold allocatedFeeFor S.movementEffects
  rw [List.map_map]
  apply Proofs.AssetTransferSparseTablesV1.sum_map_zero
  intro row _
  simp [feeAllocationContribution]

private theorem allocated_fee_append (asset : String) (left right : List EconomicEffectRow) :
    allocatedFeeFor asset (left ++ right) =
      allocatedFeeFor asset left + allocatedFeeFor asset right := by
  unfold allocatedFeeFor
  induction left with
  | nil => simp
  | cons row rest ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- The optional fee annotation is exactly the fee-allocation row projection. -/
theorem selectedPlan_fee_projection (fields : CommitmentFields) (input : S.Input) :
    FeeProjectionMatches (selectedPlan fields input) := by
  intro asset
  let effects := T.acceptedEffects (S.localState input) input.command
  let movements := S.movementEffects .accountMovement input.command.asset effects.movements
  let fees := S.movementEffects .feeAllocation input.command.asset effects.feeAllocations
  have sorted : allocatedFeeFor asset (S.projectedPlan input).rows =
      allocatedFeeFor asset (movements ++ fees) :=
    S.perm_sum_int ((C.sortOn_perm S.effectWire _).map (feeAllocationContribution asset))
  change declaredCurrentAllocationsFor asset (feeRows input) =
    allocatedFeeFor asset (S.projectedPlan input).rows
  rw [sorted, allocated_fee_append, account_rows_allocate_no_fees]
  by_cases zeroFee : input.policy.transferFeeAtoms = 0
  · simp [feeRows, zeroFee, fees, effects, T.acceptedEffects, S.localState,
      S.movementEffects, declaredCurrentAllocationsFor, allocatedFeeFor]
  · simp [feeRows, zeroFee, fees, effects, T.acceptedEffects, S.localState,
      S.movementEffects, declaredCurrentAllocationsFor, allocatedFeeFor, feeAllocationContribution]

/-- The constructed conservation row preserves separate zero issue and burn projections. -/
theorem selectedPlan_projection (fields : CommitmentFields) (input : S.Input) :
    ProjectionMatches (selectedPlan fields input) := by
  intro asset
  constructor
  · change declaredIssueFor asset [conservationRow input] =
      issuedFor asset (S.projectedPlan input).rows
    simpa [declaredIssueFor, conservationRow, G.issueDeltaFor] using
      (S.projectedPlan_supply_zero input asset).1.symm
  · change declaredBurnFor asset [conservationRow input] =
      burnedFor asset (S.projectedPlan input).rows
    simpa [declaredBurnFor, conservationRow, G.burnDeltaFor] using
      (S.projectedPlan_supply_zero input asset).2.symm

private theorem movementRows_length_le (d : String → Int) :
    ∀ owners, (T.movementRows d owners).length ≤ owners.length
  | [] => by simp [T.movementRows]
  | owner :: owners => by
      simp only [T.movementRows]
      split
      · exact Nat.le_trans (movementRows_length_le d owners) (Nat.le_succ _)
      · simpa only [List.length_cons] using Nat.succ_le_succ (movementRows_length_le d owners)

private theorem roleOrder_length_le_three (pre : T.TransferState) (command : T.Command) :
    (T.roleOrder pre command).length ≤ 3 := by
  unfold T.roleOrder
  split <;> simp

/-- The runtime role list has at most three accounts plus at most one fee row. -/
theorem selectedPlan_rows_length_le_four (fields : CommitmentFields) (input : S.Input) :
    (selectedPlan fields input).rows.length ≤ 4 := by
  let effects := T.acceptedEffects (S.localState input) input.command
  change (C.sortOn S.effectWire
    (S.movementEffects .accountMovement input.command.asset effects.movements ++
      S.movementEffects .feeAllocation input.command.asset effects.feeAllocations)).length ≤ 4
  rw [(C.sortOn_perm S.effectWire _).length_eq]
  simp only [List.length_append, S.movementEffects, List.length_map]
  have movementBound := movementRows_length_le
    (T.delta (S.localState input) input.command)
    (T.roleOrder (S.localState input) input.command)
  have rolesBound := roleOrder_length_le_three (S.localState input) input.command
  simp only [effects, T.acceptedEffects]
  split <;> simp only [List.length_nil, List.length_cons] <;> omega

private theorem selectedPlan_within_item_bounds (fields : CommitmentFields) (input : S.Input) :
    PlanWithinItemBounds (selectedPlan fields input) := by
  have rowBound : (S.projectedPlan input).rows.length ≤ 4 := by
    simpa only [selectedPlan_rows] using selectedPlan_rows_length_le_four fields input
  by_cases zeroFee : input.policy.transferFeeAtoms = 0
  · simp [PlanWithinItemBounds, selectedPlan, feeRows, zeroFee]
    omega
  · simp [PlanWithinItemBounds, selectedPlan, feeRows, zeroFee]
    omega

private theorem selectedPlan_keys_unique (fields : CommitmentFields) {input : S.Input}
    (accepted : (S.step input).verdict = .accepted) :
    PlanKeysUnique (selectedPlan fields input) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [selectedPlan_rows] using projectedPlan_keys_unique accepted
  · simp [selectedPlan]
  · by_cases zeroFee : input.policy.transferFeeAtoms = 0 <;>
      simp [selectedPlan, feeRows, zeroFee]
  · simp [selectedPlan]
  · simp [selectedPlan]
  · simp [selectedPlan]

private theorem isU128_fitsU128 {atoms : Int} (bounded : T.IsU128 atoms) : FitsU128 atoms := by
  simpa only [T.IsU128, T.u128Max_eq_pow, FitsU128, maxU128] using bounded

private theorem isI128_fitsI128 {atoms : Int} (bounded : T.IsI128 atoms) : FitsI128 atoms := by
  simpa only [T.IsI128, T.i128Min_eq_pow, T.i128Max_eq_pow, FitsI128, minI128, maxI128]
    using bounded

private theorem conservation_row_admitted {input : K.Input} {policy : T.Policy}
    (admitted : K.StateAdmitted input.pre)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (accepted : (S.step (K.selectedInput input policy)).verdict = .accepted) :
    AssetConservationAdmitted (conservationRow (K.selectedInput input policy)) := by
  have localWellFormed := K.selectedInput_state_well_formed admitted selection
  have policyAsset := (K.policyFor_some selection).2
  have accountLower : 0 ≤ G.amountForAsset input.pre.economic.balances input.command.asset :=
    Proofs.AssetTransferPolicySelectionV1.amountForAsset_nonnegative _
      (fun row member => (admitted.1.2.1 row member).2.1) _
  have supplyBound : FitsU128
      (G.supplyFor input.pre.economic.supplies input.command.asset) := by
    have selectedSupply := localWellFormed.supply
    change T.IsU128 (G.supplyFor input.pre.economic.supplies policy.asset) at selectedSupply
    rw [policyAsset] at selectedSupply
    exact isU128_fitsU128 selectedSupply
  have accountBound : FitsU128
      (G.amountForAsset input.pre.economic.balances input.command.asset) := by
    refine ⟨accountLower, ?_⟩
    rcases supplyBound with ⟨_, supplyUpper⟩
    have covered := admitted.2.2.2.2 input.command.asset
    omega
  have accountPost :
      G.amountForAsset (S.step (K.selectedInput input policy)).post.balances input.command.asset =
        G.amountForAsset input.pre.economic.balances input.command.asset := by
    simpa only [K.selectedInput] using
      P.accepted_account_totals admitted.1.1 accepted input.command.asset
  have supplyPost :
      G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset =
        G.supplyFor input.pre.economic.supplies input.command.asset := by
    rw [S.step_frame (K.selectedInput input policy)]
    rfl
  change FitsU128 (G.amountForAsset input.pre.economic.balances input.command.asset) ∧
    FitsU128 (G.amountForAsset (S.step (K.selectedInput input policy)).post.balances
      input.command.asset) ∧
    FitsU128 (G.supplyFor input.pre.economic.supplies input.command.asset) ∧
    FitsU128 (G.supplyFor (S.step (K.selectedInput input policy)).post.supplies
      input.command.asset) ∧
    FitsU128 0 ∧ FitsU128 0 ∧
    G.amountForAsset (S.step (K.selectedInput input policy)).post.balances input.command.asset =
      G.amountForAsset input.pre.economic.balances input.command.asset + 0 - 0 ∧
    G.supplyFor (S.step (K.selectedInput input policy)).post.supplies input.command.asset =
      G.supplyFor input.pre.economic.supplies input.command.asset + 0 - 0
  refine ⟨accountBound, ?_, supplyBound, ?_, zero_fits_u128, zero_fits_u128, ?_, ?_⟩
  · rw [accountPost]
    exact accountBound
  · rw [supplyPost]
    exact supplyBound
  · rw [accountPost]
    omega
  · rw [supplyPost]
    omega

private theorem fee_rows_admitted {input : K.Input} {policy : T.Policy}
    (admitted : K.StateAdmitted input.pre)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    ∀ row ∈ feeRows (K.selectedInput input policy), FeeConservationAdmitted row := by
  have localWellFormed := K.selectedInput_state_well_formed admitted selection
  have feeBound := localWellFormed.fee
  change T.IsU128 policy.transferFeeAtoms at feeBound
  have feeFits := isU128_fitsU128 feeBound
  change ∀ row ∈
    (if policy.transferFeeAtoms = 0 then ([] : List FeeConservationRow) else
      [{ asset := input.command.asset
         feeChargedAtoms := policy.transferFeeAtoms
         currentAllocationsAtoms := policy.transferFeeAtoms
         carriedResidueAtoms := 0 }]), FeeConservationAdmitted row
  by_cases zeroFee : policy.transferFeeAtoms = 0
  · simp [zeroFee]
  · intro row member
    have rowEq : row =
        { asset := input.command.asset
          feeChargedAtoms := policy.transferFeeAtoms
          currentAllocationsAtoms := policy.transferFeeAtoms
          carriedResidueAtoms := 0 } := by
      simpa [zeroFee] using member
    subst row
    refine ⟨feeFits, feeFits, zero_fits_u128, ?_⟩
    change policy.transferFeeAtoms = policy.transferFeeAtoms + 0
    omega

private theorem selectedPlan_rows_admitted (fields : CommitmentFields) {input : K.Input}
    {policy : T.Policy} (admitted : K.StateAdmitted input.pre)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (accepted : (S.step (K.selectedInput input policy)).verdict = .accepted) :
    ∀ row ∈ (selectedPlan fields (K.selectedInput input policy)).rows, EffectRowAdmitted row := by
  let selected := K.selectedInput input policy
  let effects := T.acceptedEffects (S.localState selected) selected.command
  have localWellFormed := K.selectedInput_state_well_formed admitted selection
  have leafAccepted :
      (T.transition selected.context (S.localState selected) selected.command).verdict = .accepted :=
    (S.accepted_step_shape accepted).1
  have movementWidth : ∀ source ∈ effects.movements, FitsI128 source.deltaAtoms := by
    intro source sourceMember
    apply isI128_fitsI128
    apply T.accepted_movement_rows_i128 leafAccepted source
    rw [(T.accepted_post_eq leafAccepted).2]
    simpa only [effects] using sourceMember
  have feeWidth : FitsI128 policy.transferFeeAtoms := by
    have width :=
      ((T.accepted_iff_all_guards selected.context (S.localState selected) selected.command).mp
        leafAccepted) .effectDeltaOverflow |>.1
    change T.IsI128 policy.transferFeeAtoms at width
    exact isI128_fitsI128 width
  have feeU128 := localWellFormed.fee
  change T.IsU128 policy.transferFeeAtoms at feeU128
  have feeNonnegative : 0 ≤ policy.transferFeeAtoms := (isU128_fitsU128 feeU128).1
  intro row member
  change row ∈ C.sortOn S.effectWire
    (S.movementEffects .accountMovement input.command.asset effects.movements ++
      S.movementEffects .feeAllocation input.command.asset effects.feeAllocations) at member
  have raw := (C.mem_sortOn S.effectWire row _).mp member
  rcases List.mem_append.mp raw with movement | fee
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by
      simpa only [S.movementEffects] using movement)
    have sourceWidth := movementWidth source sourceMember
    have sourceInfo : source.deltaAtoms =
        T.delta (S.localState selected) selected.command source.principal ∧
        source.deltaAtoms ≠ 0 := by
      change source ∈ T.movementRows (T.delta (S.localState selected) selected.command)
        (T.roleOrder (S.localState selected) selected.command) at sourceMember
      exact T.movementRows_mem sourceMember
    refine ⟨sourceWidth, sourceInfo.2, ?_, ?_, ?_⟩ <;> simp
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by
      simpa only [S.movementEffects] using fee)
    change source ∈
      (if policy.transferFeeAtoms = 0 then ([] : List T.MovementRow) else
        [{ principal := policy.feeOwner, deltaAtoms := policy.transferFeeAtoms }]) at sourceMember
    by_cases zeroFee : policy.transferFeeAtoms = 0
    · simp [zeroFee] at sourceMember
    · have sourceEq : source =
        { principal := policy.feeOwner, deltaAtoms := policy.transferFeeAtoms } := by
        simpa [zeroFee] using sourceMember
      subst source
      have feePositive : 0 < policy.transferFeeAtoms := by omega
      refine ⟨feeWidth, zeroFee, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro _
        exact feePositive

private theorem selectedPlan_admitted (fields : CommitmentFields) {input : K.Input} {policy : T.Policy}
    (admitted : K.StateAdmitted input.pre)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (accepted : (S.step (K.selectedInput input policy)).verdict = .accepted) :
    EffectPlanAdmitted (selectedPlan fields (K.selectedInput input policy)) := by
  refine ⟨selectedPlan_rows_admitted fields admitted selection accepted, ?_, ?_,
    selectedPlan_projection fields _, selectedPlan_fee_projection fields _,
    selectedPlan_within_item_bounds fields _, selectedPlan_keys_unique fields accepted⟩
  · rw [selectedPlan_asset_conservation]
    intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst row
    exact conservation_row_admitted admitted selection accepted
  · rw [selectedPlan_fee_conservation]
    exact fee_rows_admitted admitted selection

private theorem completeResult_preserves_verdict_post (fields : CommitmentFields) (input : K.Input)
    (output : K.Result) :
    (completeResult fields input output).verdict = output.verdict ∧
      (completeResult fields input output).post = output.post := by
  unfold completeResult
  split
  · split <;> constructor <;> rfl
  · constructor <;> rfl

private theorem completeResult_rejected {fields : CommitmentFields} {input : K.Input}
    {output : K.Result} {code : T.RejectCode} (rejected : output.verdict = .rejected code) :
    completeResult fields input output = output := by
  unfold completeResult
  rw [rejected]

theorem complete_preserves_verdict_post (fields : CommitmentFields) (input : K.Input) :
    (complete fields input).verdict = (K.step input).verdict ∧
      (complete fields input).post = (K.step input).post := by
  exact completeResult_preserves_verdict_post fields input (K.step input)

theorem complete_rejected {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}
    (rejected : (K.step input).verdict = .rejected code) :
    complete fields input = K.step input := by
  exact completeResult_rejected rejected

theorem complete_rejected_empty {fields : CommitmentFields} {input : K.Input} {code : T.RejectCode}
    (rejected : (K.step input).verdict = .rejected code) :
    (complete fields input).post = input.pre ∧ (complete fields input).plan = EffectPlan.empty := by
  rw [complete_rejected rejected]
  exact K.rejected_step_noop rejected

/-- An accepted front-door result replaces its plan using its actual selected row. -/
theorem complete_accepted_plan {fields : CommitmentFields} {input : K.Input} {policy : T.Policy}
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    (complete fields input).plan = selectedPlan fields (K.selectedInput input policy) := by
  simp [complete, completeResult, accepted, selection]

/-- Completing the five structural fields leaves the sparse movement and fee rows intact. -/
theorem complete_preserves_rows (fields : CommitmentFields) (input : K.Input) :
    (complete fields input).plan.rows = (K.step input).plan.rows := by
  cases accepted : (K.step input).verdict with
  | rejected code => rw [complete_rejected accepted]
  | accepted =>
      obtain ⟨policy, selection, selectedAccepted, selectedStep, _, _⟩ :=
        K.accepted_selected_step accepted
      rw [complete_accepted_plan accepted selection, selectedPlan_rows, selectedStep]
      simp only [K.lift]
      exact congrArg EffectPlan.rows (S.accepted_step_shape selectedAccepted).2.2.2.symm

/-- Initial selected-policy admission proves structural admission of every completed plan. -/
theorem complete_effect_plan_admitted (fields : CommitmentFields) (input : K.Input)
    (admitted : K.StateAdmitted input.pre) :
    EffectPlanAdmitted (complete fields input).plan := by
  cases accepted : (K.step input).verdict with
  | rejected code =>
      rw [complete_rejected accepted, (K.rejected_step_noop accepted).2]
      exact empty_effectPlan_admitted
  | accepted =>
      obtain ⟨policy, selection, selectedAccepted, _, _, _⟩ :=
        K.accepted_selected_step accepted
      rw [complete_accepted_plan accepted selection]
      exact selectedPlan_admitted fields admitted selection selectedAccepted

/-- Accepted completed results retain the exact sparse table and supply relations. -/
theorem complete_accepted_exact_relations {fields : CommitmentFields} {input : K.Input}
    (admitted : K.StateAdmitted input.pre)
    (accepted : (K.step input).verdict = .accepted) :
    ExactEconomicTables input.pre.economic (complete fields input).post.economic
      (complete fields input).plan ∧
    ExactSupplyEffects input.pre.economic (complete fields input).post.economic
      (complete fields input).plan := by
  obtain ⟨policy, selection, selectedAccepted, selectedStep, _, _⟩ :=
    K.accepted_selected_step accepted
  let selected := K.selectedInput input policy
  have postEq : (complete fields input).post.economic = (S.step selected).post := by
    rw [(complete_preserves_verdict_post fields input).2, selectedStep]
    simp only [K.lift, selected]
  have balances : (complete fields input).post.economic.balances =
      (S.step selected).post.balances :=
    congrArg (fun state => state.balances) postEq
  have custody : (complete fields input).post.economic.custody = input.pre.economic.custody := by
    rw [postEq, S.step_frame selected]
    rfl
  have liabilities : (complete fields input).post.economic.liabilities =
      input.pre.economic.liabilities := by
    rw [postEq, S.step_frame selected]
    rfl
  have reserves : (complete fields input).post.economic.reserves = input.pre.economic.reserves := by
    rw [postEq, S.step_frame selected]
    rfl
  have supplies : (complete fields input).post.economic.supplies = input.pre.economic.supplies := by
    rw [postEq, S.step_frame selected]
    rfl
  have effects : (complete fields input).plan.rows = (S.step selected).plan.rows := by
    rw [complete_preserves_rows fields input, selectedStep]
    simp only [K.lift, selected]
  simpa only [selected, K.selectedInput] using
    S.disclosed_tables_refine admitted.1.1 admitted.1.2.1 selectedAccepted
      balances custody liabilities reserves supplies effects

end AssetTransferEffectPlanV1
end Proofs
