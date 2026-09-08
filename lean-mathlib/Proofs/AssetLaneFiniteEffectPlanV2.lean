import Proofs.ManagedAssetFiniteOutcomeV2

/-!
Concrete six-field managed plans from finite V2 outcomes. The carrier and numeric plan
predicates are GlobalSettlementCoreV2's existing definitions. Exact ordering,
and tokens are proved separately from that numeric predicate. Root syntax, receipt and
journal construction, cryptographic authority and universal runtime/codec
correspondence remain outside this finite construction.
-/
set_option warningAsError true

namespace Proofs.AssetLaneFiniteEffectPlanV2

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2 RegisteredSupplySupportV1

namespace FM
export ManagedAssetFiniteOutcomeV2 (State Structural project candidate transition stateRoot
  policyFor policyFor_spec accepted_iff accepted_post_effects accepted_selected_leaf
  accepted_effect_delta_i128 accepted_accounting economic_candidate_structural
  project_well_formed supply_lookup_u128 amountForAsset_nonnegative)
end FM
namespace M
export ManagedAssetLifecycleRefinementV2 (Root Context Command CommandWellFormed isIssue signedAmount
  occurrenceIds accepted_authorization_guard accepted_consumes_exact_occurrence)
end M
namespace B
export AssetLaneFiniteByteAccountingV2 (Bytes ValidToken)
end B
namespace C
export CanonicalEpochEconomicRowsV1 (sortOn sortOn_perm sortOn_ordered mem_sortOn)
end C
namespace S
export AssetTransferSparseTablesV1 (accounts perm_sum_int PositiveAccounts)
end S

attribute [local instance] lexOrd

def effectWire (row : EconomicEffectRow) : String × String × String × String :=
  (row.kind.code, row.asset, row.principal, row.custodyDomain)

def managedRawRows (command : M.Command) : List EconomicEffectRow :=
  [⟨.accountMovement, command.accountOwner, command.asset, S.accounts, M.signedAmount command⟩,
   ⟨if M.isIssue command then .issue else .burn,
     command.accountOwner, command.asset, S.accounts, M.signedAmount command⟩]

def managedConservation (pre post : FM.State) (command : M.Command) : AssetConservationRow :=
  ⟨command.asset, amountForAsset pre.balances command.asset, amountForAsset post.balances command.asset,
    supplyFor (numericRows pre.supplies) command.asset, supplyFor (numericRows post.supplies) command.asset,
    if M.isIssue command then command.amountAtoms else 0,
    if M.isIssue command then 0 else command.amountAtoms⟩

/-- The successful plan reads the actual finite result; every rejected result
returns the existing six-empty-field core plan. -/
def managedPlan (digest : B.Bytes → M.Root) (ctx : M.Context) (pre : FM.State) (command : M.Command) : EffectPlan :=
  let result := FM.transition digest ctx pre command
  match result.verdict with
  | .rejected _ => EffectPlan.empty
  | .accepted =>
      ⟨C.sortOn effectWire (managedRawRows command), [managedConservation pre result.post command], [],
        [⟨.assetTransfer, FM.stateRoot digest pre, FM.stateRoot digest result.post⟩], M.occurrenceIds ctx, []⟩

def PlanOrdered (plan : EffectPlan) : Prop :=
  plan.rows.Pairwise (fun left right => compare (effectWire left) (effectWire right) = .lt) ∧
  plan.assetConservation.Pairwise (fun left right => left.asset < right.asset) ∧
  plan.feeConservation.Pairwise (fun left right => left.asset < right.asset) ∧
  plan.laneWrites.Pairwise (fun left right => left.laneId.code < right.laneId.code) ∧
  plan.occurrenceConsumptions.Pairwise (· < ·) ∧
  plan.externalOutboxEnqueue.Pairwise (fun left right => left.effectId < right.effectId)

def PlanTokens (plan : EffectPlan) : Prop :=
  (∀ row ∈ plan.rows, B.ValidToken row.principal ∧ B.ValidToken row.asset ∧ B.ValidToken row.custodyDomain) ∧
  (∀ row ∈ plan.assetConservation, B.ValidToken row.asset) ∧
  (∀ row ∈ plan.feeConservation, B.ValidToken row.asset)

theorem effect_key_of_wire_unique (rows : List EconomicEffectRow)
    (unique : (rows.map effectWire).Nodup) : (rows.map EconomicEffectRow.key).Nodup := by
  apply List.pairwise_map.mpr
  have pairs := List.pairwise_map.mp unique
  apply pairs.imp
  intro left right different same
  apply different
  exact congrArg (fun key : EffectKind × String × String × String => (key.1.code, key.2)) same

theorem sorted_wire_unique (rows : List EconomicEffectRow) (unique : (rows.map effectWire).Nodup) :
    ((C.sortOn effectWire rows).map effectWire).Nodup :=
  unique.perm ((C.sortOn_perm effectWire rows).symm.map effectWire)

theorem sorted_rows_strict (rows : List EconomicEffectRow) (unique : (rows.map effectWire).Nodup) :
    (C.sortOn effectWire rows).Pairwise (fun left right => compare (effectWire left) (effectWire right) = .lt) := by
  have ordered := C.sortOn_ordered effectWire rows
  have distinct := List.pairwise_map.mp (sorted_wire_unique rows unique)
  apply (ordered.and distinct).imp
  intro left right pair
  rcases Ordering.isLE_iff_eq_lt_or_eq_eq.mp pair.1 with lt | eq
  · exact lt
  · exact False.elim (pair.2 (Std.LawfulEqOrd.eq_of_compare eq))

theorem covered_quantities_u128 (rows : List AmountRow) (supplies : List V1SupplyRow)
    (positive : S.PositiveAccounts rows) (unique : SourceAssetKeysUnique supplies)
    (bounded : SourceRowsU128 supplies)
    (cover : ∀ asset, amountForAsset rows asset ≤ supplyFor (numericRows supplies) asset) (asset : String) :
    FitsU128 (amountForAsset rows asset) ∧ FitsU128 (supplyFor (numericRows supplies) asset) := by
  have supply := FM.supply_lookup_u128 supplies unique bounded asset
  have lower := FM.amountForAsset_nonnegative rows (fun row member => (positive row member).2.1.1) asset
  exact ⟨⟨lower, Int.le_trans (cover asset) supply.2⟩, supply⟩

theorem managed_raw_unique (command : M.Command) : ((managedRawRows command).map effectWire).Nodup := by
  by_cases issue : M.isIssue command <;> simp [managedRawRows, effectWire, issue, EffectKind.code]

theorem managed_rejected_empty {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} {code : ManagedAssetFiniteOutcomeV2.RejectCode}
    (rejected : (FM.transition digest ctx pre command).verdict = .rejected code) :
    managedPlan digest ctx pre command = EffectPlan.empty := by simp only [managedPlan, rejected]

theorem managed_amount_positive {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) : 0 < command.amountAtoms := by
  obtain ⟨policy, selected, scalar, _⟩ := FM.accepted_selected_leaf ⟨fun _ => ""⟩ structural accepted
  have nonzero := M.accepted_authorization_guard scalar (code := .zeroAmount) (by decide)
  have lower := commandAdmitted.amount.1
  change command.amountAtoms ≠ 0 at nonzero
  omega

theorem managed_rows_admitted {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    ∀ row ∈ (managedPlan digest ctx pre command).rows, EffectRowAdmitted row := by
  have positive := managed_amount_positive structural commandAdmitted accepted
  have width : FitsI128 (M.signedAmount command) := FM.accepted_effect_delta_i128 commandAdmitted accepted
  intro row member
  simp only [managedPlan, accepted, C.mem_sortOn, managedRawRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · by_cases issue : M.isIssue command <;>
      simp only [M.signedAmount, issue, if_true, if_false] at width ⊢ <;>
      simp [EffectRowAdmitted, width] <;> omega
  · by_cases issue : M.isIssue command <;>
      simp only [M.signedAmount, issue, if_true, if_false] at width ⊢ <;>
      simp [EffectRowAdmitted, width] <;> omega

theorem managed_conservation_admitted {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    AssetConservationAdmitted (managedConservation pre (FM.transition digest ctx pre command).post command) := by
  have postStructural : FM.Structural (FM.transition digest ctx pre command).post := by
    rw [(FM.accepted_post_effects accepted).1]
    exact FM.economic_candidate_structural structural commandAdmitted ownerToken
      ((FM.accepted_iff digest ctx pre command).mp accepted).1
  have before := covered_quantities_u128 pre.balances pre.supplies structural.balancePositive
    structural.supplyUnique structural.supplyU128 structural.accountCover command.asset
  have after := covered_quantities_u128 _ _ postStructural.balancePositive postStructural.supplyUnique
    postStructural.supplyU128 postStructural.accountCover command.asset
  have equation := FM.accepted_accounting structural accepted command.asset
  simp only [if_true] at equation
  have amount := commandAdmitted.amount
  have zero : FitsU128 0 := by unfold FitsU128; decide
  by_cases issue : M.isIssue command <;>
    simp only [managedConservation, AssetConservationAdmitted, M.signedAmount, issue, if_true, if_false] at equation ⊢ <;>
    exact ⟨before.1, after.1, before.2, after.2, by first | exact amount | exact zero,
      by first | exact amount | exact zero, by omega, by omega⟩

theorem managed_projection {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    ProjectionMatches (managedPlan digest ctx pre command) := by
  intro asset
  have issued := S.perm_sum_int ((C.sortOn_perm effectWire (managedRawRows command)).map (issueContribution asset))
  have burned := S.perm_sum_int ((C.sortOn_perm effectWire (managedRawRows command)).map (burnContribution asset))
  change issuedFor asset (C.sortOn effectWire (managedRawRows command)) = issuedFor asset (managedRawRows command) at issued
  change burnedFor asset (C.sortOn effectWire (managedRawRows command)) = burnedFor asset (managedRawRows command) at burned
  simp only [managedPlan, accepted]
  rw [issued, burned]
  by_cases issue : M.isIssue command <;>
    simp [declaredIssueFor, declaredBurnFor, managedConservation, issuedFor, burnedFor,
      managedRawRows, issueContribution, burnContribution, M.signedAmount, issue]

theorem managed_fee_projection {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    FeeProjectionMatches (managedPlan digest ctx pre command) := by
  intro asset
  have fees := S.perm_sum_int ((C.sortOn_perm effectWire (managedRawRows command)).map (feeAllocationContribution asset))
  change allocatedFeeFor asset (C.sortOn effectWire (managedRawRows command)) = allocatedFeeFor asset (managedRawRows command) at fees
  simp only [managedPlan, accepted]
  rw [fees]
  by_cases issue : M.isIssue command <;>
    simp [declaredCurrentAllocationsFor, allocatedFeeFor, managedRawRows, feeAllocationContribution, issue]

theorem managed_keys_ordered {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    PlanKeysUnique (managedPlan digest ctx pre command) ∧ PlanOrdered (managedPlan digest ctx pre command) := by
  have unique := sorted_wire_unique _ (managed_raw_unique command)
  have keys := effect_key_of_wire_unique _ unique
  have strict := sorted_rows_strict _ (managed_raw_unique command)
  cases occurrence : ctx.occurrence <;>
    simp only [managedPlan, accepted, PlanKeysUnique, PlanOrdered, M.occurrenceIds, occurrence] <;>
    simpa using And.intro keys strict

theorem managed_items {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    (managedPlan digest ctx pre command).rows.length = 2 ∧
      PlanWithinItemBounds (managedPlan digest ctx pre command) := by
  have count : (C.sortOn effectWire (managedRawRows command)).length = 2 := by
    rw [(C.sortOn_perm effectWire _).length_eq]
    rfl
  cases occurrence : ctx.occurrence <;>
    simp [managedPlan, accepted, PlanWithinItemBounds, count, M.occurrenceIds, occurrence]

theorem managed_plan_admitted {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (commandAdmitted : M.CommandWellFormed command)
    (ownerToken : B.ValidToken command.accountOwner)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    EffectPlanAdmitted (managedPlan digest ctx pre command) := by
  constructor
  · exact managed_rows_admitted structural commandAdmitted accepted
  constructor
  · intro row member
    simp only [managedPlan, accepted, List.mem_singleton] at member
    subst row
    exact managed_conservation_admitted structural commandAdmitted ownerToken accepted
  constructor
  · intro row member
    simp only [managedPlan, accepted, List.not_mem_nil] at member
  exact ⟨managed_projection accepted, managed_fee_projection accepted,
    (managed_items accepted).2, (managed_keys_ordered accepted).1⟩

theorem managed_asset_token {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) : B.ValidToken command.asset := by
  obtain ⟨policy, selected, _, _⟩ := FM.accepted_selected_leaf ⟨fun _ => ""⟩ structural accepted
  have registered := ManagedAssetFiniteOutcomeV2.structural_registered structural selected
  obtain ⟨row, member, same⟩ := List.mem_map.mp registered
  exact same ▸ structural.supplyTokens row member

theorem managed_plan_tokens {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre) (ownerToken : B.ValidToken command.accountOwner)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    PlanTokens (managedPlan digest ctx pre command) := by
  have assetToken := managed_asset_token structural accepted
  have domainToken : B.ValidToken S.accounts := by unfold B.ValidToken; decide
  constructor
  · intro row member
    simp only [managedPlan, accepted, C.mem_sortOn, managedRawRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨ownerToken, assetToken, domainToken⟩
  constructor
  · intro row member
    simp only [managedPlan, accepted, List.mem_singleton] at member
    subst row
    exact assetToken
  · intro row member
    simp only [managedPlan, accepted, List.not_mem_nil] at member

theorem managed_accepted_fields {digest : B.Bytes → M.Root} {ctx : M.Context} {pre : FM.State}
    {command : M.Command} (structural : FM.Structural pre)
    (accepted : (FM.transition digest ctx pre command).verdict = .accepted) :
    ∃ occurrence, ctx.occurrence = some occurrence ∧
      managedPlan digest ctx pre command =
        ⟨C.sortOn effectWire (managedRawRows command),
          [managedConservation pre (FM.transition digest ctx pre command).post command], [],
          [⟨.assetTransfer, FM.stateRoot digest pre, FM.stateRoot digest (FM.transition digest ctx pre command).post⟩],
          [occurrence.occurrenceId], []⟩ := by
  obtain ⟨policy, _, scalar, _⟩ := FM.accepted_selected_leaf ⟨fun _ => ""⟩ structural accepted
  obtain ⟨occurrence, present, _⟩ := M.accepted_consumes_exact_occurrence scalar
  exact ⟨occurrence, present, by simp only [managedPlan, accepted, M.occurrenceIds, present]⟩

end Proofs.AssetLaneFiniteEffectPlanV2
