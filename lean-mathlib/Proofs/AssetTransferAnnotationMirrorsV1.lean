import Proofs.AssetTransferEffectPlanV1
import Proofs.AssetTransferFeeMirrorEligibilityV1

/-!
# Annotation mirrors for the completed ASSET_TRANSFER V1 plan

This file proves the full five-clause `GlobalEconomicStateRefinementV2.AnnotationMirrors`
relation for the plan returned by the completed pre-state-policy transfer
`AssetTransferEffectPlanV1.complete`.  For an admitted pre-state, a width-admitted command and
an accepted front-door verdict, the relation holds exactly when the actual first-match
selected policy charges a zero fee or credits a fee owner distinct from the sender.  A rejected
completion returns the exact empty plan, which satisfies the relation.  A positive fee credited
to the sender is accepted by the leaf yet fails the relation, retaining the existing
local/global restriction.

## Clauses

* Ordered state-bearing prefix widths: every running subtotal of account-movement, custody
  and reserve rows at one full physical key `(owner, asset, accountingDomain)` fits i128.  The
  bridge is `running_totals_fit_of_pairwise_zero`: each contribution fits i128 and at most one
  row contributes nonzero at the key, so the running total is either zero or that single
  contribution.  The at-most-one shape comes from actual role aggregation (one movement row per
  principal), zero-row elision, unique full effect keys after canonical sorting
  (`AssetTransferEffectPlanV1.projectedPlan_keys_unique`) and the two emitted kinds
  (`AssetTransferSparseTablesV1.projectedPlan_row_kinds`).  No permutation argument about
  intermediate overflow is used.
* Fee credits mirrored: the single fee-allocation row is positive and covered by the
  state-bearing aggregate at the fee owner's key, which is the leaf movement fold at that
  principal (`AssetTransferFeeMirrorEligibilityV1.accepted_fee_owner_movement_sum`).  This
  clause is exactly the eligibility condition.
* Reward/slash mirrored: no such rows are emitted.
* Fee rows canonical: a zero fee emits no fee conservation row; a nonzero u128 fee is positive.
* Fee residue exact: no designated reserve residue row and zero carried residue.

## Claim boundary

Opaque commitment strings stay unauthenticated.  This file proves no Python/Rust/compiler
refinement, no global `Verified` construction, no custody conservation closure, no
signature/profile/store authority, no receipt validity and no publisher qualification.
-/

set_option warningAsError true

namespace Proofs
namespace AssetTransferAnnotationMirrorsV1

open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

namespace E
export Proofs.AssetTransferEffectPlanV1
  (CommitmentFields selectedPlan feeRows complete selectedPlan_rows selectedPlan_fee_conservation
   complete_rejected_empty complete_accepted_plan complete_effect_plan_admitted
   projectedPlan_keys_unique)
end E

namespace K
export Proofs.AssetTransferPolicySelectionV1
  (Input StateAdmitted policyFor selectedInput step accepted_selected_step
   selectedInput_state_well_formed)
end K

namespace S
export Proofs.AssetTransferSparseTablesV1
  (Input step projectedPlan movementEffects effectWire accounts localState accepted_step_shape
   projectedPlan_effect projectedPlan_frame_effects projectedPlan_row_kinds sum_map_zero)
end S

namespace T
export Proofs.AssetTransferRefinementV1
  (Policy Command RejectCode StateWellFormed CommandWellFormed IsU128 transition
   accepted_iff_all_guards accepted_post_eq acceptedEffects)
end T

namespace F
export Proofs.AssetTransferFeeMirrorEligibilityV1 (accepted_fee_owner_movement_sum)
end F

namespace M
export Proofs.AssetTransferCustodyCompositionV1 (movementDeltaSum)
end M

namespace C
export Proofs.CanonicalEpochEconomicRowsV1 (sortOn mem_sortOn)
end C

attribute [local instance] lexOrd

/-- Once every remaining contribution is zero, the running total is frozen at an admitted value. -/
private theorem running_totals_of_zero_tail {α : Type} (contribution : α → Int) :
    ∀ (rows : List α) (total : Int), FitsI128 total →
      (∀ row ∈ rows, contribution row = 0) → RunningTotalsFitI128 contribution rows total
  | [], _, _, _ => trivial
  | row :: rows, total, fits, zero => by
      have head : contribution row = 0 := zero row (by simp)
      simp only [RunningTotalsFitI128, head, Int.add_zero]
      exact ⟨fits, running_totals_of_zero_tail contribution rows total fits
        (fun r m => zero r (by simp [m]))⟩

/-- At most one nonzero contribution, each inside i128, keeps every ordered running subtotal
inside i128 from a zero start.  This is the prefix-width bridge: no arbitrary permutation
assumption is used, only the pairwise at-most-one-nonzero shape. -/
theorem running_totals_fit_of_pairwise_zero {α : Type} (contribution : α → Int) :
    ∀ rows : List α, (∀ row ∈ rows, FitsI128 (contribution row)) →
      rows.Pairwise (fun left right => contribution left = 0 ∨ contribution right = 0) →
      RunningTotalsFitI128 contribution rows 0
  | [], _, _ => trivial
  | row :: rows, widths, pairwise => by
      have parts := List.pairwise_cons.mp pairwise
      have headWidth := widths row (by simp)
      have tailWidths : ∀ r ∈ rows, FitsI128 (contribution r) := fun r m => widths r (by simp [m])
      simp only [RunningTotalsFitI128, Int.zero_add]
      refine ⟨headWidth, ?_⟩
      by_cases zero : contribution row = 0
      · rw [zero]
        exact running_totals_fit_of_pairwise_zero contribution rows tailWidths parts.2
      · apply running_totals_of_zero_tail contribution rows _ headWidth
        intro r m
        rcases parts.1 r m with h | h
        · exact absurd h zero
        · exact h

/-- A nonzero state-bearing contribution pins the row to the queried full physical key and to
one of the three state-bearing kinds. -/
private theorem contribution_nonzero {owner asset domain : String} {row : EconomicEffectRow}
    (nonzero : stateBearingContribution owner asset domain row ≠ 0) :
    row.principal = owner ∧ row.asset = asset ∧ row.custodyDomain = domain ∧
      (row.kind = .accountMovement ∨ row.kind = .custody ∨ row.kind = .reserve) := by
  unfold stateBearingContribution at nonzero
  split at nonzero
  · assumption
  · exact absurd rfl nonzero

private theorem contribution_width {owner asset domain : String} {row : EconomicEffectRow}
    (width : FitsI128 row.deltaAtoms) :
    FitsI128 (stateBearingContribution owner asset domain row) := by
  unfold stateBearingContribution
  split
  · exact width
  · exact zero_fits_i128

/-- Accepted sparse rows carry at most one nonzero state-bearing contribution per full
physical key: the emitted kinds are account movement or fee allocation, fee rows contribute
nothing, and full effect keys are unique after canonical sorting. -/
theorem projectedPlan_state_bearing_pairwise_zero {input : S.Input}
    (accepted : (S.step input).verdict = .accepted) (owner asset domain : String) :
    (S.projectedPlan input).rows.Pairwise (fun left right =>
      stateBearingContribution owner asset domain left = 0 ∨
        stateBearingContribution owner asset domain right = 0) := by
  have keys := List.pairwise_map.mp (E.projectedPlan_keys_unique accepted)
  apply List.Pairwise.imp_of_mem (p := keys)
  intro left right leftMember rightMember different
  by_cases leftZero : stateBearingContribution owner asset domain left = 0
  · exact Or.inl leftZero
  by_cases rightZero : stateBearingContribution owner asset domain right = 0
  · exact Or.inr rightZero
  exfalso
  obtain ⟨lp, la, ld, lk⟩ := contribution_nonzero leftZero
  obtain ⟨rp, ra, rd, rk⟩ := contribution_nonzero rightZero
  have leftKind : left.kind = .accountMovement := by
    rcases S.projectedPlan_row_kinds input left leftMember with h | h
    · exact h
    · rw [h] at lk
      rcases lk with h' | h' | h' <;> cases h'
  have rightKind : right.kind = .accountMovement := by
    rcases S.projectedPlan_row_kinds input right rightMember with h | h
    · exact h
    · rw [h] at rk
      rcases rk with h' | h' | h' <;> cases h'
  apply different
  simp only [EconomicEffectRow.key, leftKind, rightKind, lp, la, ld, rp, ra, rd]

/-! ## Membership shape of the completed rows -/

private theorem effectFor_selectedPlan (fields : E.CommitmentFields) (input : S.Input)
    (kind : EffectKind) (owner asset domain : String) :
    effectFor kind (E.selectedPlan fields input) owner asset domain =
      effectFor kind (S.projectedPlan input) owner asset domain := rfl

private theorem mem_selectedPlan_rows (fields : E.CommitmentFields) (input : S.Input)
    (row : EconomicEffectRow) :
    row ∈ (E.selectedPlan fields input).rows ↔
      row ∈ S.movementEffects .accountMovement input.command.asset
          (T.acceptedEffects (S.localState input) input.command).movements ∨
        row ∈ S.movementEffects .feeAllocation input.command.asset
          (T.acceptedEffects (S.localState input) input.command).feeAllocations := by
  rw [E.selectedPlan_rows]
  change row ∈ C.sortOn S.effectWire
    (S.movementEffects .accountMovement input.command.asset
        (T.acceptedEffects (S.localState input) input.command).movements ++
      S.movementEffects .feeAllocation input.command.asset
        (T.acceptedEffects (S.localState input) input.command).feeAllocations) ↔ _
  rw [C.mem_sortOn, List.mem_append]

private theorem movement_row_kind (input : S.Input) (row : EconomicEffectRow)
    (member : row ∈ S.movementEffects .accountMovement input.command.asset
      (T.acceptedEffects (S.localState input) input.command).movements) :
    row.kind = .accountMovement := by
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp (by simpa only [S.movementEffects] using member)
  rfl

/-- The fee-allocation rows are exactly the single positive-fee credit at the fee owner. -/
private theorem mem_fee_rows (input : S.Input) (row : EconomicEffectRow) :
    row ∈ S.movementEffects .feeAllocation input.command.asset
        (T.acceptedEffects (S.localState input) input.command).feeAllocations ↔
      input.policy.transferFeeAtoms ≠ 0 ∧
        row = ⟨.feeAllocation, input.policy.feeOwner, input.command.asset, S.accounts,
          input.policy.transferFeeAtoms⟩ := by
  change row ∈ S.movementEffects .feeAllocation input.command.asset
    (if input.policy.transferFeeAtoms = 0 then []
      else [⟨input.policy.feeOwner, input.policy.transferFeeAtoms⟩]) ↔ _
  by_cases zeroFee : input.policy.transferFeeAtoms = 0
  · simp [zeroFee, S.movementEffects]
  · simp [zeroFee, S.movementEffects]

/-- The state-bearing aggregate at the fee owner's full physical key is the actual leaf
movement fold: custody and reserve effects are absent from a transfer. -/
private theorem selectedPlan_owner_effect (fields : E.CommitmentFields) (input : S.Input) :
    stateBearingEffectFor (E.selectedPlan fields input) input.policy.feeOwner
        input.command.asset S.accounts =
      M.movementDeltaSum input.policy.feeOwner
        (T.acceptedEffects (S.localState input) input.command).movements := by
  have account := S.projectedPlan_effect input .accountMovement input.policy.feeOwner
    input.command.asset S.accounts
  have frame := S.projectedPlan_frame_effects input input.policy.feeOwner
    input.command.asset S.accounts
  unfold stateBearingEffectFor
  rw [effectFor_selectedPlan, effectFor_selectedPlan, effectFor_selectedPlan, account, frame.1,
    frame.2.2]
  simp

/-- The leaf's actual fee-owner movement fold under the accepted alias cases. -/
private theorem accepted_owner_sum {input : S.Input}
    (leafAccepted :
      (T.transition input.context (S.localState input) input.command).verdict = .accepted) :
    M.movementDeltaSum input.policy.feeOwner
        (T.acceptedEffects (S.localState input) input.command).movements =
      if input.policy.feeOwner = input.command.sender then -input.command.amountAtoms
      else if input.policy.feeOwner = input.command.recipient then
        input.command.amountAtoms + input.policy.transferFeeAtoms
      else input.policy.transferFeeAtoms := by
  have h := F.accepted_fee_owner_movement_sum leafAccepted
  rw [(T.accepted_post_eq leafAccepted).2] at h
  exact h

/-! ## The four clauses that hold for every accepted completion -/

private theorem selectedPlan_unconditional_clauses (fields : E.CommitmentFields) {input : S.Input}
    (stateWellFormed : T.StateWellFormed (S.localState input))
    (accepted : (S.step input).verdict = .accepted)
    (planAdmitted : EffectPlanAdmitted (E.selectedPlan fields input)) :
    StateBearingAggregatesFitI128 (E.selectedPlan fields input) ∧
      RewardSlashMirrored (E.selectedPlan fields input) ∧
      FeeRowsCanonical (E.selectedPlan fields input) ∧
      FeeResidueExact (E.selectedPlan fields input) := by
  have feeBound : T.IsU128 input.policy.transferFeeAtoms := stateWellFormed.fee
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro owner asset domain
    rw [E.selectedPlan_rows]
    apply running_totals_fit_of_pairwise_zero
    · intro row member
      exact contribution_width (planAdmitted.1 row member).1
    · exact projectedPlan_state_bearing_pairwise_zero accepted owner asset domain
  · intro row member kind
    rcases S.projectedPlan_row_kinds input row member with h | h <;>
      rcases kind with k | k <;> rw [h] at k <;> cases k
  · intro row member
    rw [E.selectedPlan_fee_conservation] at member
    simp only [E.feeRows] at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst member
      show 0 < input.policy.transferFeeAtoms
      have := feeBound.1
      rename_i nonzero
      omega
  · intro asset
    have designatedZero : positiveDesignatedResidueFor (E.selectedPlan fields input) asset = 0 := by
      apply S.sum_map_zero
      intro row member
      rcases S.projectedPlan_row_kinds input row member with h | h <;> simp [h]
    have carriedZero : positiveCarriedResidueFor (E.selectedPlan fields input) asset = 0 := by
      apply S.sum_map_zero
      intro row member
      rw [E.selectedPlan_fee_conservation] at member
      simp only [E.feeRows] at member
      split at member
      · simp at member
      · rw [List.mem_singleton] at member
        subst member
        simp
    rw [designatedZero, carriedZero]

/-! ## The fee-credit clause is exactly the leaf eligibility condition -/

private theorem selectedPlan_fee_credits_mirrored_iff (fields : E.CommitmentFields)
    {input : S.Input} (stateWellFormed : T.StateWellFormed (S.localState input))
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (S.step input).verdict = .accepted) :
    FeeAllocationCreditsMirrored (E.selectedPlan fields input) ↔
      input.policy.transferFeeAtoms = 0 ∨ input.policy.feeOwner ≠ input.command.sender := by
  have leafAccepted :
      (T.transition input.context (S.localState input) input.command).verdict = .accepted :=
    (S.accepted_step_shape accepted).1
  have guards :=
    (T.accepted_iff_all_guards input.context (S.localState input) input.command).mp leafAccepted
  have amountNonzero : input.command.amountAtoms ≠ 0 := guards .zeroAmount
  have amountLower : 0 ≤ input.command.amountAtoms := commandWellFormed.amount.1
  have feeLower : 0 ≤ input.policy.transferFeeAtoms := stateWellFormed.fee.1
  have ownerSum := accepted_owner_sum leafAccepted
  have ownerEffect := selectedPlan_owner_effect fields input
  constructor
  · intro mirrored
    by_cases zeroFee : input.policy.transferFeeAtoms = 0
    · exact Or.inl zeroFee
    · right
      intro sameOwner
      have feeRowMember : (⟨.feeAllocation, input.policy.feeOwner, input.command.asset, S.accounts,
          input.policy.transferFeeAtoms⟩ : EconomicEffectRow) ∈ (E.selectedPlan fields input).rows :=
        (mem_selectedPlan_rows fields input _).mpr (Or.inr ((mem_fee_rows input _).mpr ⟨zeroFee, rfl⟩))
      have credit : 0 < input.policy.transferFeeAtoms ∧
          input.policy.transferFeeAtoms ≤ stateBearingEffectFor (E.selectedPlan fields input)
            input.policy.feeOwner input.command.asset S.accounts :=
        mirrored _ feeRowMember rfl
      rw [ownerEffect, ownerSum, if_pos sameOwner] at credit
      omega
  · intro eligible row member kind
    rcases (mem_selectedPlan_rows fields input row).mp member with movement | fee
    · have h := movement_row_kind input row movement
      rw [kind] at h
      cases h
    · obtain ⟨nonzero, rfl⟩ := (mem_fee_rows input row).mp fee
      show 0 < input.policy.transferFeeAtoms ∧
        input.policy.transferFeeAtoms ≤ stateBearingEffectFor (E.selectedPlan fields input)
          input.policy.feeOwner input.command.asset S.accounts
      rw [ownerEffect, ownerSum]
      rcases eligible with zero | distinctOwner
      · exact absurd zero nonzero
      · rw [if_neg distinctOwner]
        refine ⟨by omega, ?_⟩
        split <;> omega

private theorem selectedPlan_annotation_mirrors_iff (fields : E.CommitmentFields) {input : S.Input}
    (stateWellFormed : T.StateWellFormed (S.localState input))
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (S.step input).verdict = .accepted)
    (planAdmitted : EffectPlanAdmitted (E.selectedPlan fields input)) :
    AnnotationMirrors (E.selectedPlan fields input) ↔
      input.policy.transferFeeAtoms = 0 ∨ input.policy.feeOwner ≠ input.command.sender := by
  obtain ⟨widths, rewardSlash, feeRows, residue⟩ :=
    selectedPlan_unconditional_clauses fields stateWellFormed accepted planAdmitted
  rw [← selectedPlan_fee_credits_mirrored_iff fields stateWellFormed commandWellFormed accepted]
  constructor
  · intro mirrors
    exact mirrors.2.1
  · intro credits
    exact ⟨widths, credits, rewardSlash, feeRows, residue⟩

/-! ## Public front-door contracts -/

/-- The exact empty plan of every rejection satisfies all five clauses. -/
theorem empty_annotation_mirrors : AnnotationMirrors EffectPlan.empty := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro owner asset domain
    trivial
  · intro row member
    simp [EffectPlan.empty] at member
  · intro row member
    simp [EffectPlan.empty] at member
  · intro row member
    simp [EffectPlan.empty] at member
  · intro asset
    rfl

/-- A rejected completion returns the exact empty plan, which satisfies the relation. -/
theorem complete_rejected_annotation_mirrors {fields : E.CommitmentFields} {input : K.Input}
    {code : T.RejectCode} (rejected : (K.step input).verdict = .rejected code) :
    (E.complete fields input).plan = EffectPlan.empty ∧
      AnnotationMirrors (E.complete fields input).plan := by
  have empty := (E.complete_rejected_empty (fields := fields) rejected).2
  rw [empty]
  exact ⟨rfl, empty_annotation_mirrors⟩

/-- Selected-policy reduction of the completed plan.  The caller still names the selected
row; the front door below removes that premise. -/
theorem complete_selected_annotation_mirrors_iff {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (admitted : K.StateAdmitted input.pre)
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy) :
    AnnotationMirrors (E.complete fields input).plan ↔
      policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender := by
  obtain ⟨selected, selectedSelection, selectedAccepted, _, _, _⟩ :=
    K.accepted_selected_step accepted
  have same : selected = policy := Option.some.inj (selectedSelection.symm.trans selection)
  subst same
  have planAdmitted : EffectPlanAdmitted (E.selectedPlan fields (K.selectedInput input selected)) := by
    have admittedPlan := E.complete_effect_plan_admitted fields input admitted
    rwa [E.complete_accepted_plan accepted selection] at admittedPlan
  rw [E.complete_accepted_plan accepted selection]
  exact selectedPlan_annotation_mirrors_iff fields
    (K.selectedInput_state_well_formed admitted selection) commandWellFormed selectedAccepted
    planAdmitted

/-- Every accepted completion satisfies the four clauses that do not depend on the fee alias:
ordered state-bearing prefix widths, absent reward/slash rows, positive charged fee rows, and
zero designated and carried residue. -/
theorem complete_accepted_unconditional_clauses (fields : E.CommitmentFields) {input : K.Input}
    (admitted : K.StateAdmitted input.pre) (accepted : (K.step input).verdict = .accepted) :
    StateBearingAggregatesFitI128 (E.complete fields input).plan ∧
      RewardSlashMirrored (E.complete fields input).plan ∧
      FeeRowsCanonical (E.complete fields input).plan ∧
      FeeResidueExact (E.complete fields input).plan := by
  obtain ⟨policy, selection, selectedAccepted, _, _, _⟩ := K.accepted_selected_step accepted
  have planAdmitted : EffectPlanAdmitted (E.selectedPlan fields (K.selectedInput input policy)) := by
    have admittedPlan := E.complete_effect_plan_admitted fields input admitted
    rwa [E.complete_accepted_plan accepted selection] at admittedPlan
  rw [E.complete_accepted_plan accepted selection]
  exact selectedPlan_unconditional_clauses fields
    (K.selectedInput_state_well_formed admitted selection) selectedAccepted planAdmitted

/-- Front door.  For an admitted pre-state, a width-admitted command and an accepted
front-door verdict, the completed plan satisfies the full five-clause relation exactly when
the actual first-match selected policy charges no fee or credits an owner distinct from the
sender.  No policy, row shape, sortedness, or aggregate width is assumed. -/
theorem complete_annotation_mirrors_iff (fields : E.CommitmentFields) {input : K.Input}
    (admitted : K.StateAdmitted input.pre) (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted) :
    AnnotationMirrors (E.complete fields input).plan ↔
      ∃ policy, K.policyFor input.pre.policies input.command.asset = some policy ∧
        (policy.transferFeeAtoms = 0 ∨ policy.feeOwner ≠ input.command.sender) := by
  obtain ⟨policy, selection, _, _, _, _⟩ := K.accepted_selected_step accepted
  rw [complete_selected_annotation_mirrors_iff admitted commandWellFormed accepted selection]
  constructor
  · intro eligible
    exact ⟨policy, selection, eligible⟩
  · rintro ⟨candidate, candidateSelection, eligible⟩
    have same : candidate = policy := Option.some.inj (candidateSelection.symm.trans selection)
    rw [← same]
    exact eligible

/-- The retained local/global restriction: a positive fee credited to the sender is accepted by
the leaf yet its completed plan fails the global relation. -/
theorem complete_positive_sender_fee_not_mirrored {fields : E.CommitmentFields} {input : K.Input}
    {policy : T.Policy} (admitted : K.StateAdmitted input.pre)
    (commandWellFormed : T.CommandWellFormed input.command)
    (accepted : (K.step input).verdict = .accepted)
    (selection : K.policyFor input.pre.policies input.command.asset = some policy)
    (positiveFee : 0 < policy.transferFeeAtoms)
    (senderOwner : policy.feeOwner = input.command.sender) :
    ¬ AnnotationMirrors (E.complete fields input).plan := by
  rw [complete_selected_annotation_mirrors_iff admitted commandWellFormed accepted selection]
  rintro (zero | distinct)
  · omega
  · exact distinct senderOwner

end AssetTransferAnnotationMirrorsV1
end Proofs
