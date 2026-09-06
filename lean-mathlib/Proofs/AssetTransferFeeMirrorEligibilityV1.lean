import Proofs.AssetTransferCustodyCompositionV1

/-!
# Accepted V1 transfer fee-mirror eligibility

This single-asset, accounts-domain projection uses the accepted leaf model's
actual movement and fee-allocation lists. `FeeMirrorEligible` checks signed row
sums and the allocation comparison in the existing Python
`_require_fee_mirror_v1`. It takes no caller-supplied eligibility premise.
The row fold and its alias/zero-elision proof come from the existing composition
model. An accepted leaf emits at most one movement per principal; it has no
other state-bearing effect kinds. Its positive fee produces one allocation and
one zero-residue conservation row, while a zero fee omits both fee rows.

`transferFeeAtoms` is the accepted policy fee, observed as `fee_charged_atoms`
in the Python leaf's conservation row. Sender-as-fee-owner netting leaves
`-amountAtoms` at the sender, so a positive fee retains the global refusal.
Recipient-as-fee-owner netting leaves `amountAtoms + transferFeeAtoms` there.

The universal claim concerns this mathematical projection under the existing
well-formed accepted-leaf premises. The companion test pins sources and compares
finite actual Python leaf effects with the unchanged global fee-mirror checker.
This does not prove universal Python/Rust/compiler refinement, arbitrary global
effect-plan validity, authenticated admission, custody successor selection,
receipt validity, publication, settlement authority or production qualification.
-/

namespace Proofs.AssetTransferFeeMirrorEligibilityV1

open Proofs.AssetTransferRefinementV1
open Proofs.AssetTransferCustodyCompositionV1 (movementDeltaSum)

/-- The signed aggregate and allocation clauses, projected to leaf account rows.
The asset and accounts-domain coordinates are fixed for this one-asset model. -/
def FeeMirrorEligible (effects : AbstractEffects) : Prop :=
  (∀ row ∈ effects.movements, IsI128 (movementDeltaSum row.principal effects.movements)) ∧
  (∀ row ∈ effects.feeAllocations,
    row.deltaAtoms ≤ movementDeltaSum row.principal effects.movements)

instance (effects : AbstractEffects) : Decidable (FeeMirrorEligible effects) :=
  inferInstanceAs (Decidable ((_ ∧ _)))

/-- Every keyed movement sum is derived from the accepted rows and fits i128. -/
theorem accepted_movement_sums_i128
    {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) (p : Principal) :
    IsI128 (movementDeltaSum p (transition ctx pre cmd).effects.movements) := by
  rw [Proofs.AssetTransferCustodyCompositionV1.accepted_movement_sum_matches_state_delta h p]
  rw [accepted_balance_eq h p, Int.add_comm (pre.balance p), Int.add_sub_cancel]
  exact accepted_deltas_i128 h p

/-- Sum the emitted rows at the fee owner, including both possible role aliases. -/
theorem accepted_fee_owner_movement_sum
    {ctx : Context} {pre : TransferState} {cmd : Command}
    (h : (transition ctx pre cmd).verdict = .accepted) :
    movementDeltaSum pre.policy.feeOwner (transition ctx pre cmd).effects.movements =
      if pre.policy.feeOwner = cmd.sender then -cmd.amountAtoms
      else if pre.policy.feeOwner = cmd.recipient then cmd.amountAtoms + pre.policy.transferFeeAtoms
      else pre.policy.transferFeeAtoms := by
  rw [Proofs.AssetTransferCustodyCompositionV1.accepted_movement_sum_matches_state_delta h]
  rw [accepted_balance_eq h]
  rw [Int.add_comm (pre.balance pre.policy.feeOwner), Int.add_sub_cancel]
  have hsr := (accepted_iff_all_guards ctx pre cmd).mp h .selfTransfer
  by_cases hos : pre.policy.feeOwner = cmd.sender
  · rw [if_pos hos, hos]
    exact (delta_fee_owner_is_sender hos hsr).1
  · rw [if_neg hos]
    by_cases hor : pre.policy.feeOwner = cmd.recipient
    · rw [if_pos hor, hor]
      exact (delta_fee_owner_is_recipient hor hsr).2
    · rw [if_neg hor]
      exact (delta_distinct_roles hsr hos hor).2.2

/-- Eligibility is exactly zero fee or a fee owner distinct from the sender.
No row existence, row sum, or eligibility flag is an assumption. -/
theorem accepted_fee_mirror_eligible_iff
    {ctx : Context} {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed cmd)
    (h : (transition ctx pre cmd).verdict = .accepted) :
    FeeMirrorEligible (transition ctx pre cmd).effects ↔
      pre.policy.transferFeeAtoms = 0 ∨ pre.policy.feeOwner ≠ cmd.sender := by
  have widths : ∀ row ∈ (transition ctx pre cmd).effects.movements,
      IsI128 (movementDeltaSum row.principal (transition ctx pre cmd).effects.movements) := by
    intro row _
    exact accepted_movement_sums_i128 h row.principal
  have fees : (transition ctx pre cmd).effects.feeAllocations =
      if pre.policy.transferFeeAtoms = 0 then []
      else [⟨pre.policy.feeOwner, pre.policy.transferFeeAtoms⟩] := by
    rw [(accepted_post_eq h).2]
    rfl
  unfold FeeMirrorEligible
  rw [and_iff_right widths, fees]
  by_cases hfee : pre.policy.transferFeeAtoms = 0
  · rw [if_pos hfee]
    constructor
    · intro _
      exact Or.inl hfee
    · intro _ row member
      exact False.elim (List.not_mem_nil member)
  · rw [if_neg hfee]
    simp only [List.mem_singleton, forall_eq, hfee, false_or]
    rw [accepted_fee_owner_movement_sum h]
    have hf := hpre.fee.1
    have ha := hcmd.amount.1
    have hnonzero : cmd.amountAtoms ≠ 0 :=
      (accepted_iff_all_guards ctx pre cmd).mp h .zeroAmount
    by_cases hos : pre.policy.feeOwner = cmd.sender
    · rw [if_pos hos]
      constructor
      · intro impossible
        omega
      · intro distinct
        exact False.elim (distinct hos)
    · rw [if_neg hos]
      constructor
      · intro _
        exact hos
      · intro _
        split <;> omega

/-- A positive fee allocated to the accepted sender fails the mirror relation. -/
theorem positive_sender_fee_not_eligible
    {ctx : Context} {pre : TransferState} {cmd : Command}
    (hpre : StateWellFormed pre) (hcmd : CommandWellFormed cmd)
    (h : (transition ctx pre cmd).verdict = .accepted)
    (hfee : 0 < pre.policy.transferFeeAtoms) (hos : pre.policy.feeOwner = cmd.sender) :
    ¬ FeeMirrorEligible (transition ctx pre cmd).effects := by
  rw [accepted_fee_mirror_eligible_iff hpre hcmd h]
  intro eligible
  rcases eligible with zero | distinct
  · omega
  · exact distinct hos

end Proofs.AssetTransferFeeMirrorEligibilityV1
