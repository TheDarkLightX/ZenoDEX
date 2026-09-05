import Proofs.AssetTransferRefinementV1
import Proofs.AssetTransferCustodyCompletionV1
import Proofs.CheckedSignedDeltaRefinementV1

/-!
# Custody-complete ASSET transfer composition

This file composes the bounded transfer model with the checked signed-delta
model.  For an accepted transfer, every account's unsigned pre/post holdings
produce the exact aggregated movement delta emitted by the abstract effect
plan.  The custody frame is represented by using one holding on both sides;
its signed delta is therefore zero by the existing signed-delta theorem.

The account enumeration is an explicit finite model premise.  This file does
not prove canonical row decoding or serialization, source-level Python/Rust
refinement, state roots, journals, signatures, authentication, receipts,
release/profile/image selection, publication, settlement authority, or actual
custody, possession, title, or claimant control.  The theorem is research
evidence for the mathematical composition only; it is not a deployed proof.
-/

namespace Proofs.AssetTransferCustodyCompositionV1

namespace T
export Proofs.AssetTransferRefinementV1 (Context Command IsI128 IsU128 Principal StateWellFormed TransferState
  AbstractEffects MovementRow delta movementRows roleOrder transition accepted_balance_eq accepted_conserves_total
  accepted_deltas_i128 accepted_balances_u128 accepted_post_eq accepted_supply_unchanged acceptedEffects
  movementRows_mem delta_untouched occ sumOver sumOver_nonneg)
end T

namespace D
export Proofs.CheckedSignedDeltaRefinementV1 (Holding checkedSignedDelta exactDifference representable
  success_iff_exact_representable unchanged_holdings_accept_zero minMagnitude signedMax)
end D

namespace C
export Proofs.AssetTransferCustodyCompletionV1 (complete completeChecked completed_totals_preserve_supply
  checked_completion_accepts_valid_projection maxAtoms)
end C

/-! A validated signed-holding view of an `Int` account amount. -/
def holdingOf (atoms : Int) (h : T.IsU128 atoms) : D.Holding :=
  ⟨atoms.toNat, by
    have hupper : (atoms.toNat : Int) ≤ Proofs.AssetTransferRefinementV1.u128Max := by
      rw [Int.toNat_of_nonneg h.1]
      exact h.2
    rw [Proofs.AssetTransferRefinementV1.u128Max_eq_pow] at hupper
    omega
  ⟩

theorem exactDifference_holdingOf {post pre : Int}
    (hpost : T.IsU128 post) (hpre : T.IsU128 pre) :
    D.exactDifference (holdingOf post hpost) (holdingOf pre hpre) = post - pre := by
  simp [D.exactDifference, holdingOf, Int.toNat_of_nonneg hpost.1,
    Int.toNat_of_nonneg hpre.1]

theorem isI128_iff_representable {d : Int} :
    T.IsI128 d ↔ D.representable d := by
  simp [Proofs.AssetTransferRefinementV1.IsI128,
    Proofs.AssetTransferRefinementV1.i128Min,
    Proofs.AssetTransferRefinementV1.i128Max,
    D.representable, D.minMagnitude, D.signedMax]

/-!
For every principal, the checked post-minus-pre account holding delta equals
the transfer core's aggregated delta.  `accepted_deltas_i128` supplies the
representability needed by the signed-delta checker; this is stronger than
merely assuming that the checker returned a value.
-/
theorem accepted_account_signed_delta
    {ctx : T.Context} {pre : T.TransferState} {cmd : T.Command}
    (hpre : T.StateWellFormed pre)
    (h : (T.transition ctx pre cmd).verdict = .accepted) (p : T.Principal) :
    D.checkedSignedDelta
      (holdingOf ((T.transition ctx pre cmd).post.balance p)
        (T.accepted_balances_u128 hpre h p))
      (holdingOf (pre.balance p) (hpre.balances p)) =
      .ok (T.delta pre cmd p) := by
  rw [D.success_iff_exact_representable]
  constructor
  · rw [exactDifference_holdingOf]
    have hbalance := T.accepted_balance_eq h p
    omega
  · exact (isI128_iff_representable.mp (T.accepted_deltas_i128 h p))

/-! Every movement row actually emitted by the accepted abstract effect plan
carries the same delta proved above.  Zero-delta principals are omitted by
`movementRows`; their account theorem still proves a checked zero delta. -/
theorem accepted_movement_row_signed_delta
    {ctx : T.Context} {pre : T.TransferState} {cmd : T.Command}
    (hpre : T.StateWellFormed pre)
    (h : (T.transition ctx pre cmd).verdict = .accepted)
    {row : T.MovementRow}
    (hrow : row ∈ (T.transition ctx pre cmd).effects.movements) :
    D.checkedSignedDelta
      (holdingOf ((T.transition ctx pre cmd).post.balance row.principal)
        (T.accepted_balances_u128 hpre h row.principal))
      (holdingOf (pre.balance row.principal) (hpre.balances row.principal)) =
      .ok row.deltaAtoms := by
  have hmem := T.movementRows_mem (d := T.delta pre cmd)
    ((T.accepted_post_eq h).2 ▸ hrow)
  rw [hmem.1]
  exact accepted_account_signed_delta hpre h row.principal

/-! The custody side of the wrapper is a frame by construction. -/
theorem unchanged_custody_signed_delta (holding : D.Holding) :
    D.checkedSignedDelta holding holding = .ok 0 :=
  D.unchanged_holdings_accept_zero holding

def movementDeltaSum (p : T.Principal) : List T.MovementRow → Int
  | [] => 0
  | row :: rows =>
      (if row.principal = p then row.deltaAtoms else 0) + movementDeltaSum p rows

/-! Folding all rows by principal accounts for omitted zero rows. -/
theorem movementRows_sum_eq_delta_mul_occ {d : T.Principal → Int} (p : T.Principal) :
    ∀ ps : List T.Principal,
      movementDeltaSum p (T.movementRows d ps) = d p * T.occ p ps
  | [] => by simp [T.movementRows, movementDeltaSum, T.occ]
  | q :: qs => by
      by_cases hzero : d q = 0
      · simp only [T.movementRows, if_pos hzero]
        rw [movementRows_sum_eq_delta_mul_occ p qs]
        by_cases hqp : q = p
        · subst q
          simp [T.occ, hzero]
        · simp [T.occ, hqp]
      · simp only [T.movementRows, hzero, ↓reduceIte, movementDeltaSum]
        rw [movementRows_sum_eq_delta_mul_occ p qs]
        by_cases hqp : q = p
        · subst q
          simp [T.occ, Int.mul_add]
        · simp only [T.occ, if_neg hqp]
          simp

/-! The role-order list includes each potentially changed principal once,
including sender/recipient/fee-owner aliases. Zero deltas need no contribution. -/
theorem delta_mul_occ_roleOrder {pre : T.TransferState} {cmd : T.Command}
    (hsr : cmd.sender ≠ cmd.recipient) (p : T.Principal) :
    T.delta pre cmd p * T.occ p (T.roleOrder pre cmd) = T.delta pre cmd p := by
  unfold T.roleOrder
  by_cases hos : pre.policy.feeOwner = cmd.sender
  · rw [if_pos (Or.inl hos)]
    by_cases hs : p = cmd.sender
    · subst p
      simp [T.occ, Ne.symm hsr]
    · by_cases hr : p = cmd.recipient
      · subst p
        simp [T.occ, hsr]
      · have hfee : p ≠ pre.policy.feeOwner := by
          intro hpf
          apply hs
          exact hpf.trans hos
        have hz := T.delta_untouched hs hr hfee
        simp [T.occ, Ne.symm hs, Ne.symm hr, hz]
  · by_cases hor : pre.policy.feeOwner = cmd.recipient
    · rw [if_pos (Or.inr hor)]
      by_cases hs : p = cmd.sender
      · subst p
        simp [T.occ, Ne.symm hsr]
      · by_cases hr : p = cmd.recipient
        · subst p
          simp [T.occ, hsr]
        · have hfee : p ≠ pre.policy.feeOwner := by
            intro hpf
            apply hr
            exact hpf.trans hor
          have hz := T.delta_untouched hs hr hfee
          simp [T.occ, Ne.symm hs, Ne.symm hr, hz]
    · rw [if_neg (by
        intro h
        rcases h with h | h
        · exact hos h
        · exact hor h)]
      by_cases hs : p = cmd.sender
      · subst p
        simp [T.occ, Ne.symm hsr, hos]
      · by_cases hr : p = cmd.recipient
        · subst p
          simp [T.occ, hsr, hor]
        · by_cases hf : p = pre.policy.feeOwner
          · subst p
            simp [T.occ, Ne.symm hos, Ne.symm hor]
          · have hz := T.delta_untouched hs hr hf
            simp [T.occ, Ne.symm hs, Ne.symm hr, Ne.symm hf, hz]

/-! The folded emitted movement map equals the actual accepted state delta at
every principal. -/
theorem accepted_movement_sum_matches_state_delta
    {ctx : T.Context} {pre : T.TransferState} {cmd : T.Command}
    (h : (T.transition ctx pre cmd).verdict = .accepted) (p : T.Principal) :
    movementDeltaSum p (T.transition ctx pre cmd).effects.movements =
      (T.transition ctx pre cmd).post.balance p - pre.balance p := by
  rw [(T.accepted_post_eq h).2]
  change movementDeltaSum p (T.movementRows (T.delta pre cmd) (T.roleOrder pre cmd)) = _
  rw [movementRows_sum_eq_delta_mul_occ]
  have hguards := (Proofs.AssetTransferRefinementV1.accepted_iff_all_guards ctx pre cmd).mp h
  rw [delta_mul_occ_roleOrder (hguards .selfTransfer) p]
  have hbalance := T.accepted_balance_eq h p
  omega

/-!
An optional scalar lift for the same finite account enumeration: accepted
account conservation plus one common custody total gives the completed supply
pair.  `StateWellFormed` makes the finite account sum nonnegative before its
natural representation is used. `preProjection` binds the exact signed
account-plus-custody total to the transfer state's own supply; the theorem
does not claim this representation boundary for runtime rows.
-/
theorem accepted_complete_supply_with_common_custody
    {ctx : T.Context} {pre : T.TransferState} {cmd : T.Command}
    (hpre : T.StateWellFormed pre)
    (h : (T.transition ctx pre cmd).verdict = .accepted)
    (ps : List T.Principal)
    (hs : T.occ cmd.sender ps = 1)
    (hr : T.occ cmd.recipient ps = 1)
    (ho : T.occ pre.policy.feeOwner ps = 1)
    {custody : Nat}
    (preProjection : T.sumOver pre.balance ps + (custody : Int) = pre.supplyAtoms) :
    C.complete (T.sumOver pre.balance ps).toNat
      (T.sumOver (T.transition ctx pre cmd).post.balance ps).toNat custody custody =
        (pre.supplyAtoms.toNat, pre.supplyAtoms.toNat) ∧
    C.completeChecked (T.sumOver pre.balance ps).toNat
      (T.sumOver (T.transition ctx pre cmd).post.balance ps).toNat custody custody =
        .some (pre.supplyAtoms.toNat, pre.supplyAtoms.toNat) ∧
    0 ≤ T.sumOver pre.balance ps ∧
    0 ≤ T.sumOver (T.transition ctx pre cmd).post.balance ps ∧
    T.sumOver pre.balance ps + (custody : Int) = pre.supplyAtoms ∧
    T.sumOver (T.transition ctx pre cmd).post.balance ps + (custody : Int) =
      (T.transition ctx pre cmd).post.supplyAtoms := by
  have hpreNonneg : 0 ≤ T.sumOver pre.balance ps :=
    T.sumOver_nonneg (fun p => (hpre.balances p).1) ps
  have hpreNat : (T.sumOver pre.balance ps).toNat + custody = pre.supplyAtoms.toNat := by
    rw [← Int.toNat_of_nonneg hpreNonneg]
    omega
  have hsupplyBound : pre.supplyAtoms.toNat ≤ C.maxAtoms := by
    have hbound : (pre.supplyAtoms.toNat : Int) ≤ Proofs.AssetTransferRefinementV1.u128Max := by
      rw [Int.toNat_of_nonneg hpre.supply.1]
      exact hpre.supply.2
    rw [Proofs.AssetTransferRefinementV1.u128Max_eq_pow] at hbound
    dsimp [C.maxAtoms]
    omega
  have hacct : T.sumOver (T.transition ctx pre cmd).post.balance ps =
      T.sumOver pre.balance ps :=
    T.accepted_conserves_total h ps hs hr ho
  have hacctNat := congrArg Int.toNat hacct
  have hpostNonneg : 0 ≤ T.sumOver (T.transition ctx pre cmd).post.balance ps := by
    rw [hacct]
    exact hpreNonneg
  have hsupply := T.accepted_supply_unchanged h
  have hpostProjection :
      T.sumOver (T.transition ctx pre cmd).post.balance ps + (custody : Int) =
        (T.transition ctx pre cmd).post.supplyAtoms := by
    omega
  have hcomplete := C.completed_totals_preserve_supply hacctNat rfl hpreNat hsupplyBound
  have hchecked := C.checked_completion_accepts_valid_projection hacctNat rfl hpreNat hsupplyBound
  exact ⟨hcomplete.1, hchecked, hpreNonneg, hpostNonneg, preProjection, hpostProjection⟩

end Proofs.AssetTransferCustodyCompositionV1
