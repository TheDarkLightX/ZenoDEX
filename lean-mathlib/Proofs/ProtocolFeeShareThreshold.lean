import Mathlib.Tactic

/-!
# Protocol Fee Share Threshold (LP residual channel)

This file captures a simple arithmetic model used in game-theory analysis:

- `lpResidual` is the LP-visible residual after protocol fee capture.
- At full protocol capture (`protocolFeeShare = 10000 bps`), residual is exactly `0`.
- Increasing protocol fee share is monotone non-increasing for LP residual.
- If the pre-capture base is large enough and fee share is not full capture, residual is at least `1`.

The purpose is to formalize the threshold structure used by attack-boundary hypotheses.
-/

namespace Proofs
namespace ProtocolFeeShareThreshold

def BPS : Nat := 10000

def lpResidual (poolDelta lpShare protocolFeeShare : Nat) : Nat :=
  let base := (poolDelta * lpShare) / BPS
  (base * (BPS - protocolFeeShare)) / BPS

theorem lpResidual_full_capture_zero (poolDelta lpShare : Nat) :
    lpResidual poolDelta lpShare BPS = 0 := by
  simp [lpResidual, BPS]

theorem lpResidual_monotone_in_protocol_capture {poolDelta lpShare pfs₁ pfs₂ : Nat}
    (hcap : pfs₁ ≤ pfs₂) :
    lpResidual poolDelta lpShare pfs₂ ≤ lpResidual poolDelta lpShare pfs₁ := by
  unfold lpResidual
  set base : Nat := (poolDelta * lpShare) / BPS
  have hsub : BPS - pfs₂ ≤ BPS - pfs₁ := Nat.sub_le_sub_left hcap BPS
  have hmul : base * (BPS - pfs₂) ≤ base * (BPS - pfs₁) := Nat.mul_le_mul_left base hsub
  exact Nat.div_le_div_right hmul

theorem lpResidual_positive_if_large_base_and_not_full_capture {poolDelta lpShare pfs : Nat}
    (hbound : pfs < BPS)
    (hbase : BPS ≤ (poolDelta * lpShare) / BPS) :
    1 ≤ lpResidual poolDelta lpShare pfs := by
  unfold lpResidual
  set base : Nat := (poolDelta * lpShare) / BPS
  have hbase' : BPS ≤ base := by simpa [base] using hbase
  have hpos : 0 < BPS - pfs := Nat.sub_pos_of_lt hbound
  have hmul_base : base ≤ base * (BPS - pfs) := by
    exact Nat.le_mul_of_pos_right base hpos
  have hmul : BPS ≤ base * (BPS - pfs) := le_trans hbase' hmul_base
  have hdiv : BPS / BPS ≤ (base * (BPS - pfs)) / BPS := Nat.div_le_div_right hmul
  simpa [BPS, base] using hdiv

end ProtocolFeeShareThreshold
end Proofs
