import Mathlib

namespace ZenoDEX

/-!
No-overdelivery theorem for the refined cycle 115 2-bucket CPMM surrogate:

`if reserveIn ≤ 680200 then num / 748221 else num / 1100000`

under model bounds:
- `reserveIn ≤ 1000000`
- `0 < netIn`
- guard `netIn * 10 ≤ reserveIn`
-/

def cpmmP2EnvelopeOutV2 (reserveIn reserveOut netIn : Nat) : Nat :=
  let num := reserveOut * netIn
  if reserveIn ≤ 680200 then
    num / 748221
  else
    num / 1100000

theorem cpmmP2EnvelopeV2_branch1_den_bound
    (reserveIn netIn : Nat)
    (hLo : reserveIn ≤ 680200)
    (hGuard : netIn * 10 ≤ reserveIn) :
    reserveIn + netIn ≤ 748221 := by
  have hnetMul : netIn * 10 ≤ 680200 := le_trans hGuard hLo
  omega

theorem cpmmP2EnvelopeV2_branch2_den_bound
    (reserveIn netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hGuard : netIn * 10 ≤ reserveIn) :
    reserveIn + netIn ≤ 1100000 := by
  have hnetMul : netIn * 10 ≤ 1000000 := le_trans hGuard hIn
  omega

theorem cpmmP2EnvelopeV2_boundary_left
    (reserveOut netIn : Nat) :
    cpmmP2EnvelopeOutV2 680200 reserveOut netIn =
      (reserveOut * netIn) / 748221 := by
  simp [cpmmP2EnvelopeOutV2]

theorem cpmmP2EnvelopeV2_boundary_right
    (reserveIn reserveOut netIn : Nat)
    (hHi : 680200 < reserveIn) :
    cpmmP2EnvelopeOutV2 reserveIn reserveOut netIn =
      (reserveOut * netIn) / 1100000 := by
  have hNotLe : ¬reserveIn ≤ 680200 := Nat.not_le.mpr hHi
  simp [cpmmP2EnvelopeOutV2, hNotLe]

theorem cpmmP2EnvelopeV2_no_overdelivery
    (reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNetPos : 0 < netIn)
    (hGuard : netIn * 10 ≤ reserveIn) :
    cpmmP2EnvelopeOutV2 reserveIn reserveOut netIn ≤
      (reserveOut * netIn) / (reserveIn + netIn) := by
  unfold cpmmP2EnvelopeOutV2
  by_cases hLo : reserveIn ≤ 680200
  · have hsum : reserveIn + netIn ≤ 748221 :=
      cpmmP2EnvelopeV2_branch1_den_bound reserveIn netIn hLo hGuard
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using
      (Nat.div_le_div_left hsum hpos :
        (reserveOut * netIn) / 748221 ≤ (reserveOut * netIn) / (reserveIn + netIn))
  · have hsum : reserveIn + netIn ≤ 1100000 :=
      cpmmP2EnvelopeV2_branch2_den_bound reserveIn netIn hIn hGuard
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using
      (Nat.div_le_div_left hsum hpos :
        (reserveOut * netIn) / 1100000 ≤ (reserveOut * netIn) / (reserveIn + netIn))

end ZenoDEX
