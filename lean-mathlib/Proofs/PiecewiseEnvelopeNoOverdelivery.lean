import Mathlib

namespace ZenoDEX

/-!
No-overdelivery theorem for the envelope-tight 2-bucket CPMM surrogate used in
cycle 114 experiments:

`if reserveIn ≤ 640000 then num / 704000 else num / 1100000`

under model bounds:
- `reserveIn ≤ 1000000`
- `0 < netIn`
- guard `netIn * 10 ≤ reserveIn`
-/

def cpmmP2EnvelopeOut (reserveIn reserveOut netIn : Nat) : Nat :=
  let num := reserveOut * netIn
  if reserveIn ≤ 640000 then
    num / 704000
  else
    num / 1100000

theorem cpmmP2Envelope_branch1_den_bound
    (reserveIn netIn : Nat)
    (hLo : reserveIn ≤ 640000)
    (hGuard : netIn * 10 ≤ reserveIn) :
    reserveIn + netIn ≤ 704000 := by
  have hnetMul : netIn * 10 ≤ 640000 := le_trans hGuard hLo
  omega

theorem cpmmP2Envelope_branch2_den_bound
    (reserveIn netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hGuard : netIn * 10 ≤ reserveIn) :
    reserveIn + netIn ≤ 1100000 := by
  have hnetMul : netIn * 10 ≤ 1000000 := le_trans hGuard hIn
  omega

theorem cpmmP2Envelope_no_overdelivery
    (reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNetPos : 0 < netIn)
    (hGuard : netIn * 10 ≤ reserveIn) :
    cpmmP2EnvelopeOut reserveIn reserveOut netIn ≤
      (reserveOut * netIn) / (reserveIn + netIn) := by
  unfold cpmmP2EnvelopeOut
  by_cases hLo : reserveIn ≤ 640000
  · have hsum : reserveIn + netIn ≤ 704000 :=
      cpmmP2Envelope_branch1_den_bound reserveIn netIn hLo hGuard
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using (Nat.div_le_div_left hsum hpos : (reserveOut * netIn) / 704000 ≤ (reserveOut * netIn) / (reserveIn + netIn))
  · have hsum : reserveIn + netIn ≤ 1100000 :=
      cpmmP2Envelope_branch2_den_bound reserveIn netIn hIn hGuard
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using (Nat.div_le_div_left hsum hpos : (reserveOut * netIn) / 1100000 ≤ (reserveOut * netIn) / (reserveIn + netIn))

end ZenoDEX
