import Mathlib

namespace ZenoDEX

/-!
Parameterized no-overdelivery theorem for 2-bucket piecewise CPMM surrogates.

This file removes hardcoded constants by proving a generic family:

`if reserveIn ≤ t then num / d1 else num / d2`

under the standard guard `netIn * 10 ≤ reserveIn`, reserve cap bounds, and
envelope side conditions on denominators.
-/

def cpmmPiecewiseOutParam
    (t d1 d2 reserveIn reserveOut netIn : Nat) : Nat :=
  let num := reserveOut * netIn
  if reserveIn ≤ t then
    num / d1
  else
    num / d2

theorem cpmmPiecewise_branch1_den_bound
    (t d1 reserveIn netIn : Nat)
    (hLo : reserveIn ≤ t)
    (hGuard : netIn * 10 ≤ reserveIn)
    (hEnv1 : 11 * t ≤ 10 * d1) :
    reserveIn + netIn ≤ d1 := by
  have hnet10 : netIn * 10 ≤ t := le_trans hGuard hLo
  have hsum10 : 10 * (reserveIn + netIn) ≤ 11 * t := by
    omega
  have hsum10' : 10 * (reserveIn + netIn) ≤ 10 * d1 := le_trans hsum10 hEnv1
  omega

theorem cpmmPiecewise_branch2_den_bound
    (reserveCap d2 reserveIn netIn : Nat)
    (hIn : reserveIn ≤ reserveCap)
    (hGuard : netIn * 10 ≤ reserveIn)
    (hEnv2 : 11 * reserveCap ≤ 10 * d2) :
    reserveIn + netIn ≤ d2 := by
  have hnet10 : netIn * 10 ≤ reserveCap := le_trans hGuard hIn
  have hsum10 : 10 * (reserveIn + netIn) ≤ 11 * reserveCap := by
    omega
  have hsum10' : 10 * (reserveIn + netIn) ≤ 10 * d2 := le_trans hsum10 hEnv2
  omega

theorem cpmmPiecewiseOutParam_no_overdelivery
    (t d1 d2 reserveCap reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ reserveCap)
    (hNetPos : 0 < netIn)
    (hGuard : netIn * 10 ≤ reserveIn)
    (hEnv1 : 11 * t ≤ 10 * d1)
    (hEnv2 : 11 * reserveCap ≤ 10 * d2) :
    cpmmPiecewiseOutParam t d1 d2 reserveIn reserveOut netIn ≤
      (reserveOut * netIn) / (reserveIn + netIn) := by
  unfold cpmmPiecewiseOutParam
  by_cases hLo : reserveIn ≤ t
  · have hsum : reserveIn + netIn ≤ d1 :=
      cpmmPiecewise_branch1_den_bound t d1 reserveIn netIn hLo hGuard hEnv1
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using
      (Nat.div_le_div_left hsum hpos :
        (reserveOut * netIn) / d1 ≤ (reserveOut * netIn) / (reserveIn + netIn))
  · have hsum : reserveIn + netIn ≤ d2 :=
      cpmmPiecewise_branch2_den_bound reserveCap d2 reserveIn netIn hIn hGuard hEnv2
    have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hNetPos
    simpa [hLo] using
      (Nat.div_le_div_left hsum hpos :
        (reserveOut * netIn) / d2 ≤ (reserveOut * netIn) / (reserveIn + netIn))

theorem cpmmPiecewiseOutParam_v2_no_overdelivery
    (reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNetPos : 0 < netIn)
    (hGuard : netIn * 10 ≤ reserveIn) :
    cpmmPiecewiseOutParam 680200 748221 1100000 reserveIn reserveOut netIn ≤
      (reserveOut * netIn) / (reserveIn + netIn) := by
  have hEnv1 : 11 * 680200 ≤ 10 * 748221 := by decide
  have hEnv2 : 11 * 1000000 ≤ 10 * 1100000 := by decide
  simpa using
    cpmmPiecewiseOutParam_no_overdelivery
      680200 748221 1100000 1000000 reserveIn reserveOut netIn
      hIn hNetPos hGuard hEnv1 hEnv2

end ZenoDEX
