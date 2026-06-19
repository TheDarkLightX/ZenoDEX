import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# CPMM target-price executable lower bound

The runtime target-price search in `src/core/cpmm_target_price.py` starts from
the least gross exact-in amount that can reach a required post-fee net input.
This file proves the integer bridge for that helper:

* `minGrossForNet net feeMultiplier` reaches at least `net` after executable
  floor net recovery;
* every smaller gross amount fails that same net threshold;
* the executable starting amount for a positive CPMM output is sufficient.

The theorem is intentionally integer-only. It does not use the continuous
arbitrage formula; it pins the exact ceil/floor bridge used by consensus code.
-/

namespace TauSwap
namespace CPMM
namespace TargetPrice

/-- Basis-points denominator used by the runtime fee formulas. -/
def BPS : Nat := 10000

/-- Runtime helper: least gross amount whose floor net input can reach `net`. -/
def minGrossForNet (net feeMultiplier : Nat) : Nat :=
  (net * BPS) ⌈/⌉ feeMultiplier

/-- Executable post-fee net input for a gross amount and fee multiplier. -/
def executableNetFromGross (gross feeMultiplier : Nat) : Nat :=
  (gross * feeMultiplier) / BPS

/-- Runtime positive-output net threshold: enough net input for floor output ≥ 1. -/
def positiveOutputNetThreshold (reserveIn reserveOut : Nat) : Nat :=
  reserveIn ⌈/⌉ (reserveOut - 1)

/-- CPMM exact-in output after fee has already been converted into `net`. -/
def exactInOutputFromNet (reserveIn reserveOut net : Nat) : Nat :=
  (reserveOut * net) / (reserveIn + net)

/-- Runtime starting gross amount for the first possible positive exact-in output. -/
def minimumExecutableGross (reserveIn reserveOut feeMultiplier : Nat) : Nat :=
  minGrossForNet (positiveOutputNetThreshold reserveIn reserveOut) feeMultiplier

/-- Strictness property of natural ceiling division. -/
lemma mul_lt_of_lt_ceilDiv {b a m : Nat} (ha : 0 < a) (hm : m < b ⌈/⌉ a) :
    a * m < b := by
  have hnot : ¬ b ≤ a * m := by
    intro hle
    have : b ⌈/⌉ a ≤ m := (ceilDiv_le_iff_le_mul ha).2 hle
    exact (not_le_of_gt hm) this
  exact lt_of_not_ge hnot

/-- The ceil-sized gross amount reaches the requested executable net input. -/
theorem minGrossForNet_reaches
    (net feeMultiplier : Nat) (hfee : 0 < feeMultiplier) :
    net ≤ executableNetFromGross (minGrossForNet net feeMultiplier) feeMultiplier := by
  unfold executableNetFromGross minGrossForNet BPS
  have hBPS : 0 < (10000 : Nat) := by decide
  have hceil : net * 10000 ≤ feeMultiplier * ((net * 10000) ⌈/⌉ feeMultiplier) :=
    le_smul_ceilDiv (a := feeMultiplier) (b := net * 10000) hfee
  have hceil' : net * 10000 ≤ ((net * 10000) ⌈/⌉ feeMultiplier) * feeMultiplier := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hceil
  exact (Nat.le_div_iff_mul_le hBPS).2 hceil'

/-- Any gross amount below `minGrossForNet` fails to reach the requested net input. -/
theorem minGrossForNet_minimal
    (net feeMultiplier gross : Nat)
    (hfee : 0 < feeMultiplier)
    (hgross : gross < minGrossForNet net feeMultiplier) :
    executableNetFromGross gross feeMultiplier < net := by
  unfold executableNetFromGross minGrossForNet BPS at *
  have hBPS : 0 < (10000 : Nat) := by decide
  have hmul : feeMultiplier * gross < net * 10000 :=
    mul_lt_of_lt_ceilDiv (b := net * 10000) (a := feeMultiplier) (m := gross) hfee hgross
  have hmul' : gross * feeMultiplier < net * 10000 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact (Nat.div_lt_iff_lt_mul hBPS).2 hmul'

/-- The net threshold is sufficient for a positive floor-rounded CPMM output. -/
theorem positiveOutputNetThreshold_sufficient
    {reserveIn reserveOut net : Nat}
    (hreserveIn : 0 < reserveIn)
    (hreserveOut : 1 < reserveOut)
    (hnet : positiveOutputNetThreshold reserveIn reserveOut ≤ net) :
    0 < exactInOutputFromNet reserveIn reserveOut net := by
  unfold exactInOutputFromNet positiveOutputNetThreshold at *
  have hdenOut : 0 < reserveOut - 1 := Nat.sub_pos_of_lt hreserveOut
  have hthreshold :
      reserveIn ≤ (reserveOut - 1) * (reserveIn ⌈/⌉ (reserveOut - 1)) :=
    le_smul_ceilDiv (a := reserveOut - 1) (b := reserveIn) hdenOut
  have hreserve_le : reserveIn ≤ (reserveOut - 1) * net := by
    exact hthreshold.trans (Nat.mul_le_mul_left (reserveOut - 1) hnet)
  have hden_le_num : reserveIn + net ≤ reserveOut * net := by
    calc
      reserveIn + net ≤ (reserveOut - 1) * net + net := Nat.add_le_add_right hreserve_le net
      _ = reserveOut * net := by
        have hsplit : reserveOut = (reserveOut - 1) + 1 := by omega
        rw [hsplit]
        rw [Nat.add_sub_cancel]
        rw [Nat.add_mul, one_mul]
  have hden_pos : 0 < reserveIn + net := Nat.add_pos_left hreserveIn net
  exact Nat.div_pos hden_le_num hden_pos

/--
The executable gross starting point used by target-price search produces a
positive output whenever output reserves and the fee multiplier are live.
-/
theorem minimumExecutableGross_produces_positive_output
    {reserveIn reserveOut feeMultiplier : Nat}
    (hreserveIn : 0 < reserveIn)
    (hreserveOut : 1 < reserveOut)
    (hfee : 0 < feeMultiplier) :
    0 < exactInOutputFromNet reserveIn reserveOut
      (executableNetFromGross (minimumExecutableGross reserveIn reserveOut feeMultiplier) feeMultiplier) := by
  apply positiveOutputNetThreshold_sufficient hreserveIn hreserveOut
  unfold minimumExecutableGross
  exact minGrossForNet_reaches (positiveOutputNetThreshold reserveIn reserveOut) feeMultiplier hfee

/-- Non-vacuity witness for the executable gross sizing formula. -/
example :
    minGrossForNet 100 9970 = 101 ∧
      executableNetFromGross (minGrossForNet 100 9970) 9970 = 100 ∧
      executableNetFromGross 100 9970 < 100 := by
  native_decide

/-- Non-vacuity witness for the positive-output starting point. -/
example :
    0 < exactInOutputFromNet 100 200
      (executableNetFromGross (minimumExecutableGross 100 200 9970) 9970) := by
  native_decide

end TargetPrice
end CPMM
end TauSwap
