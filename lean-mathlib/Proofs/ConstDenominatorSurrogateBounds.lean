import Mathlib

namespace ZenoDEX

theorem div_mul_le_of_le_den {x reserve den : Nat} (hden : reserve ≤ den) :
    (x / den) * reserve ≤ x := by
  have hmul : (x / den) * reserve ≤ (x / den) * den := Nat.mul_le_mul_left (x / den) hden
  exact le_trans hmul (Nat.div_mul_le_self x den)

theorem cpmm_constden_no_overdelivery
    (reserveIn reserveOut netIn den : Nat)
    (hden : reserveIn + netIn ≤ den)
    (hnet : 0 < netIn) :
    (reserveOut * netIn) / den ≤ (reserveOut * netIn) / (reserveIn + netIn) := by
  have hpos : 0 < reserveIn + netIn := Nat.add_pos_right reserveIn hnet
  exact Nat.div_le_div_left hden hpos

theorem cpmm_constden_2097152_safe_under_model_bounds
    (reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNet : netIn ≤ 100000)
    (hNetPos : 0 < netIn) :
    (reserveOut * netIn) / 2097152 ≤ (reserveOut * netIn) / (reserveIn + netIn) := by
  have hsum1100000 : reserveIn + netIn ≤ 1100000 := Nat.add_le_add hIn hNet
  have hsum : reserveIn + netIn ≤ 2097152 := le_trans hsum1100000 (by decide)
  exact cpmm_constden_no_overdelivery reserveIn reserveOut netIn 2097152 hsum hNetPos

theorem cpmm_constden_safe_if_den_ge_1100000
    (reserveIn reserveOut netIn den : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNet : netIn ≤ 100000)
    (hNetPos : 0 < netIn)
    (hDen : 1100000 ≤ den) :
    (reserveOut * netIn) / den ≤ (reserveOut * netIn) / (reserveIn + netIn) := by
  have hsum1100000 : reserveIn + netIn ≤ 1100000 := Nat.add_le_add hIn hNet
  have hsum : reserveIn + netIn ≤ den := le_trans hsum1100000 hDen
  exact cpmm_constden_no_overdelivery reserveIn reserveOut netIn den hsum hNetPos

theorem cpmm_constden_1100000_safe_under_model_bounds
    (reserveIn reserveOut netIn : Nat)
    (hIn : reserveIn ≤ 1000000)
    (hNet : netIn ≤ 100000)
    (hNetPos : 0 < netIn) :
    (reserveOut * netIn) / 1100000 ≤ (reserveOut * netIn) / (reserveIn + netIn) := by
  simpa using cpmm_constden_safe_if_den_ge_1100000 reserveIn reserveOut netIn 1100000 hIn hNet hNetPos (le_rfl : 1100000 ≤ 1100000)

theorem cpmm_constden_1048576_overdelivery_witness :
    let reserveIn := 1000000
    let reserveOut := 1000000
    let netIn := 100000
    (reserveOut * netIn) / 1048576 > (reserveOut * netIn) / (reserveIn + netIn) := by
  native_decide

theorem cpmm_constden_1097728_overdelivery_witness :
    let reserveIn := 1000000
    let reserveOut := 1000000
    let netIn := 100000
    (reserveOut * netIn) / 1097728 > (reserveOut * netIn) / (reserveIn + netIn) := by
  native_decide

theorem lp_constden_min_safe
    (amount0 amount1 lpSupply reserve0 reserve1 den : Nat)
    (h0 : reserve0 ≤ den)
    (h1 : reserve1 ≤ den) :
    let n0 := amount0 * lpSupply
    let n1 := amount1 * lpSupply
    let minted := Nat.min (n0 / den) (n1 / den)
    minted * reserve0 ≤ n0 ∧ minted * reserve1 ≤ n1 := by
  dsimp
  constructor
  · have hmin0 : Nat.min ((amount0 * lpSupply) / den) ((amount1 * lpSupply) / den) ≤ ((amount0 * lpSupply) / den) :=
      Nat.min_le_left _ _
    have hmul0 :
        Nat.min ((amount0 * lpSupply) / den) ((amount1 * lpSupply) / den) * reserve0
          ≤ ((amount0 * lpSupply) / den) * reserve0 :=
      Nat.mul_le_mul_right reserve0 hmin0
    exact le_trans hmul0 (div_mul_le_of_le_den h0)
  · have hmin1 : Nat.min ((amount0 * lpSupply) / den) ((amount1 * lpSupply) / den) ≤ ((amount1 * lpSupply) / den) :=
      Nat.min_le_right _ _
    have hmul1 :
        Nat.min ((amount0 * lpSupply) / den) ((amount1 * lpSupply) / den) * reserve1
          ≤ ((amount1 * lpSupply) / den) * reserve1 :=
      Nat.mul_le_mul_right reserve1 hmin1
    exact le_trans hmul1 (div_mul_le_of_le_den h1)

theorem lp_constden_1048576_safe_under_model_bounds
    (amount0 amount1 lpSupply reserve0 reserve1 : Nat)
    (h0 : reserve0 ≤ 1000000)
    (h1 : reserve1 ≤ 1000000) :
    let n0 := amount0 * lpSupply
    let n1 := amount1 * lpSupply
    let minted := Nat.min (n0 / 1048576) (n1 / 1048576)
    minted * reserve0 ≤ n0 ∧ minted * reserve1 ≤ n1 := by
  have h0' : reserve0 ≤ 1048576 := le_trans h0 (by decide)
  have h1' : reserve1 ≤ 1048576 := le_trans h1 (by decide)
  simpa using lp_constden_min_safe amount0 amount1 lpSupply reserve0 reserve1 1048576 h0' h1'

end ZenoDEX
