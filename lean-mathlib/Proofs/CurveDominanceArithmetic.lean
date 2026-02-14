import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Curve Dominance Arithmetic Obligations

These lemmas capture the arithmetic side-conditions that keep
`curve_dominance_check_v1` inductive:

1. Slippage expressions are nonnegative under nonnegative inputs.
2. The reserve-based slippage expression is bounded by the metric type range.
3. If slippage is known nonnegative, "both better" / tradeoff antecedents are impossible.
-/

namespace Proofs
namespace CurveDominanceArithmetic

def slippageSetAlpha (alpha : Int) : Int :=
  (alpha * 5) / 10

def slippageSetTrade (alpha trade : Int) : Int :=
  (alpha * (5 + trade / 100)) / 10

def slippageSetReserves (alpha x y : Int) : Int :=
  (alpha * ((x + y) / 100)) / 20

theorem slippage_set_alpha_nonneg {alpha : Int} (hAlpha : 0 ≤ alpha) :
    0 ≤ slippageSetAlpha alpha := by
  unfold slippageSetAlpha
  have hMul : 0 ≤ alpha * 5 := mul_nonneg hAlpha (by decide)
  exact Int.ediv_nonneg hMul (by decide)

theorem slippage_set_trade_nonneg {alpha trade : Int}
    (hAlpha : 0 ≤ alpha) (hTrade : 0 ≤ trade) :
    0 ≤ slippageSetTrade alpha trade := by
  unfold slippageSetTrade
  have hTradeDiv : 0 ≤ trade / 100 := Int.ediv_nonneg hTrade (by decide)
  have hFactor : 0 ≤ 5 + trade / 100 := by linarith
  have hMul : 0 ≤ alpha * (5 + trade / 100) := mul_nonneg hAlpha hFactor
  exact Int.ediv_nonneg hMul (by decide)

theorem slippage_set_reserves_nonneg {alpha x y : Int}
    (hAlpha : 0 ≤ alpha) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ slippageSetReserves alpha x y := by
  unfold slippageSetReserves
  have hXY : 0 ≤ x + y := by linarith
  have hDiv : 0 ≤ (x + y) / 100 := Int.ediv_nonneg hXY (by decide)
  have hMul : 0 ≤ alpha * ((x + y) / 100) := mul_nonneg hAlpha hDiv
  exact Int.ediv_nonneg hMul (by decide)

def slippageSetReservesNat (alpha x y : Nat) : Nat :=
  (alpha * ((x + y) / 100)) / 20

theorem slippage_set_reserves_nat_le_2000
    {alpha x y : Nat}
    (hAlpha : alpha ≤ 200)
    (hx : x ≤ 10000)
    (hy : y ≤ 10000) :
    slippageSetReservesNat alpha x y ≤ 2000 := by
  unfold slippageSetReservesNat
  have hSum : x + y ≤ 20000 := by omega
  have hDiv100 : (x + y) / 100 ≤ 200 := by
    have hMul : x + y ≤ 200 * 100 := by simpa using hSum
    exact Nat.div_le_of_le_mul hMul
  have hNumerator : alpha * ((x + y) / 100) ≤ 40000 := by
    calc
      alpha * ((x + y) / 100) ≤ 200 * 200 := Nat.mul_le_mul hAlpha hDiv100
      _ = 40000 := by norm_num
  have hDiv20 : (alpha * ((x + y) / 100)) / 20 ≤ 40000 / 20 := Nat.div_le_div_right hNumerator
  calc
    (alpha * ((x + y) / 100)) / 20 ≤ 40000 / 20 := hDiv20
    _ = 2000 := by norm_num

theorem no_both_better_if_slippage_nonneg {slippage il : Int}
    (hSlip : 0 ≤ slippage) :
    ¬ (slippage < 0 ∧ il < 0) := by
  intro hBoth
  exact (not_lt_of_ge hSlip) hBoth.1

theorem tradeoff_antecedent_false_if_slippage_nonneg {slippage : Int}
    (hSlip : 0 ≤ slippage) :
    ¬ (slippage < -10) := by
  intro hLt
  have hLtZero : slippage < 0 := by
    have hNegTen : (-10 : Int) < 0 := by decide
    exact lt_trans hLt hNegTen
  exact (not_lt_of_ge hSlip) hLtZero

end CurveDominanceArithmetic
end Proofs
