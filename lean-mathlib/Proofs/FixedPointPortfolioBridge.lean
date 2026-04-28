import Proofs.FixedPointIntervalBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Fixed-Point Portfolio Bridge

This packet lifts the one-value fixed-point bridge to finite portfolios.

If every real leg `x i` lies in `[L i, U i]`, then summing floor-decoded
fixed-point legs stays inside the portfolio interval with one lower-side tick
of buffer per leg.  Summing ceil-decoded legs has the symmetric upper-side
buffer.

This is the reusable numerical rule needed for multi-leg payoff bundles,
portfolio delta tables, and batch settlement receipts.
-/

namespace Proofs
namespace FixedPointPortfolioBridge

open FixedPointIntervalBridge
open scoped BigOperators

variable {ι : Type _}

noncomputable section

/-- Runtime rounding direction for a settlement leg. -/
inductive RoundingMode where
  | floor
  | ceil
  deriving DecidableEq, Repr

namespace RoundingMode

/-- Lower-side interval buffer introduced by this rounding mode. -/
def lowerBuffer (mode : RoundingMode) (scale : ℝ) : ℝ :=
  match mode with
  | floor => tick scale
  | ceil => 0

/-- Upper-side interval buffer introduced by this rounding mode. -/
def upperBuffer (mode : RoundingMode) (scale : ℝ) : ℝ :=
  match mode with
  | floor => 0
  | ceil => tick scale

end RoundingMode

/-- Decode a fixed-point value using the selected runtime rounding mode. -/
def decodeByMode (scale : ℝ) (mode : RoundingMode) (x : ℝ) : ℝ :=
  match mode with
  | RoundingMode.floor => floorDecode scale x
  | RoundingMode.ceil => ceilDecode scale x

/-- A single fixed-point value decoded by an arbitrary rounding mode stays
inside the interval expanded on the side affected by that mode. -/
theorem decodeByMode_mem_expanded_interval
    {scale x L U : ℝ} (mode : RoundingMode)
    (hscale : 0 < scale)
    (hx : L ≤ x ∧ x ≤ U) :
    L - mode.lowerBuffer scale ≤ decodeByMode scale mode x ∧
      decodeByMode scale mode x ≤ U + mode.upperBuffer scale := by
  cases mode
  · have h := floorDecode_mem_expanded_interval
      (scale := scale) (x := x) (L := L) (U := U) hscale hx
    constructor
    · simpa [RoundingMode.lowerBuffer, decodeByMode] using le_of_lt h.1
    · simpa [RoundingMode.upperBuffer, decodeByMode] using h.2
  · have h := ceilDecode_mem_expanded_interval
      (scale := scale) (x := x) (L := L) (U := U) hscale hx
    constructor
    · simpa [RoundingMode.lowerBuffer, decodeByMode] using h.1
    · simpa [RoundingMode.upperBuffer, decodeByMode] using le_of_lt h.2

/-- Sum of lower per-leg tick buffers. -/
theorem sum_sub_tick_eq_sum_sub_card_mul_tick
    [DecidableEq ι] (S : Finset ι) (L : ι → ℝ) (scale : ℝ) :
    (S.sum fun i => L i - tick scale) =
      (S.sum fun i => L i) - (S.card : ℝ) * tick scale := by
  simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Sum of upper per-leg tick buffers. -/
theorem sum_add_tick_eq_sum_add_card_mul_tick
    [DecidableEq ι] (S : Finset ι) (U : ι → ℝ) (scale : ℝ) :
    (S.sum fun i => U i + tick scale) =
      (S.sum fun i => U i) + (S.card : ℝ) * tick scale := by
  simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- A finite portfolio of floor-decoded fixed-point legs stays within the
aggregate interval expanded downward by one tick per leg. -/
theorem sum_floorDecode_mem_expanded_interval
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ} (hscale : 0 < scale)
    {x L U : ι → ℝ}
    (hx : ∀ i, i ∈ S → L i ≤ x i ∧ x i ≤ U i) :
    (S.sum fun i => L i - tick scale) ≤
        S.sum (fun i => floorDecode scale (x i)) ∧
      S.sum (fun i => floorDecode scale (x i)) ≤
        S.sum U := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt
      (floorDecode_mem_expanded_interval
        (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).1
  · apply Finset.sum_le_sum
    intro i hi
    exact
      (floorDecode_mem_expanded_interval
        (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).2

/-- A finite portfolio of ceil-decoded fixed-point legs stays within the
aggregate interval expanded upward by one tick per leg. -/
theorem sum_ceilDecode_mem_expanded_interval
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ} (hscale : 0 < scale)
    {x L U : ι → ℝ}
    (hx : ∀ i, i ∈ S → L i ≤ x i ∧ x i ≤ U i) :
    S.sum L ≤
        S.sum (fun i => ceilDecode scale (x i)) ∧
      S.sum (fun i => ceilDecode scale (x i)) ≤
        S.sum (fun i => U i + tick scale) := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact
      (ceilDecode_mem_expanded_interval
        (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).1
  · apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt
      (ceilDecode_mem_expanded_interval
        (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).2

/-- Same floor portfolio bound, normalized as `sum L - card * tick`. -/
theorem sum_floorDecode_mem_card_expanded_interval
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ} (hscale : 0 < scale)
    {x L U : ι → ℝ}
    (hx : ∀ i, i ∈ S → L i ≤ x i ∧ x i ≤ U i) :
    S.sum L - (S.card : ℝ) * tick scale ≤
        S.sum (fun i => floorDecode scale (x i)) ∧
      S.sum (fun i => floorDecode scale (x i)) ≤
        S.sum U := by
  rw [← sum_sub_tick_eq_sum_sub_card_mul_tick S L scale]
  exact sum_floorDecode_mem_expanded_interval S hscale hx

/-- Same ceil portfolio bound, normalized as `sum U + card * tick`. -/
theorem sum_ceilDecode_mem_card_expanded_interval
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ} (hscale : 0 < scale)
    {x L U : ι → ℝ}
    (hx : ∀ i, i ∈ S → L i ≤ x i ∧ x i ≤ U i) :
    S.sum L ≤
        S.sum (fun i => ceilDecode scale (x i)) ∧
      S.sum (fun i => ceilDecode scale (x i)) ≤
        S.sum U + (S.card : ℝ) * tick scale := by
  rw [← sum_add_tick_eq_sum_add_card_mul_tick S U scale]
  exact sum_ceilDecode_mem_expanded_interval S hscale hx

/-- A finite portfolio decoded with per-leg rounding modes stays within the
aggregate interval expanded only on the sides affected by each leg's mode. -/
theorem sum_decodeByMode_mem_expanded_interval
    [DecidableEq ι] (S : Finset ι)
    {scale : ℝ} (hscale : 0 < scale)
    {mode : ι → RoundingMode}
    {x L U : ι → ℝ}
    (hx : ∀ i, i ∈ S → L i ≤ x i ∧ x i ≤ U i) :
    S.sum (fun i => L i - (mode i).lowerBuffer scale) ≤
        S.sum (fun i => decodeByMode scale (mode i) (x i)) ∧
      S.sum (fun i => decodeByMode scale (mode i) (x i)) ≤
        S.sum (fun i => U i + (mode i).upperBuffer scale) := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact
      (decodeByMode_mem_expanded_interval
        (mode i) (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).1
  · apply Finset.sum_le_sum
    intro i hi
    exact
      (decodeByMode_mem_expanded_interval
        (mode i) (scale := scale) (x := x i) (L := L i) (U := U i)
        hscale (hx i hi)).2

end

end FixedPointPortfolioBridge
end Proofs
