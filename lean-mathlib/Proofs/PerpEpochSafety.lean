import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
Epoch-based perp safety (math-only).

This file provides a small, self-contained lemma capturing the core safety knob used by the
epoch-perp risk engine: if the oracle price can move by at most `m` bps per epoch and the
maintenance margin is at least `m` bps, then a position that is maintenance-safe at the old
price cannot be driven to negative collateral by a single oracle update.

This is intentionally stated over `ℚ` to avoid rounding subtleties; the ESSO kernel uses
integer fixed-point arithmetic and is independently verified by SMT.
-/

namespace Proofs

namespace PerpEpochSafety

theorem collateral_nonneg_after_bounded_move
    (pos P P' C m maint : ℚ)
    (hP : 0 ≤ P)
    (hmaint : m ≤ maint)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (P' - P) := by
  set δ : ℚ := P' - P
  have hneg_abs : -( |pos| * |δ| ) ≤ pos * δ := by
    -- `- |pos * δ| ≤ pos * δ`, and `|pos * δ| = |pos| * |δ|`.
    have h := neg_abs_le (pos * δ)
    simpa [δ, abs_mul, mul_assoc, mul_left_comm, mul_comm] using h

  have hδ_le : |pos| * |δ| ≤ |pos| * (m * P / 10000) := by
    have hpos_nonneg : 0 ≤ |pos| := abs_nonneg pos
    -- Multiply the bounded-move hypothesis by `|pos| ≥ 0`.
    have : |pos| * |δ| ≤ |pos| * (m * P / 10000) :=
      mul_le_mul_of_nonneg_left (by simpa [δ] using hmove) hpos_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  have hmargin_m : |pos| * (m * P / 10000) ≤ |pos| * P * maint / 10000 := by
    have hpos_nonneg : 0 ≤ |pos| := abs_nonneg pos
    have hP_nonneg : 0 ≤ P := hP
    have h10000_pos : 0 < (10000 : ℚ) := by norm_num
    -- From `m ≤ maint` and `P ≥ 0`, we get `m * P ≤ maint * P`.
    have hmP : m * P ≤ maint * P := mul_le_mul_of_nonneg_right hmaint hP_nonneg
    -- Multiply by `|pos| ≥ 0`.
    have h1 : |pos| * (m * P) ≤ |pos| * (maint * P) :=
      mul_le_mul_of_nonneg_left hmP hpos_nonneg
    -- Divide by a positive constant preserves the inequality.
    have h2 : |pos| * (m * P) / 10000 ≤ |pos| * (maint * P) / 10000 :=
      div_le_div_of_nonneg_right h1 (le_of_lt h10000_pos)
    -- Reassociate to match the statement.
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h2

  have hpos_abs_delta_le_C : |pos| * |δ| ≤ C :=
    le_trans hδ_le (le_trans hmargin_m hC)

  have hC_sub : 0 ≤ C - |pos| * |δ| := by
    exact sub_nonneg.mpr hpos_abs_delta_le_C

  -- Combine: `C - |pos||δ| ≤ C + pos·δ` and `0 ≤ C - |pos||δ|`.
  have hbridge : C - |pos| * |δ| ≤ C + pos * δ := by
    linarith [hneg_abs]

  have : 0 ≤ C + pos * δ := le_trans hC_sub hbridge
  simpa [δ, mul_assoc, mul_left_comm, mul_comm] using this

end PerpEpochSafety

end Proofs
