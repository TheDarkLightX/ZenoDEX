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

/-!
v1.1 clamp lemma.

The v1 kernel assumes the oracle update satisfies a bounded-move inequality.
The v1.1 kernel enforces the same bound by clamping the raw update into the admissible band.
The lemmas below make that reduction explicit: once the move is clamped, the v1 solvency lemma
applies verbatim with `P' := clamp_move P P_raw m`.
-/

def clamp_move (P P_raw m : ℚ) : ℚ :=
  let δ := m * P / 10000
  max (P - δ) (min (P + δ) P_raw)

theorem abs_clamp_move_sub_le
    (P P_raw m : ℚ)
    (hP : 0 ≤ P)
    (hm : 0 ≤ m) :
    |clamp_move P P_raw m - P| ≤ m * P / 10000 := by
  set δ : ℚ := m * P / 10000
  have h10000_pos : 0 < (10000 : ℚ) := by norm_num
  have hδ : 0 ≤ δ := by
    have : 0 ≤ m * P := mul_nonneg hm hP
    exact div_nonneg this (le_of_lt h10000_pos)
  have hlohi : P - δ ≤ P + δ := by linarith
  have hlo : P - δ ≤ max (P - δ) (min (P + δ) P_raw) := le_max_left _ _
  have hhi : max (P - δ) (min (P + δ) P_raw) ≤ P + δ := by
    exact (max_le_iff).2 ⟨hlohi, min_le_left _ _⟩

  have h_lower : -δ ≤ max (P - δ) (min (P + δ) P_raw) - P := by linarith [hlo]
  have h_upper : max (P - δ) (min (P + δ) P_raw) - P ≤ δ := by linarith [hhi]
  have habs : |max (P - δ) (min (P + δ) P_raw) - P| ≤ δ :=
    (abs_le).2 ⟨h_lower, h_upper⟩
  -- Rewrite back to the `clamp_move` form.
  simpa [clamp_move, δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using habs

theorem collateral_nonneg_after_clamped_move
    (pos P P_raw C m maint : ℚ)
    (hP : 0 ≤ P)
    (hm : 0 ≤ m)
    (hmaint : m ≤ maint)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (clamp_move P P_raw m - P) := by
  refine collateral_nonneg_after_bounded_move pos P (clamp_move P P_raw m) C m maint hP hmaint ?_ hC
  exact abs_clamp_move_sub_le P P_raw m hP hm

end PerpEpochSafety

end Proofs
