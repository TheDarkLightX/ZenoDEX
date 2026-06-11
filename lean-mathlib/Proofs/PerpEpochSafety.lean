import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
Epoch-based perp safety (math-only).

This file provides a small, self-contained lemma capturing the core safety knob used by the
epoch-perp risk engine: if the oracle price can move by at most `m` bps per epoch and the
maintenance margin is at least `m` bps, then a position that is maintenance-safe at the old
price cannot be driven to negative collateral by a single oracle update.

This is intentionally stated over `ℚ` to avoid rounding subtleties; the production kernel
uses integer fixed-point arithmetic and is independently verified by SMT.
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

theorem collateral_nonneg_after_bounded_move_with_abs_bound
    (pos P P' C m maint B : ℚ)
    (hP : 0 ≤ P)
    (hm : 0 ≤ m)
    (hmaint : m ≤ maint)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hpos : |pos| ≤ B)
    (hC : B * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (P' - P) := by
  have hmaint0 : 0 ≤ maint := le_trans hm hmaint
  have h10000_pos : 0 < (10000 : ℚ) := by norm_num
  have hfactor : 0 ≤ P * maint / 10000 := by
    have : 0 ≤ P * maint := mul_nonneg hP hmaint0
    exact div_nonneg this (le_of_lt h10000_pos)

  have hbound_scaled : |pos| * P * maint / 10000 ≤ B * P * maint / 10000 := by
    have h1 : |pos| * (P * maint / 10000) ≤ B * (P * maint / 10000) :=
      mul_le_mul_of_nonneg_right hpos hfactor
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h1

  refine collateral_nonneg_after_bounded_move pos P P' C m maint hP hmaint hmove ?_
  exact le_trans hbound_scaled hC

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

/-!
Quantitative headroom and funded-liquidation strengthening.

`collateral_nonneg_after_bounded_move` is qualitative: it shows post-move
equity is non-negative.  The lemmas below strengthen it in two directions:

* `collateral_headroom_after_bounded_move` lower-bounds the post-move equity
  by the explicit headroom `|pos| * P * (maint - m) / 10000`.  It needs
  strictly fewer hypotheses than the qualitative lemma (neither `0 ≤ P` nor
  `m ≤ maint` is required), and the qualitative lemma is re-derived from it
  as `collateral_nonneg_of_headroom`.
* `liquidation_penalty_funded_after_bounded_move` shows that under the
  parameter inequality `penalty * (10000 + m) ≤ 10000 * (maint - m)`, the
  liquidation penalty priced at the post-move price `P'` is covered by the
  post-move equity.  This is the no-bad-debt / liquidator-funding condition:
  the penalty can always be paid out of the liquidated account itself, so a
  runtime cap of the form `min(collateral_after_pnl, raw_penalty)` (the
  `liq_penalty_capped` rule) never binds after a single clamped oracle move,
  and the keeper reward never draws on the insurance fund.

The production defaults satisfy the inequality with slack
(`witness_production_funded_liquidation`): effective maintenance
`maint = 600` bps (500 maintenance + 100 depeg buffer), oracle clamp
`m = 500` bps (`max_oracle_move_bps`), penalty `50` bps:
`50 * 10500 = 525000 ≤ 10000 * 100 = 1000000`.

`witness_headroom_tight` shows the headroom bound is attained (with
`maint = m`, a clamp-edge downward move on a maintenance-exact account leaves
exactly zero equity), so the bound is sharp and cannot be improved without
new hypotheses.
-/

/-- Quantitative headroom: after a bounded oracle move, the post-move equity
    is at least `|pos| * P * (maint - m) / 10000`.  Strengthens
    `collateral_nonneg_after_bounded_move` (which only gives `0 ≤`), and
    drops its `0 ≤ P` and `m ≤ maint` hypotheses. -/
theorem collateral_headroom_after_bounded_move
    (pos P P' C m maint : ℚ)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    |pos| * P * (maint - m) / 10000 ≤ C + pos * (P' - P) := by
  set δ : ℚ := P' - P
  have habs_nonneg : 0 ≤ |pos| := abs_nonneg pos
  have hneg_abs : -(|pos| * |δ|) ≤ pos * δ := by
    have h := neg_abs_le (pos * δ)
    simpa [abs_mul] using h
  have hscaled : |pos| * |δ| ≤ |pos| * (m * P / 10000) :=
    mul_le_mul_of_nonneg_left hmove habs_nonneg
  have halg : |pos| * P * (maint - m) / 10000
      = |pos| * P * maint / 10000 - |pos| * (m * P / 10000) := by
    ring
  linarith

/-- The qualitative theorem re-derived from the quantitative headroom bound:
    when the headroom floor is non-negative (`m ≤ maint`, `0 ≤ P`), post-move
    equity is non-negative.  Same statement as
    `collateral_nonneg_after_bounded_move`; recorded to show the strict
    generalization. -/
theorem collateral_nonneg_of_headroom
    (pos P P' C m maint : ℚ)
    (hP : 0 ≤ P)
    (hmaint : m ≤ maint)
    (hmove : |P' - P| ≤ m * P / 10000)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    0 ≤ C + pos * (P' - P) := by
  have hfloor := collateral_headroom_after_bounded_move pos P P' C m maint hmove hC
  have hnum : 0 ≤ |pos| * P * (maint - m) :=
    mul_nonneg (mul_nonneg (abs_nonneg pos) hP) (by linarith)
  have hquot : 0 ≤ |pos| * P * (maint - m) / 10000 :=
    div_nonneg hnum (by norm_num)
  linarith

/-- **Funded liquidation.**  Under the parameter inequality
    `penalty * (10000 + m) ≤ 10000 * (maint - m)`, the post-move equity covers
    the liquidation penalty priced at the post-move price `P'`.  The
    liquidated account itself funds the liquidator after any single clamped
    oracle move: no insurance-fund draw and no bad debt. -/
theorem liquidation_penalty_funded_after_bounded_move
    (pos P P' C m maint penalty : ℚ)
    (hP : 0 ≤ P)
    (hpen : 0 ≤ penalty)
    (hparam : penalty * (10000 + m) ≤ 10000 * (maint - m))
    (hmove : |P' - P| ≤ m * P / 10000)
    (hC : |pos| * P * maint / 10000 ≤ C) :
    |pos| * P' * penalty / 10000 ≤ C + pos * (P' - P) := by
  have hfloor := collateral_headroom_after_bounded_move pos P P' C m maint hmove hC
  have habs_nonneg : 0 ≤ |pos| := abs_nonneg pos
  have hP'le : P' ≤ P * (10000 + m) / 10000 := by
    have h1 : P' - P ≤ m * P / 10000 := le_trans (le_abs_self _) hmove
    have h2 : P * (10000 + m) / 10000 = P + m * P / 10000 := by ring
    linarith
  have hA : |pos| * P' * penalty ≤ |pos| * P * (penalty * (10000 + m)) / 10000 := by
    have h1 : |pos| * P' ≤ |pos| * (P * (10000 + m) / 10000) :=
      mul_le_mul_of_nonneg_left hP'le habs_nonneg
    have h2 : |pos| * P' * penalty ≤ |pos| * (P * (10000 + m) / 10000) * penalty :=
      mul_le_mul_of_nonneg_right h1 hpen
    have h3 : |pos| * (P * (10000 + m) / 10000) * penalty
        = |pos| * P * (penalty * (10000 + m)) / 10000 := by ring
    linarith
  have hB : |pos| * P * (penalty * (10000 + m)) ≤ 10000 * (|pos| * P * (maint - m)) := by
    have h1 : |pos| * P * (penalty * (10000 + m)) ≤ |pos| * P * (10000 * (maint - m)) :=
      mul_le_mul_of_nonneg_left hparam (mul_nonneg habs_nonneg hP)
    have h2 : |pos| * P * (10000 * (maint - m)) = 10000 * (|pos| * P * (maint - m)) := by
      ring
    linarith
  linarith

/-- Sharpness witness for the headroom bound: with `maint = m = 600`,
    `pos = 1`, `P = 10000`, a clamp-edge downward move on a
    maintenance-exact account (`C = 600`) leaves exactly the headroom floor
    (zero).  The bound is attained, hence not improvable. -/
theorem witness_headroom_tight :
    (600 : ℚ) + 1 * ((10000 - 600) - 10000) = |(1 : ℚ)| * 10000 * (600 - 600) / 10000 := by
  norm_num

/-- Production-parameter witness: effective maintenance 600 bps
    (500 maintenance + 100 depeg buffer), oracle clamp 500 bps
    (`max_oracle_move_bps`), and liquidation penalty 50 bps satisfy the
    funded-liquidation inequality with slack. -/
theorem witness_production_funded_liquidation :
    (50 : ℚ) * (10000 + 500) ≤ 10000 * (600 - 500) := by
  norm_num

/-- End-to-end production witness: `pos = 1`, `P = 10000`, worst-case
    downward move to `P' = 9500` (clamp 500 bps), collateral exactly at
    maintenance (600 bps).  Post-move equity (100) covers the penalty at the
    new price (47.5). -/
theorem witness_production_penalty_funded :
    |(1 : ℚ)| * 9500 * 50 / 10000 ≤ 600 + 1 * (9500 - 10000) := by
  norm_num

end PerpEpochSafety

end Proofs
