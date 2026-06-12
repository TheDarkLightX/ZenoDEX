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

/-!
Two-epoch compounded clamp bound.

The single-epoch lemmas above assume the liquidation engine runs every epoch.
If liquidation is delayed by one epoch (keeper outage, censorship), the price
can move twice before the engine acts, and per-epoch clamps compound
geometrically: each move is bounded relative to the *then-current* price, not
the original one.  `two_epoch_move_bound` makes the compounding explicit:
two `m`-bps clamped moves stay within `2m + m²/10⁴` bps of the original
price.

With production `m = 500` the two-epoch factor is `1025` bps
(`witness_two_epoch_factor`), which exceeds the effective maintenance of
`600` bps (`witness_two_epoch_exceeds_maintenance`): a single missed
liquidation epoch can already exhaust the entire maintenance buffer.  This is
the checked anchor for the `L = 2` row of the insurance shortfall analysis in
`docs/DISASTER_STATE_MINIMIZATION_ANALYSIS.md`.
-/

/-- Two consecutive clamped moves compound: if each move is bounded by `m`
    bps of the then-current price, the total move is bounded by
    `(2m + m²/10⁴)` bps of the original price. -/
theorem two_epoch_move_bound
    (P₀ P₁ P₂ m : ℚ)
    (hm : 0 ≤ m)
    (h1 : |P₁ - P₀| ≤ m * P₀ / 10000)
    (h2 : |P₂ - P₁| ≤ m * P₁ / 10000) :
    |P₂ - P₀| ≤ (2 * m + m ^ 2 / 10000) * P₀ / 10000 := by
  have htri : |P₂ - P₀| ≤ |P₂ - P₁| + |P₁ - P₀| := abs_sub_le P₂ P₁ P₀
  have hP₁le : P₁ ≤ P₀ + m * P₀ / 10000 := by
    have h := le_abs_self (P₁ - P₀)
    linarith
  have hmP₁ : m * P₁ ≤ m * (P₀ + m * P₀ / 10000) :=
    mul_le_mul_of_nonneg_left hP₁le hm
  have hexp : m * (P₀ + m * P₀ / 10000) = m * P₀ + m * (m * P₀) / 10000 := by
    ring
  have hgoal_exp : (2 * m + m ^ 2 / 10000) * P₀ / 10000
      = m * P₀ / 10000 + m * P₀ / 10000 + m * (m * P₀) / 10000 / 10000 := by
    ring
  linarith

/-- Production two-epoch factor: with `m = 500`, two compounded clamped moves
    reach at most `1025` bps of the original price. -/
theorem witness_two_epoch_factor :
    2 * 500 + (500 : ℚ) ^ 2 / 10000 = 1025 := by
  norm_num

/-- One missed liquidation epoch already exhausts production maintenance:
    the two-epoch factor (`1025` bps) exceeds effective maintenance
    (`600` bps).  Insurance is therefore sized by the `L ≥ 2`
    liveness-failure tail, not by single-epoch arithmetic. -/
theorem witness_two_epoch_exceeds_maintenance :
    (600 : ℚ) < 2 * 500 + (500 : ℚ) ^ 2 / 10000 := by
  norm_num

/-!
L-epoch geometric clamp bounds.

`two_epoch_move_bound` is the `k = 2` slice of the general law: along a path
of `k` consecutive `m`-bps clamped moves the price is confined to the
geometric envelope `[P₀·(1 − m/10⁴)^k, P₀·(1 + m/10⁴)^k]`
(`clamped_path_lower` / `clamped_path_upper`).

Two Bernoulli corollaries expose a structural asymmetry between the two
sides of the book under multiplicative clamps:

* downside (long-side loss): the total drop over `k` epochs is
  **subadditive** — at most `k·m` bps of the ORIGINAL price
  (`clamped_path_drop_le_linear`);
* upside (short-side loss): the total rise is **superadditive** — at least
  `k·m` bps (`short_tail_dominates_linear`), and in general the short-side
  tail dominates the long-side tail epoch-for-epoch
  (`short_tail_ge_long_tail`).

Consequence for insurance sizing: the `shortfall(L)` requirement of the
liveness-failure analysis is generated by SHORT liquidations first; sizing
on the long-side tail underestimates the requirement at every `L ≥ 2`.
`witness_three_epoch_tails` pins the production numbers at `L = 3`:
short-side `1576.25` bps versus long-side `1426.25` bps.
-/

/-- Upper geometric envelope: `k` clamped moves keep the price at or below
    `P 0 · (1 + m/10⁴)^k`. -/
theorem clamped_path_upper
    (P : ℕ → ℚ) (m : ℚ) (hm : 0 ≤ m)
    (hstep : ∀ i, |P (i + 1) - P i| ≤ m * P i / 10000) :
    ∀ k, P k ≤ P 0 * (1 + m / 10000) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := hstep k
      have h1 : P (k + 1) ≤ P k + m * P k / 10000 := by
        have h := le_abs_self (P (k + 1) - P k)
        linarith
      have hg : (0 : ℚ) ≤ 1 + m / 10000 := by linarith
      have h3 : P k * (1 + m / 10000) ≤ P 0 * (1 + m / 10000) ^ k * (1 + m / 10000) :=
        mul_le_mul_of_nonneg_right ih hg
      calc P (k + 1) ≤ P k * (1 + m / 10000) := by linarith
        _ ≤ P 0 * (1 + m / 10000) ^ k * (1 + m / 10000) := h3
        _ = P 0 * (1 + m / 10000) ^ (k + 1) := by ring

/-- Lower geometric envelope: `k` clamped moves keep the price at or above
    `P 0 · (1 − m/10⁴)^k` (clamp below one price unit per unit, `m ≤ 10⁴`). -/
theorem clamped_path_lower
    (P : ℕ → ℚ) (m : ℚ) (hm1 : m ≤ 10000)
    (hstep : ∀ i, |P (i + 1) - P i| ≤ m * P i / 10000) :
    ∀ k, P 0 * (1 - m / 10000) ^ k ≤ P k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := hstep k
      have h1 : P k - m * P k / 10000 ≤ P (k + 1) := by
        have h := neg_abs_le (P (k + 1) - P k)
        linarith
      have hg : (0 : ℚ) ≤ 1 - m / 10000 := by linarith
      have h3 : P 0 * (1 - m / 10000) ^ k * (1 - m / 10000) ≤ P k * (1 - m / 10000) :=
        mul_le_mul_of_nonneg_right ih hg
      calc P 0 * (1 - m / 10000) ^ (k + 1)
          = P 0 * (1 - m / 10000) ^ k * (1 - m / 10000) := by ring
        _ ≤ P k * (1 - m / 10000) := h3
        _ = P k - m * P k / 10000 := by ring
        _ ≤ P (k + 1) := h1

/-- Downside subadditivity (Bernoulli): the total drop over `k` clamped
    epochs is at most `k·m` bps of the ORIGINAL price.  Long-side multi-epoch
    tails are no worse than linear. -/
theorem clamped_path_drop_le_linear
    (P : ℕ → ℚ) (m : ℚ) (hm1 : m ≤ 10000) (hP0 : 0 ≤ P 0)
    (hstep : ∀ i, |P (i + 1) - P i| ≤ m * P i / 10000) (k : ℕ) :
    P 0 - P k ≤ (k : ℚ) * (m * P 0 / 10000) := by
  have hlow := clamped_path_lower P m hm1 hstep k
  have hbern : 1 - (k : ℚ) * (m / 10000) ≤ (1 - m / 10000) ^ k := by
    have h := one_add_mul_le_pow (a := -(m / 10000)) (by linarith) k
    calc 1 - (k : ℚ) * (m / 10000) = 1 + (k : ℚ) * (-(m / 10000)) := by ring
      _ ≤ (1 + -(m / 10000)) ^ k := h
      _ = (1 - m / 10000) ^ k := by ring_nf
  have hmul : P 0 * (1 - (k : ℚ) * (m / 10000)) ≤ P 0 * (1 - m / 10000) ^ k :=
    mul_le_mul_of_nonneg_left hbern hP0
  have hexp : P 0 * (1 - (k : ℚ) * (m / 10000))
      = P 0 - (k : ℚ) * (m * P 0 / 10000) := by ring
  linarith

/-- Upside superadditivity (Bernoulli): the upward clamp envelope exceeds the
    linear budget `k·m` bps at every horizon.  Short-side multi-epoch tails
    are at least linear. -/
theorem short_tail_dominates_linear (m : ℚ) (hm : 0 ≤ m) (k : ℕ) :
    (k : ℚ) * (m / 10000) ≤ (1 + m / 10000) ^ k - 1 := by
  have h := one_add_mul_le_pow (a := m / 10000) (by linarith) k
  linarith

/-- Tail asymmetry: at every horizon the short-side envelope tail dominates
    the long-side tail, `1 − (1−x)^k ≤ (1+x)^k − 1` for `x ∈ [0, 1]`
    (equivalently `2 ≤ (1+x)^k + (1−x)^k`). -/
theorem short_tail_ge_long_tail (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - (1 - x) ^ k ≤ (1 + x) ^ k - 1 := by
  have key : ∀ n : ℕ, (1 - x) ^ n ≤ (1 + x) ^ n ∧ 2 ≤ (1 + x) ^ n + (1 - x) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        obtain ⟨hle, hsum⟩ := ih
        have hxm : (0 : ℚ) ≤ 1 - x := by linarith
        have hxp : (0 : ℚ) ≤ 1 + x := by linarith
        have hpow_nonneg : (0 : ℚ) ≤ (1 + x) ^ n := pow_nonneg hxp n
        constructor
        · calc (1 - x) ^ (n + 1) = (1 - x) ^ n * (1 - x) := by ring
            _ ≤ (1 + x) ^ n * (1 - x) := mul_le_mul_of_nonneg_right hle hxm
            _ ≤ (1 + x) ^ n * (1 + x) := by
                apply mul_le_mul_of_nonneg_left _ hpow_nonneg
                linarith
            _ = (1 + x) ^ (n + 1) := by ring
        · have hgap : 0 ≤ x * ((1 + x) ^ n - (1 - x) ^ n) :=
            mul_nonneg hx0 (sub_nonneg.mpr hle)
          have hexp : (1 + x) ^ (n + 1) + (1 - x) ^ (n + 1)
              = ((1 + x) ^ n + (1 - x) ^ n) + x * ((1 + x) ^ n - (1 - x) ^ n) := by
            ring
          linarith
  have h := (key k).2
  linarith

/-- Production `L = 3` tails: short-side envelope `1576.25` bps
    (`(21/20)³ − 1 = 1261/8000`) strictly dominates long-side
    `1426.25` bps (`1 − (19/20)³ = 1141/8000`).  Insurance sized on the
    long-side tail underestimates the short-side requirement. -/
theorem witness_three_epoch_tails :
    (1 + 500 / 10000 : ℚ) ^ 3 - 1 = 1261 / 8000 ∧
    1 - (1 - 500 / 10000 : ℚ) ^ 3 = 1141 / 8000 ∧
    (1141 / 8000 : ℚ) < 1261 / 8000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end PerpEpochSafety

end Proofs
