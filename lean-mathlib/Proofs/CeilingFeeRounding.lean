import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.DiscreteArgmaxProximity

/-!
# Ceiling-Fee Rounding: Production Model Bounds

This file formally models the production CPMM swap arithmetic (ceiling fee +
floor output) and proves conservative floor error and argmax proximity bounds.
The proved bounds use `K0/M0 + K1/M1 + 2` and `L + K0/M0 + K1/M1 + 2`, which are
weaker than the empirical `2L + 2` and `3L + 2` bounds; the exact empirical
constants are not formally proved here.

## The Production Model

The production v8 kernel (`src/core/cpmm.py`) computes:
```
  fee    = ⌈amount_in * fee_bps / 10000⌉   (ceiling)
  net    = amount_in - fee                  (net input after fee)
  output = ⌊K * net / (M + net)⌋           (floor output)
```

The clean model (proven in `DiscreteArgmaxProximity.lean`) uses:
```
  net_cont = c * amount_in                  (continuous fee, c = 1 - fee_bps/10000)
  output   = ⌊K * net_cont / (M + net_cont)⌋
```

## Key Insight: Ceiling Fee as Input Perturbation

The ceiling fee perturbs the net input by less than 1 unit. Since `⌈x⌉ - x ∈ [0, 1)`,
we have `net_prod ≤ net_cont` and `net_cont - net_prod ∈ [0, 1)`.

By Lipschitz continuity of `cpmmOutputCont(K, M, ·)` with constant `K/M`
(the maximum derivative, achieved at `x = 0`), the output perturbation is:
`|cont(net_cont) - cont(net_prod)| ≤ (K/M) * |net_cont - net_prod| < K/M`

## What This File Proves

1. **Per-pool output Lipschitz**: `|f(x1) - f(x2)| ≤ (K/M) * |x1 - x2|`
2. **Per-pool production floor error**: `cont(clean) - prodFloor < K/M + 1`
3. **Split production floor error**: `splitCont - splitProdFloor < K0/M0 + K1/M1 + 2`
4. **Production argmax proximity**:
   `splitProdFloor(⌊b*⌋) ≥ splitProdFloor(b) - (L + K0/M0 + K1/M1 + 2)`
5. **Coupled split Lipschitz**:
   `|splitCont(x) - splitCont(y)| ≤ L * |x-y|` where
   `L = max(c0*K0/M0, c1*K1/M1)`.

## Relationship to Empirical Bounds

The low-fee empirical bounds use `L = max(c0*K0/M0, c1*K1/M1)` (split Lipschitz)
and show floor error `< 2L + 2` and argmax proximity `< 3L + 2` on the tested
corpus. The formal bounds here use `K0/M0 + K1/M1` for the production ceiling-fee
perturbation lane and also prove the coupled continuous-split Lipschitz constant
`L`. The gross-spot production bound and the low-fee empirical `3L + 2` bound
are not ordered universally under fees; the relationship depends on pool
parameters. The proved theorems state the conservative `K0/M0 + K1/M1 + 2` and
`L + K0/M0 + K1/M1 + 2` production bounds for all fee settings satisfying the
explicit perturbation hypotheses.

## Non-Claims

- The ceiling fee perturbation bound (`net_cont - net_prod < 1`) is an EXTERNAL
  hypothesis, not proven in Lean.
- The per-pool Lipschitz constant `K/M` is the worst case (at `x=0`).
- The effective-`L` production constants are empirical; the gross-spot
  production lane is the universal formal lane in this file.
- The coupled split Lipschitz constant `L` is an upper bound, not the exact
  split Lipschitz constant in every parameter regime.
- Strong concavity parameter `m` is an external hypothesis.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/CeilingFeeRounding.lean`
-/

open Real

/-! ## Part 1: Production Output Model -/

/-- The production CPMM output function (floored).
    `cpmmOutputProdFloor K M x_net = ⌊K * x_net / (M + x_net)⌋` -/
noncomputable def cpmmOutputProdFloor (K M x_net : ℝ) : ℝ :=
  ↑⌊K * x_net / (M + x_net)⌋

/-- The production 2-pool split function (floored). -/
noncomputable def splitFunctionProdFloor
    (K0 M0 x0 K1 M1 x1 : ℝ) : ℝ :=
  cpmmOutputProdFloor K0 M0 x0 + cpmmOutputProdFloor K1 M1 x1

/-! ## Part 2: Per-Pool Output Lipschitz -/

/-- The CPMM output function is Lipschitz with constant `K/M` with respect
    to the net input `x`, for `K ≥ 0`, `M > 0`, `x ≥ 0`.

    Proof: `f(x1) - f(x2) = K*M*(x1-x2) / ((M+x1)(M+x2))`, and since
    `(M+x1)(M+x2) ≥ M^2`, we get `|f(x1)-f(x2)| ≤ K*M*|x1-x2|/M^2 = (K/M)*|x1-x2|`. -/
lemma cpmm_output_lipschitz_wrt_net
    (K M x1 x2 : ℝ)
    (hK : K ≥ 0) (hM : M > 0) (hx1 : x1 ≥ 0) (hx2 : x2 ≥ 0)
    : |cpmmOutputCont K M x1 - cpmmOutputCont K M x2| ≤ (K / M) * |x1 - x2| := by
  have hM_pos : 0 < M := hM
  have hMx1 : M + x1 > 0 := by nlinarith
  have hMx2 : M + x2 > 0 := by nlinarith
  have h_denom_pos : 0 < (M + x1) * (M + x2) := by nlinarith
  have h_prod_ge_M2 : (M + x1) * (M + x2) ≥ M * M := by nlinarith
  have h_KM_nn : 0 ≤ K * M := mul_nonneg hK (le_of_lt hM)
  have h_diff : cpmmOutputCont K M x1 - cpmmOutputCont K M x2 =
    K * M * (x1 - x2) / ((M + x1) * (M + x2)) := by
    unfold cpmmOutputCont; field_simp; ring
  rw [h_diff]
  rw [abs_le]
  have h_abs_nn : 0 ≤ |x1 - x2| := abs_nonneg (x1 - x2)
  have h_xdiff_le_abs : x1 - x2 ≤ |x1 - x2| := le_abs_self (x1 - x2)
  have h_neg_xdiff_le_abs : -(x1 - x2) ≤ |x1 - x2| := by
    have h := le_abs_self (-(x1 - x2))
    rwa [abs_neg] at h
  have h_KM2_nn : 0 ≤ K * (M * M) := by nlinarith [hK, hM_pos]
  have h_Kabs_nn : 0 ≤ K * |x1 - x2| := mul_nonneg hK h_abs_nn
  refine ⟨?_, ?_⟩
  · -- Lower: -(K/M)*|x1-x2| ≤ K*M*(x1-x2)/denom
    rw [le_div_iff₀ h_denom_pos]
    field_simp
    -- Goal: K * M^2 * (x1-x2) ≥ -K * |x1-x2| * (M+x1)*(M+x2)
    have h_s1 : K * (M * M) * (x1 - x2) ≥ -K * (M * M) * |x1 - x2| := by
      have h_neg_le : -|x1 - x2| ≤ x1 - x2 := by linarith [h_neg_xdiff_le_abs]
      have := mul_le_mul_of_nonneg_left h_neg_le h_KM2_nn
      linarith
    have h_s2 : -K * |x1 - x2| * (M * M) ≥ -K * |x1 - x2| * ((M + x1) * (M + x2)) := by
      have h_pos : K * |x1 - x2| * (M * M) ≤ K * |x1 - x2| * ((M + x1) * (M + x2)) := by
        exact mul_le_mul_of_nonneg_left h_prod_ge_M2 h_Kabs_nn
      linarith
    linarith [h_s1, h_s2]
  · -- Upper: K*M*(x1-x2)/denom ≤ (K/M)*|x1-x2|
    rw [div_le_iff₀ h_denom_pos]
    field_simp
    -- Goal: K * M^2 * (x1-x2) ≤ K * |x1-x2| * (M+x1)*(M+x2)
    have h_s1 : K * (M * M) * (x1 - x2) ≤ K * (M * M) * |x1 - x2| := by
      exact mul_le_mul_of_nonneg_left h_xdiff_le_abs h_KM2_nn
    have h_s2 : K * (M * M) * |x1 - x2| ≤ K * |x1 - x2| * ((M + x1) * (M + x2)) := by
      have := mul_le_mul_of_nonneg_left h_prod_ge_M2 h_Kabs_nn
      linarith
    linarith [h_s1, h_s2]

/-! ## Part 3: Per-Pool Production Floor Error -/

/-- Per-pool production floor error (directed):
    when `net_prod ≤ net_cont` (ceiling fee takes more), the clean continuous
    output minus the production floored output is in `[0, K/M + 1)`. -/
lemma cpmm_prod_floor_error_bound_directed
    (K M net_cont net_prod : ℝ)
    (hK : K ≥ 0) (hM : M > 0)
    (h_net_cont_nn : net_cont ≥ 0) (h_net_prod_nn : net_prod ≥ 0)
    (h_net_prod_le : net_prod ≤ net_cont)
    (h_perturbation : net_cont - net_prod < 1)
    : 0 ≤ cpmmOutputCont K M net_cont - cpmmOutputProdFloor K M net_prod ∧
      cpmmOutputCont K M net_cont - cpmmOutputProdFloor K M net_prod < K / M + 1 := by
  have hM_pos : 0 < M := hM
  have hMx_cont : M + net_cont > 0 := by nlinarith
  have hMx_prod : M + net_prod > 0 := by nlinarith
  have h_diff_nn : 0 ≤ net_cont - net_prod := by nlinarith
  have h_KM_nn : 0 ≤ K * M := mul_nonneg hK (le_of_lt hM)
  have h_f_increasing : cpmmOutputCont K M net_prod ≤ cpmmOutputCont K M net_cont := by
    unfold cpmmOutputCont
    have h_diff : K * net_cont / (M + net_cont) - K * net_prod / (M + net_prod) =
      K * M * (net_cont - net_prod) / ((M + net_cont) * (M + net_prod)) := by
      field_simp; ring
    have h_denom_pos : 0 < (M + net_cont) * (M + net_prod) := by nlinarith
    have h_num_nn : 0 ≤ K * M * (net_cont - net_prod) := by
      nlinarith [h_KM_nn, h_diff_nn]
    have h_frac_nn : 0 ≤ K * M * (net_cont - net_prod) / ((M + net_cont) * (M + net_prod)) :=
      div_nonneg h_num_nn (le_of_lt h_denom_pos)
    linarith [h_diff, h_frac_nn]
  have h_prod_floor_le : cpmmOutputProdFloor K M net_prod ≤ cpmmOutputCont K M net_prod := by
    unfold cpmmOutputProdFloor cpmmOutputCont
    have hz_nn : 0 ≤ K * net_prod / (M + net_prod) := by
      have hKx_nn : 0 ≤ K * net_prod := mul_nonneg hK h_net_prod_nn
      exact div_nonneg hKx_nn (le_of_lt hMx_prod)
    exact_mod_cast Int.floor_le _
  have h_prod_floor_lt : cpmmOutputCont K M net_prod < cpmmOutputProdFloor K M net_prod + 1 := by
    unfold cpmmOutputProdFloor cpmmOutputCont
    have := Int.lt_floor_add_one (K * net_prod / (M + net_prod))
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · -- Lower bound: cont(clean) - prodFloor ≥ 0
    have h_cont_diff_nn : 0 ≤ cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod := by
      linarith [h_f_increasing]
    have h_floor_err_nn : 0 ≤ cpmmOutputCont K M net_prod - cpmmOutputProdFloor K M net_prod := by
      linarith [h_prod_floor_le]
    linarith [h_cont_diff_nn, h_floor_err_nn]
  · -- Upper bound: cont(clean) - prodFloor < K/M + 1
    by_cases hK_zero : K = 0
    · -- K = 0: cpmmOutputCont = 0, cpmmOutputProdFloor = 0
      have h_cont_zero : cpmmOutputCont 0 M net_cont = 0 := by
        unfold cpmmOutputCont; simp
      have h_floor_zero : cpmmOutputProdFloor 0 M net_prod = 0 := by
        unfold cpmmOutputProdFloor
        have h_zero_arg : (0 : ℝ) * net_prod / (M + net_prod) = 0 := by simp
        rw [h_zero_arg, Int.floor_zero, Int.cast_zero]
      rw [hK_zero] at *
      simp [h_cont_zero, h_floor_zero]
    · have h_lip := cpmm_output_lipschitz_wrt_net K M net_cont net_prod
        hK hM h_net_cont_nn h_net_prod_nn
      have h_abs_diff : |net_cont - net_prod| = net_cont - net_prod :=
        abs_of_nonneg h_diff_nn
      rw [h_abs_diff] at h_lip
      have h_cont_diff_le : cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod ≤
          (K / M) * (net_cont - net_prod) := by
        have h_le_abs : cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod ≤
          |cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod| := le_abs_self _
        linarith [h_le_abs, h_lip]
      have hK_pos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK_zero)
      have h_KM_pos : 0 < K / M := div_pos hK_pos hM_pos
      have h_cont_diff_lt : cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod < K / M := by
        nlinarith [h_cont_diff_le, h_perturbation, h_KM_pos]
      have h_floor_err_lt : cpmmOutputCont K M net_prod - cpmmOutputProdFloor K M net_prod < 1 := by
        linarith [h_prod_floor_le, h_prod_floor_lt]
      have h_total : cpmmOutputCont K M net_cont - cpmmOutputProdFloor K M net_prod =
        (cpmmOutputCont K M net_cont - cpmmOutputCont K M net_prod) +
        (cpmmOutputCont K M net_prod - cpmmOutputProdFloor K M net_prod) := by ring
      rw [h_total]
      linarith [h_cont_diff_lt, h_floor_err_lt]

/-! ## Part 4: Split Production Floor Error -/

/-- The production 2-pool split floor error bound.

    If each pool's production net input is within 1 of the clean net input
    (ceiling fee perturbation), and the production net input is ≤ the clean
    net input, then:

    `splitCont - splitProdFloor < K0/M0 + K1/M1 + 2` -/
lemma split_prod_floor_error_bound
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (net_prod0 net_prod1 : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (ha_nn : 0 ≤ a) (_hD_nn : 0 ≤ D) (ha_le_D : a ≤ D)
    (h_net_prod0_nn : net_prod0 ≥ 0) (h_net_prod1_nn : net_prod1 ≥ 0)
    (h_net_prod0_le : net_prod0 ≤ c0 * a)
    (h_net_prod1_le : net_prod1 ≤ c1 * (D - a))
    (h_perturbation0 : c0 * a - net_prod0 < 1)
    (h_perturbation1 : c1 * (D - a) - net_prod1 < 1)
    : 0 ≤ splitFunctionCont K0 M0 c0 K1 M1 c1 D a -
        splitFunctionProdFloor K0 M0 net_prod0 K1 M1 net_prod1 ∧
      splitFunctionCont K0 M0 c0 K1 M1 c1 D a -
        splitFunctionProdFloor K0 M0 net_prod0 K1 M1 net_prod1 <
        K0 / M0 + K1 / M1 + 2 := by
  have h0 := cpmm_prod_floor_error_bound_directed K0 M0 (c0 * a) net_prod0
    hK0 hM0 (mul_nonneg hc0 ha_nn) h_net_prod0_nn h_net_prod0_le h_perturbation0
  have h_Da_nn : 0 ≤ D - a := by nlinarith [ha_le_D]
  have h1 := cpmm_prod_floor_error_bound_directed K1 M1 (c1 * (D - a)) net_prod1
    hK1 hM1 (mul_nonneg hc1 h_Da_nn) h_net_prod1_nn h_net_prod1_le h_perturbation1
  unfold splitFunctionCont splitFunctionProdFloor
  refine ⟨?_, ?_⟩
  · linarith [h0.1, h1.1]
  · linarith [h0.2, h1.2]

/-! ## Part 5: Production Argmax Proximity -/

/-- **Production Argmax Proximity**: The production floored split function
    at `⌊b*⌋` achieves at least `(L + K0/M0 + K1/M1 + 2)` of the
    production discrete optimum.

    This is the production-model counterpart of `cpmm_discrete_argmax_proximity`
    in `DiscreteArgmaxProximity.lean`, with the ceiling-fee perturbation
    error added to the floor error.

    Non-claims:
    - The ceiling fee perturbation bound is external (not proven in Lean)
    - The bound `L + K0/M0 + K1/M1 + 2` and the empirical `3L + 2` are both
      valid; neither is universally tighter. -/
theorem cpmm_prod_discrete_argmax_proximity
    (K0 M0 c0 K1 M1 c1 D L b_star b : ℝ)
    (net_prod0_star net_prod1_star net_prod0_b net_prod1_b : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0) (hb_star_nn : 0 ≤ b_star) (hb_star_le_D : b_star ≤ D)
    (hb_nn : 0 ≤ b) (hb_le_D : b ≤ D)
    (hL : L ≥ 0)
    (h_net_prod0_star_nn : net_prod0_star ≥ 0)
    (h_net_prod1_star_nn : net_prod1_star ≥ 0)
    (h_net_prod0_b_nn : net_prod0_b ≥ 0)
    (h_net_prod1_b_nn : net_prod1_b ≥ 0)
    (h_net_prod0_star_le : net_prod0_star ≤ c0 * ↑⌊b_star⌋)
    (h_net_prod1_star_le : net_prod1_star ≤ c1 * (D - ↑⌊b_star⌋))
    (h_net_prod0_b_le : net_prod0_b ≤ c0 * b)
    (h_net_prod1_b_le : net_prod1_b ≤ c1 * (D - b))
    (h_perturbation0_star : c0 * ↑⌊b_star⌋ - net_prod0_star < 1)
    (h_perturbation1_star : c1 * (D - ↑⌊b_star⌋) - net_prod1_star < 1)
    (h_perturbation0_b : c0 * b - net_prod0_b < 1)
    (h_perturbation1_b : c1 * (D - b) - net_prod1_b < 1)
    (h_lipschitz : ∀ x y : ℝ,
      |splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
       splitFunctionCont K0 M0 c0 K1 M1 c1 D y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    : splitFunctionProdFloor K0 M0 net_prod0_star K1 M1 net_prod1_star ≥
      splitFunctionProdFloor K0 M0 net_prod0_b K1 M1 net_prod1_b -
      (L + K0 / M0 + K1 / M1 + 2) := by
  have h_floor_bstar_nn : (0 : ℝ) ≤ ↑⌊b_star⌋ :=
    floor_nonneg_of_nonneg b_star hb_star_nn
  have h_floor_bstar_le_D : (↑⌊b_star⌋ : ℝ) ≤ D := by
    have h_fl : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
    linarith
  have hD_nn : 0 ≤ D := le_of_lt hD
  have h_floor_err_bstar :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ -
      splitFunctionProdFloor K0 M0 net_prod0_star K1 M1 net_prod1_star <
      K0 / M0 + K1 / M1 + 2 := by
    have h := split_prod_floor_error_bound K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋
      net_prod0_star net_prod1_star
      hK0 hM0 hc0 hK1 hM1 hc1
      h_floor_bstar_nn hD_nn h_floor_bstar_le_D
      h_net_prod0_star_nn h_net_prod1_star_nn
      h_net_prod0_star_le h_net_prod1_star_le
      h_perturbation0_star h_perturbation1_star
    exact h.2
  have h_floor_le_b :
      splitFunctionProdFloor K0 M0 net_prod0_b K1 M1 net_prod1_b ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b := by
    have h0 := cpmm_prod_floor_error_bound_directed K0 M0 (c0 * b) net_prod0_b
      hK0 hM0 (mul_nonneg hc0 hb_nn) h_net_prod0_b_nn
      h_net_prod0_b_le h_perturbation0_b
    have h_Db_nn : 0 ≤ D - b := by nlinarith
    have h1 := cpmm_prod_floor_error_bound_directed K1 M1 (c1 * (D - b)) net_prod1_b
      hK1 hM1 (mul_nonneg hc1 h_Db_nn) h_net_prod1_b_nn
      h_net_prod1_b_le h_perturbation1_b
    unfold splitFunctionCont splitFunctionProdFloor
    linarith [h0.1, h1.1]
  have h_floor_prox := concave_floor_L_optimal
    (splitFunctionCont K0 M0 c0 K1 M1 c1 D) L b_star hL h_lipschitz h_max
  have h_prod_floor_ge : splitFunctionProdFloor K0 M0 net_prod0_star K1 M1 net_prod1_star >
      splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ -
      (K0 / M0 + K1 / M1 + 2) := by
    linarith [h_floor_err_bstar]
  have h_max_b : splitFunctionCont K0 M0 c0 K1 M1 c1 D b ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star := h_max b
  linarith [h_prod_floor_ge, h_floor_prox, h_max_b, h_floor_le_b]

/-- **Production certified-anchor argmax distance** under ceiling-fee
    perturbation.

    Assume an anchor `anchor` is in the production candidate set, `b_arg` is a
    production argmax or any point whose production value dominates the anchor,
    and the clean continuous objective is strongly concave with parameter `m`.
    If the anchor has clean continuous loss at most `alpha`, then the production
    argmax lies within

    `sqrt(2 * (alpha + (K0/M0 + K1/M1 + 2)) / m)`

    of the clean continuous maximizer `b_star`.

    The exact certificate is tighter when the anchor's actual production value
    is known: use `abstract_certified_anchor_argmax_distance` with
    `tau = f_cont(b_star) - f_prod(anchor)`. This theorem packages the
    universal gross-spot ceiling-fee envelope for production CPMM arithmetic. -/
theorem cpmm_prod_certified_anchor_argmax_distance
    (K0 M0 c0 K1 M1 c1 D alpha m b_star anchor b_arg : ℝ)
    (net_prod0_anchor net_prod1_anchor net_prod0_arg net_prod1_arg : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0)
    (h_anchor_nn : 0 ≤ anchor) (h_anchor_le_D : anchor ≤ D)
    (h_arg_nn : 0 ≤ b_arg) (h_arg_le_D : b_arg ≤ D)
    (h_net_prod0_anchor_nn : net_prod0_anchor ≥ 0)
    (h_net_prod1_anchor_nn : net_prod1_anchor ≥ 0)
    (h_net_prod0_arg_nn : net_prod0_arg ≥ 0)
    (h_net_prod1_arg_nn : net_prod1_arg ≥ 0)
    (h_net_prod0_anchor_le : net_prod0_anchor ≤ c0 * anchor)
    (h_net_prod1_anchor_le : net_prod1_anchor ≤ c1 * (D - anchor))
    (h_net_prod0_arg_le : net_prod0_arg ≤ c0 * b_arg)
    (h_net_prod1_arg_le : net_prod1_arg ≤ c1 * (D - b_arg))
    (h_perturbation0_anchor : c0 * anchor - net_prod0_anchor < 1)
    (h_perturbation1_anchor : c1 * (D - anchor) - net_prod1_anchor < 1)
    (h_perturbation0_arg : c0 * b_arg - net_prod0_arg < 1)
    (h_perturbation1_arg : c1 * (D - b_arg) - net_prod1_arg < 1)
    (_halpha : alpha ≥ 0) (hm : m > 0)
    (h_anchor_loss :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
      splitFunctionCont K0 M0 c0 K1 M1 c1 D anchor ≤ alpha)
    (h_argmax :
      splitFunctionProdFloor K0 M0 net_prod0_anchor K1 M1 net_prod1_anchor ≤
      splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤
      Real.sqrt (2 * (alpha + (K0 / M0 + K1 / M1 + 2)) / m) := by
  set eta : ℝ := K0 / M0 + K1 / M1 + 2
  have hD_nn : 0 ≤ D := le_of_lt hD
  have h_anchor_err := split_prod_floor_error_bound
    K0 M0 c0 K1 M1 c1 D anchor net_prod0_anchor net_prod1_anchor
    hK0 hM0 hc0 hK1 hM1 hc1
    h_anchor_nn hD_nn h_anchor_le_D
    h_net_prod0_anchor_nn h_net_prod1_anchor_nn
    h_net_prod0_anchor_le h_net_prod1_anchor_le
    h_perturbation0_anchor h_perturbation1_anchor
  have h_arg_err := split_prod_floor_error_bound
    K0 M0 c0 K1 M1 c1 D b_arg net_prod0_arg net_prod1_arg
    hK0 hM0 hc0 hK1 hM1 hc1
    h_arg_nn hD_nn h_arg_le_D
    h_net_prod0_arg_nn h_net_prod1_arg_nn
    h_net_prod0_arg_le h_net_prod1_arg_le
    h_perturbation0_arg h_perturbation1_arg
  have h_prod_arg_le_cont :
      splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_arg := by
    linarith [h_arg_err.1]
  have h_anchor_total_loss :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
      splitFunctionProdFloor K0 M0 net_prod0_anchor K1 M1 net_prod1_anchor ≤
      alpha + eta := by
    linarith [h_anchor_loss, h_anchor_err.2]
  have h_sc := h_strong_concave b_arg
  have h_key : (m / 2) * (b_arg - b_star)^2 ≤ alpha + eta := by
    linarith [h_anchor_total_loss, h_prod_arg_le_cont, h_argmax, h_sc]
  have h_cross : (b_arg - b_star)^2 * m ≤ 2 * (alpha + eta) := by
    have h_2m : 2 * (m / 2 : ℝ) = m := by field_simp
    nlinarith [h_key, hm, h_2m]
  have h_sq_le : (b_arg - b_star)^2 ≤ 2 * (alpha + eta) / m := by
    rw [le_div_iff₀ hm]
    linarith [h_cross]
  have h_abs_sq : |b_arg - b_star|^2 = (b_arg - b_star)^2 :=
    sq_abs (b_arg - b_star)
  have h_abs_nn : 0 ≤ |b_arg - b_star| := abs_nonneg (b_arg - b_star)
  have h_abs_eq_sqrt : |b_arg - b_star| = Real.sqrt (|b_arg - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  have h_bound : |b_arg - b_star| ≤ Real.sqrt (2 * (alpha + eta) / m) := by
    rw [h_abs_eq_sqrt, h_abs_sq]
    exact Real.sqrt_le_sqrt h_sq_le
  simpa [eta] using h_bound

/-! ## Part 5b: Oracle-Tight Production Argmax Distance -/

/-- **Production oracle argmax distance** under ceiling-fee perturbation.

    If the production value at the perturbed argmax is known (or bounded
    below), no anchor slack is needed. Strong concavity and the one-sided
    floor relation `prodFloor(b_arg) ≤ cont(b_arg)` give the exact
    certificate:

    `|b_arg - b_star| ≤ sqrt(2 * (cont(b_star) - prodFloor(b_arg)) / m)`

    This is strictly tighter than the anchor-based theorem when the
    production value at the argmax exceeds the production value at the
    anchor. For a finite candidate set, the oracle value is `max prodFloor`;
    a practical checker substitutes any certified lower bound on it. -/
theorem cpmm_prod_oracle_argmax_distance
    (K0 M0 c0 K1 M1 c1 D m b_star b_arg : ℝ)
    (net_prod0_arg net_prod1_arg : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0)
    (h_arg_nn : 0 ≤ b_arg) (h_arg_le_D : b_arg ≤ D)
    (h_net_prod0_arg_nn : net_prod0_arg ≥ 0)
    (h_net_prod1_arg_nn : net_prod1_arg ≥ 0)
    (h_net_prod0_arg_le : net_prod0_arg ≤ c0 * b_arg)
    (h_net_prod1_arg_le : net_prod1_arg ≤ c1 * (D - b_arg))
    (h_perturbation0_arg : c0 * b_arg - net_prod0_arg < 1)
    (h_perturbation1_arg : c1 * (D - b_arg) - net_prod1_arg < 1)
    (hm : m > 0)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤
      Real.sqrt (2 * (splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg) / m) := by
  have hD_nn : 0 ≤ D := le_of_lt hD
  have h_arg_err := split_prod_floor_error_bound
    K0 M0 c0 K1 M1 c1 D b_arg net_prod0_arg net_prod1_arg
    hK0 hM0 hc0 hK1 hM1 hc1
    h_arg_nn hD_nn h_arg_le_D
    h_net_prod0_arg_nn h_net_prod1_arg_nn
    h_net_prod0_arg_le h_net_prod1_arg_le
    h_perturbation0_arg h_perturbation1_arg
  have h_prod_arg_le_cont :
      splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_arg := by
    linarith [h_arg_err.1]
  exact abstract_oracle_perturbed_argmax_distance
    (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
    (fun _ : ℝ => splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg)
    m b_star b_arg hm h_prod_arg_le_cont h_strong_concave

/-! ## Part 5c: Anchored Lipschitz-Perturbation Production Radius -/

/-- **Production anchored Lipschitz-perturbation argmax distance**.

    This theorem packages the production ceiling-fee split values into the
    generic anchored-pair certificate from `DiscreteArgmaxProximity.lean`.
    It applies when the continuous maximizer `b_star` need not be a production
    candidate. A host checker supplies:

    * a production anchor `anchor`,
    * a production candidate `b_arg` whose value dominates that anchor,
    * clean anchor loss `alpha`,
    * anchor distance budget `rho`,
    * pairwise perturbation variation budget `L_e`, and
    * a radius `R` satisfying the quadratic certificate obligations.

    The checker can compute the smallest admissible `R` as the larger root of
    `alpha + L_e * (R + rho) <= (m/2) * R^2`, with `L_e <= m*R`.
    This result is a certificate consumer; it does not search for the argmax,
    derive `m`, or prove the ceiling-fee net-input arithmetic. -/
theorem cpmm_prod_anchor_lipschitz_argmax_distance
    (K0 M0 c0 K1 M1 c1 D m L_e alpha rho R b_star anchor b_arg : ℝ)
    (net_prod0_anchor net_prod1_anchor net_prod0_arg net_prod1_arg : ℝ)
    (hm : m > 0) (hLe : L_e ≥ 0) (halpha : alpha ≥ 0)
    (hrho : rho ≥ 0) (hR : R ≥ 0)
    (h_anchor_loss :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
      splitFunctionCont K0 M0 c0 K1 M1 c1 D anchor ≤ alpha)
    (h_anchor_distance : |anchor - b_star| ≤ rho)
    (h_argmax :
      splitFunctionProdFloor K0 M0 net_prod0_anchor K1 M1 net_prod1_anchor ≤
      splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg)
    (h_perturbation_pair :
      (splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg -
        splitFunctionCont K0 M0 c0 K1 M1 c1 D b_arg) -
      (splitFunctionProdFloor K0 M0 net_prod0_anchor K1 M1 net_prod1_anchor -
        splitFunctionCont K0 M0 c0 K1 M1 c1 D anchor) ≤
        L_e * |b_arg - anchor|)
    (h_radius_certificate : alpha + L_e * (R + rho) ≤ (m / 2) * R^2)
    (h_root_side : L_e ≤ m * R)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star -
        (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ R := by
  exact abstract_anchor_lipschitz_perturbed_argmax_distance
    (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
    m L_e alpha rho R b_star anchor b_arg
    (splitFunctionProdFloor K0 M0 net_prod0_anchor K1 M1 net_prod1_anchor)
    (splitFunctionProdFloor K0 M0 net_prod0_arg K1 M1 net_prod1_arg)
    hm hLe halpha hrho hR
    h_anchor_loss h_anchor_distance h_argmax h_perturbation_pair
    h_radius_certificate h_root_side h_strong_concave

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: per-pool error bound is satisfied for a concrete case.
    K=1000, M=1000, net_cont=50, net_prod=49.5 (perturbation = 0.5 < 1). -/
theorem witness_per_pool_error_bound :
    cpmmOutputCont 1000 1000 50 - cpmmOutputProdFloor 1000 1000 49.5 < 1000 / 1000 + 1 := by
  have h := cpmm_prod_floor_error_bound_directed 1000 1000 50 49.5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (49.5 : ℝ) ≤ 50) (by norm_num : (50 : ℝ) - 49.5 < 1)
  exact h.2

/-! ## Part 7: Coupled Lipschitz Bound (max not sum) -/

/-- For non-negative `x, y`, `|x - y| ≤ max x y`. -/
lemma abs_sub_le_max (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x - y| ≤ max x y := by
  by_cases hxy : x ≥ y
  · rw [abs_of_nonneg (by linarith)]
    linarith [le_max_left x y]
  · push_neg at hxy
    rw [abs_of_nonpos (by linarith)]
    linarith [le_max_right x y]

/-- Key lemma: if `a * b ≤ 0` (opposite signs or one is zero), then
    `|a + b| ≤ max |a| |b|`. This is tighter than the triangle inequality
    `|a + b| ≤ |a| + |b|` when the terms partially cancel.

    This is the abstraction compression that replaces the sum bound with the
    max bound for differences of non-negative monotone terms. -/
lemma abs_add_le_max_of_mul_nonpos (a b : ℝ) (h : a * b ≤ 0) :
    |a + b| ≤ max |a| |b| := by
  by_cases hz : a = 0
  · simp [hz, abs_zero]
  by_cases hz2 : b = 0
  · simp [hz2, abs_zero, add_zero]
  have h_ab_ne : a * b ≠ 0 := mul_ne_zero hz hz2
  have h_strict : a * b < 0 := lt_of_le_of_ne h h_ab_ne
  by_cases ha : a > 0
  · have hb : b < 0 := by nlinarith
    rw [show a + b = a - (-b) by ring, abs_of_pos ha, abs_of_neg hb]
    exact abs_sub_le_max a (-b) (le_of_lt ha) (le_of_lt (neg_pos_of_neg hb))
  · push_neg at ha
    have ha' : a < 0 := lt_of_le_of_ne ha hz
    have hb : b > 0 := by nlinarith
    rw [show a + b = b - (-a) by ring, abs_of_neg ha', abs_of_pos hb, max_comm]
    exact abs_sub_le_max b (-a) (le_of_lt hb) (le_of_lt (neg_pos_of_neg ha'))

/-- The CPMM output function is monotone non-decreasing for `K ≥ 0, M > 0`. -/
lemma cpmmOutputCont_monotone (K M x1 x2 : ℝ)
    (hK : K ≥ 0) (hM : M > 0) (hx1 : x1 ≥ 0) (hx2 : x2 ≥ 0)
    (h12 : x1 ≤ x2) :
    cpmmOutputCont K M x1 ≤ cpmmOutputCont K M x2 := by
  have hMx1 : M + x1 > 0 := by nlinarith
  have hMx2 : M + x2 > 0 := by nlinarith
  have h_diff : cpmmOutputCont K M x2 - cpmmOutputCont K M x1 =
    K * M * (x2 - x1) / ((M + x1) * (M + x2)) := by
    unfold cpmmOutputCont; field_simp; ring
  have h_denom_pos : 0 < (M + x1) * (M + x2) := by nlinarith
  have h_KM_nn : 0 ≤ K * M := mul_nonneg hK (le_of_lt hM)
  have h_diff_nn : 0 ≤ x2 - x1 := by linarith
  have h_num_nn : 0 ≤ K * M * (x2 - x1) := mul_nonneg h_KM_nn h_diff_nn
  have h_frac_nn : 0 ≤ K * M * (x2 - x1) / ((M + x1) * (M + x2)) :=
    div_nonneg h_num_nn (le_of_lt h_denom_pos)
  linarith [h_diff, h_frac_nn]

/-- **Coupled Lipschitz Bound**: The split function is Lipschitz with constant
    `L = max(c0*K0/M0, c1*K1/M1)`, which is tighter than the sum `K0/M0 + K1/M1`.

    Key insight: the split difference `F(x) - F(y) = b0 + b1` where
    `b0 = f0(c0*x) - f0(c0*y)` and `b1 = f1(c1*(D-x)) - f1(c1*(D-y))`.
    Since `f0` and `f1` are both increasing, `b0` and `b1` have opposite signs
    (pool 0 increases with the split variable, pool 1 decreases).
    So `|b0 + b1| ≤ max(|b0|, |b1|)` (tighter than `|b0| + |b1|`).

    Non-claims:
    - L is an upper bound, not the exact Lipschitz constant.
    - The exact constant is `max(|f'(0)|, |f'(D)|) ≤ L`. -/
theorem split_lipschitz_coupled
    (K0 M0 c0 K1 M1 c1 D x y : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (_hD : D ≥ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxD : x ≤ D) (hyD : y ≤ D)
    : |splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
       splitFunctionCont K0 M0 c0 K1 M1 c1 D y| ≤
      max (c0 * K0 / M0) (c1 * K1 / M1) * |x - y| := by
  -- Split the difference into pool-0 and pool-1 components
  have h_split_diff :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
      splitFunctionCont K0 M0 c0 K1 M1 c1 D y =
      (cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y)) +
      (cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y))) := by
    unfold splitFunctionCont; ring
  rw [h_split_diff]
  -- The two components have opposite signs (pool 0 increases, pool 1 decreases)
  have h_b0_b1_nonpos :
      (cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y)) *
      (cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y))) ≤ 0 := by
    by_cases hxy : x ≥ y
    · have h_c0xy : c0 * y ≤ c0 * x := mul_le_mul_of_nonneg_left hxy hc0
      have h_b0_nn : 0 ≤ cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y) := by
        have h := cpmmOutputCont_monotone K0 M0 (c0 * y) (c0 * x) hK0 hM0
          (mul_nonneg hc0 hy) (mul_nonneg hc0 hx) h_c0xy
        linarith
      have h_Dx_Dy : D - x ≤ D - y := by linarith
      have h_c1Dx_Dy : c1 * (D - x) ≤ c1 * (D - y) :=
        mul_le_mul_of_nonneg_left h_Dx_Dy hc1
      have h_Dx_nn : 0 ≤ D - x := by nlinarith
      have h_Dy_nn : 0 ≤ D - y := by nlinarith
      have h_b1_np : cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y)) ≤ 0 := by
        have h := cpmmOutputCont_monotone K1 M1 (c1 * (D - x)) (c1 * (D - y)) hK1 hM1
          (mul_nonneg hc1 h_Dx_nn) (mul_nonneg hc1 h_Dy_nn) h_c1Dx_Dy
        linarith
      nlinarith [h_b0_nn, h_b1_np]
    · push_neg at hxy
      have h_c0xy : c0 * x ≤ c0 * y := mul_le_mul_of_nonneg_left (le_of_lt hxy) hc0
      have h_b0_np : cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y) ≤ 0 := by
        have h := cpmmOutputCont_monotone K0 M0 (c0 * x) (c0 * y) hK0 hM0
          (mul_nonneg hc0 hx) (mul_nonneg hc0 hy) h_c0xy
        linarith
      have h_Dy_Dx : D - y ≤ D - x := by linarith
      have h_c1Dy_Dx : c1 * (D - y) ≤ c1 * (D - x) :=
        mul_le_mul_of_nonneg_left h_Dy_Dx hc1
      have h_Dx_nn : 0 ≤ D - x := by nlinarith
      have h_Dy_nn : 0 ≤ D - y := by nlinarith
      have h_b1_nn : 0 ≤ cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y)) := by
        have h := cpmmOutputCont_monotone K1 M1 (c1 * (D - y)) (c1 * (D - x)) hK1 hM1
          (mul_nonneg hc1 h_Dy_nn) (mul_nonneg hc1 h_Dx_nn) h_c1Dy_Dx
        linarith
      nlinarith [h_b0_np, h_b1_nn]
  -- Apply the key lemma: opposite signs give max, not sum
  have h_abs_le_max :=
    abs_add_le_max_of_mul_nonpos
      (cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y))
      (cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y)))
      h_b0_b1_nonpos
  -- Bound each component using per-pool Lipschitz
  have h_abs_nn : 0 ≤ |x - y| := abs_nonneg _
  have h_c0_x_nn : 0 ≤ c0 * x := mul_nonneg hc0 hx
  have h_c0_y_nn : 0 ≤ c0 * y := mul_nonneg hc0 hy
  have h_lip0 := cpmm_output_lipschitz_wrt_net K0 M0 (c0 * x) (c0 * y)
    hK0 hM0 h_c0_x_nn h_c0_y_nn
  have h_abs_c0_diff : |c0 * x - c0 * y| = c0 * |x - y| := by
    rw [show c0 * x - c0 * y = c0 * (x - y) by ring, abs_mul, abs_of_nonneg hc0]
  rw [h_abs_c0_diff] at h_lip0
  have h_Dx_nn : 0 ≤ D - x := by nlinarith
  have h_Dy_nn : 0 ≤ D - y := by nlinarith
  have h_c1_Dx_nn : 0 ≤ c1 * (D - x) := mul_nonneg hc1 h_Dx_nn
  have h_c1_Dy_nn : 0 ≤ c1 * (D - y) := mul_nonneg hc1 h_Dy_nn
  have h_lip1 := cpmm_output_lipschitz_wrt_net K1 M1 (c1 * (D - x)) (c1 * (D - y))
    hK1 hM1 h_c1_Dx_nn h_c1_Dy_nn
  have h_abs_c1_diff : |c1 * (D - x) - c1 * (D - y)| = c1 * |x - y| := by
    rw [show c1 * (D - x) - c1 * (D - y) = c1 * (y - x) by ring, abs_mul,
      abs_of_nonneg hc1, abs_sub_comm]
  rw [h_abs_c1_diff] at h_lip1
  -- Combine: each |bi| <= ci*Ki/Mi * |x-y| <= L * |x-y|
  set L := max (c0 * K0 / M0) (c1 * K1 / M1)
  have h_b0_le : |cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y)| ≤ L * |x - y| := by
    have h_lm : c0 * K0 / M0 ≤ L := le_max_left _ _
    have h_step : (K0 / M0) * (c0 * |x - y|) ≤ L * |x - y| := by
      have h_eq : (K0 / M0) * (c0 * |x - y|) = (c0 * K0 / M0) * |x - y| := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_right h_lm h_abs_nn
    linarith [h_lip0, h_step]
  have h_b1_le : |cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y))| ≤ L * |x - y| := by
    have h_lm : c1 * K1 / M1 ≤ L := le_max_right _ _
    have h_step : (K1 / M1) * (c1 * |x - y|) ≤ L * |x - y| := by
      have h_eq : (K1 / M1) * (c1 * |x - y|) = (c1 * K1 / M1) * |x - y| := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_right h_lm h_abs_nn
    linarith [h_lip1, h_step]
  -- max |b0| |b1| <= L * |x-y| since both are
  have h_max_le : max
      |cpmmOutputCont K0 M0 (c0 * x) - cpmmOutputCont K0 M0 (c0 * y)|
      |cpmmOutputCont K1 M1 (c1 * (D - x)) - cpmmOutputCont K1 M1 (c1 * (D - y))| ≤
      L * |x - y| := max_le h_b0_le h_b1_le
  linarith [h_abs_le_max, h_max_le]

/-- Witness: coupled Lipschitz bound is satisfied and tighter than the sum
    bound for a concrete case. K0=1000, M0=1000, c0=0.99, K1=2000, M1=1000,
    c1=0.99, D=100, x=50, y=49. -/
theorem witness_coupled_lipschitz :
    max (0.99 * 1000 / 1000) (0.99 * 2000 / 1000) * |(50 : ℝ) - 49| ≤
    (1000 / 1000 + 2000 / 1000) * |(50 : ℝ) - 49| ∧
    max (0.99 * 1000 / 1000) (0.99 * 2000 / 1000) * |(50 : ℝ) - 49| < 2 := by
  constructor
  · norm_num
  · norm_num
