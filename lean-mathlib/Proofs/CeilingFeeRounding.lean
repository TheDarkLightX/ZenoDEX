import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.DiscreteArgmaxProximity

/-!
# Ceiling-Fee Rounding: Production Model Bounds

This file formally models the production CPMM swap arithmetic (ceiling fee +
floor output) and proves conservative floor error and argmax proximity bounds.
The proved bounds use `K0/M0 + K1/M1 + 2` and `L + K0/M0 + K1/M1 + 2`, which are
weaker than (but imply) the empirical `2L + 2` and `3L + 2` bounds; the exact
empirical constants are not formally proved here.

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

## Relationship to Empirical Bounds

The empirical bounds use `L = max(c0*K0/M0, c1*K1/M1)` (split Lipschitz) and show
floor error `< 2L + 2` and argmax proximity `< 3L + 2`. The formal bounds here use
`K0/M0 + K1/M1` (per-pool output Lipschitz), which are ≥ `L` (since `c ≤ 1`), so
the formal bounds are WEAKER than the empirical bounds. When `c = 1` (no fee),
the formal bounds would reduce to the clean model bounds, but this specialization
is not formally proved here — the proved theorems state the conservative
`K0/M0 + K1/M1 + 2` and `L + K0/M0 + K1/M1 + 2` bounds for all fee settings.

## Non-Claims

- The ceiling fee perturbation bound (`net_cont - net_prod < 1`) is an EXTERNAL
  hypothesis, not proven in Lean.
- The per-pool Lipschitz constant `K/M` is the worst case (at `x=0`).
- The formal bounds are weaker than the empirical bounds.
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

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: per-pool error bound is satisfied for a concrete case.
    K=1000, M=1000, net_cont=50, net_prod=49.5 (perturbation = 0.5 < 1). -/
theorem witness_per_pool_error_bound :
    cpmmOutputCont 1000 1000 50 - cpmmOutputProdFloor 1000 1000 49.5 < 1000 / 1000 + 1 := by
  have h := cpmm_prod_floor_error_bound_directed 1000 1000 50 49.5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (49.5 : ℝ) ≤ 50) (by norm_num : (50 : ℝ) - 49.5 < 1)
  exact h.2
