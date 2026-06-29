/-
# Discrete Argmax Proximity for CPMM Split Function

This file proves that the discrete (floor-rounded) CPMM split function's value
at the floor of the continuous maximizer is near-optimal, and that any discrete
point STRICTLY beating it must lie within a bounded window of the continuous
maximizer (under a strong-concavity hypothesis).

## Reformulation of Phase 3A

The literal Phase 3A hypothesis ("discrete CPMM split is concave") is FALSE:
floor rounding creates staircase plateaus that break discrete concavity
(empirically verified in `docs/research/cpmm_split_concavity_test.py`).

The CORRECT theorem is: the discrete split function evaluated at `⌊b*_cont⌋`
achieves at least `(L + ε)` of the discrete optimum, where `L` is the Lipschitz
constant (max spot price) and `ε` is the total floor rounding error bound
(`ε = 2` for the 2-pool split, since each pool contributes `< 1` unit of error).

## Theorem Chain (Proven Here)

1. **Floor rounding error (single pool)**: `0 ≤ cont - floor < 1`
2. **Floor rounding error (2-pool split)**: `0 ≤ cont - floor < 2`
3. **Abstract near-optimality**: `floor(⌊b*⌋) ≥ floor(b) - (L + ε)` for all `b`
4. **CPMM near-optimality**: `splitFloor(⌊b*⌋) ≥ splitFloor(b) - (L + 2)`
5. **Abstract window sufficiency (strict-beat)**: if `floor(b) > floor(⌊b*⌋)`
   then `|b - b*| < √(2(L + ε) / m)` (requires strong concavity parameter `m`
   as an EXTERNAL hypothesis)
6. **CPMM window sufficiency (strict-beat)**: if a discrete point strictly
   beats `floor(⌊b*⌋)`, then `|b - b*| < √(2(L + 2) / m)`

## Argmax Corollary (Theorem 7, PROVEN)

The window sufficiency theorems (5, 6) cover points that STRICTLY beat
`floor(⌊b*⌋)`. The argmax window corollary (`argmax_window_corollary`
below) extends this to the actual integer argmax `n*`, covering both
cases:

- **Strict-beat case**: if `floor(n*) > floor(⌊b*⌋)`, Theorem 6 gives
  `|n* - b*| < √(2(L+2)/m)`.
- **Tie case**: if `floor(n*) = floor(⌊b*⌋)` (plateau), strong concavity
  + floor-error chain gives the same bound `(m/2)(n*-b*)² < L + 2`, hence
  `|n* - b*| < √(2(L+2)/m)`.

The combined bound is `|n* - b*| ≤ max(1, √(2(L+2)/m))`, which holds
universally. The `max(1, …)` accounts for the strict-beat case where the
window could be < 1 (large `m`), using the trivial floor-proximity
bound `< 1` as a fallback.

## External Hypothesis: Strong Concavity Parameter `m`

The strong concavity parameter `m` is taken as an EXTERNAL hypothesis.
It is NOT derived from CPMM structure in this file. For the CPMM split
function, `m` can be lower-bounded by the minimum second derivative
(which is strictly negative from `CpmmSplitConcavity.lean`), but
converting the second-forward-difference negativity into a pointwise
`f(x) ≤ f(b*) - (m/2)(x - b*)²` bound requires additional analysis
not proven here. Production use requires a verified or runtime-certified
`m` lower bound.

## Impact

This is the theorem that underpins the continuous-guided discrete search used
in the ternary search DP. The abstract theorems (3, 5) are unconditional and
reusable. The CPMM-specific theorems (4, 6) are proven for the CLEAN model
(continuous fee + floor output) with `ε = 2`, CONDITIONAL on Lipschitz /
global-max / strong-concavity hypotheses that are NOT discharged here.

The PRODUCTION model (ceiling fee + floor output, matching `src/core/cpmm.py`
v8 kernel) uses `ε = 2L + 2` and a `(3L + 2)` argmax bound; these are verified
empirically in `docs/research/discrete_argmax_proximity_test.py`, not formally
proven in Lean (would require modeling `Int.ceil` for the fee computation).

For balanced pools (`L < 1`), the clean-model gap is at most 3 and the
production-model gap is at most 5, both within integer rounding noise.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/DiscreteArgmaxProximity.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.CpmmSplitConcavity
import Proofs.WindowBound

open Real

/-- The floored CPMM output function, modeling integer arithmetic.
    `cpmmOutputFloor K M x = ⌊K * x / (M + x)⌋` where K = R_out, M = R_in.
    For non-negative integer inputs, this equals the production `swap_exact_in`
    output (floor division). -/
noncomputable def cpmmOutputFloor (K M x : ℝ) : ℝ := ↑⌊K * x / (M + x)⌋

/-- The floored 2-pool split function, modeling the discrete batch clearing
    objective.
    `splitFunctionFloor(a) = floor(cont(K0,M0,c0*a)) + floor(cont(K1,M1,c1*(D-a)))` -/
noncomputable def splitFunctionFloor
    (K0 M0 c0 K1 M1 c1 D a : ℝ) : ℝ :=
  cpmmOutputFloor K0 M0 (c0 * a) + cpmmOutputFloor K1 M1 (c1 * (D - a))

/-- Lemma 1: Floor rounding error for a single CPMM pool.
    For `K ≥ 0`, `x ≥ 0`, `M + x > 0`: `0 ≤ cont - floor < 1`.
    This is immediate from the definition of floor: `⌊z⌋ ≤ z < ⌊z⌋ + 1`. -/
lemma cpmm_floor_error_bound
    (K M x : ℝ) (hK : K ≥ 0) (hx : x ≥ 0) (hMx : M + x > 0)
    : 0 ≤ cpmmOutputCont K M x - cpmmOutputFloor K M x ∧
      cpmmOutputCont K M x - cpmmOutputFloor K M x < 1 := by
  have hKx_nn : 0 ≤ K * x := mul_nonneg hK hx
  have hz_nn : 0 ≤ K * x / (M + x) := div_nonneg hKx_nn (le_of_lt hMx)
  have hfloor_le : (↑⌊K * x / (M + x)⌋ : ℝ) ≤ K * x / (M + x) := Int.floor_le _
  have hfloor_lt : K * x / (M + x) < (↑⌊K * x / (M + x)⌋ : ℝ) + 1 := by
    have := Int.lt_floor_add_one (K * x / (M + x))
    exact_mod_cast this
  constructor
  · unfold cpmmOutputCont cpmmOutputFloor
    linarith
  · unfold cpmmOutputCont cpmmOutputFloor
    linarith

/-- Lemma 2: Floor rounding error for the 2-pool split function.
    For valid parameters: `0 ≤ cont - floor < 2`.
    Each pool contributes `< 1` unit of error, so the sum is `< 2`. -/
lemma split_floor_error_bound
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (hK0 : K0 ≥ 0) (hc0a_nn : c0 * a ≥ 0) (hM0c0a : M0 + c0 * a > 0)
    (hK1 : K1 ≥ 0) (hc1Da_nn : c1 * (D - a) ≥ 0) (hM1c1Da : M1 + c1 * (D - a) > 0)
    : 0 ≤ splitFunctionCont K0 M0 c0 K1 M1 c1 D a - splitFunctionFloor K0 M0 c0 K1 M1 c1 D a ∧
      splitFunctionCont K0 M0 c0 K1 M1 c1 D a - splitFunctionFloor K0 M0 c0 K1 M1 c1 D a < 2 := by
  have h0 := cpmm_floor_error_bound K0 M0 (c0 * a) hK0 hc0a_nn hM0c0a
  have h1 := cpmm_floor_error_bound K1 M1 (c1 * (D - a)) hK1 hc1Da_nn hM1c1Da
  constructor
  · simp only [splitFunctionCont, splitFunctionFloor]
    linarith [h0.1, h1.1]
  · simp only [splitFunctionCont, splitFunctionFloor]
    linarith [h0.2, h1.2]

/-- Lemma 3: The floored split function is bounded above by the continuous split.
    `splitFloor(b) ≤ splitCont(b)` for all valid `b`. -/
lemma split_floor_le_cont
    (K0 M0 c0 K1 M1 c1 D a : ℝ)
    (hK0 : K0 ≥ 0) (hc0a_nn : c0 * a ≥ 0) (hM0c0a : M0 + c0 * a > 0)
    (hK1 : K1 ≥ 0) (hc1Da_nn : c1 * (D - a) ≥ 0) (hM1c1Da : M1 + c1 * (D - a) > 0)
    : splitFunctionFloor K0 M0 c0 K1 M1 c1 D a ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D a := by
  have h := split_floor_error_bound K0 M0 c0 K1 M1 c1 D a
    hK0 hc0a_nn hM0c0a hK1 hc1Da_nn hM1c1Da
  linarith

/-- Helper: `0 ≤ x` implies `0 ≤ ↑⌊x⌋` (floor of a nonneg real is nonneg). -/
lemma floor_nonneg_of_nonneg (x : ℝ) (hx : 0 ≤ x) : (0 : ℝ) ≤ ↑⌊x⌋ := by
  by_contra h_neg
  push_neg at h_neg
  have h_lt_succ : x < ↑⌊x⌋ + 1 := by
    have := Int.lt_floor_add_one x
    exact_mod_cast this
  have h_floor_le_neg1 : (↑⌊x⌋ : ℝ) ≤ -1 := by
    have h_int : (⌊x⌋ : ℤ) < 0 := by exact_mod_cast h_neg
    have : (⌊x⌋ : ℤ) ≤ -1 := by omega
    exact_mod_cast this
  linarith

/-- **Theorem 1 (Abstract)**: Discrete argmax proximity.
    Let `f_cont` be a continuous function and `f_floor` its floored version.
    If `f_cont` is `L`-Lipschitz with global max at `b*`, and the floor error is
    bounded by `ε` (i.e., `f_cont - f_floor < ε`), then:

    `f_floor(⌊b*⌋) ≥ f_floor(b) - (L + ε)` for all `b`.

    This means the continuous-guided discrete search (checking `⌊b*⌋`) achieves
    a value within `(L + ε)` of the discrete optimum.

    **Proof chain**:
    1. `f_floor(⌊b*⌋) > f_cont(⌊b*⌋) - ε`  (floor error at `⌊b*⌋`)
    2. `f_cont(⌊b*⌋) ≥ f_cont(b*) - L`      (floor proximity, from Lipschitz)
    3. `f_cont(b*) ≥ f_cont(b)`              (`b*` is continuous global max)
    4. `f_cont(b) ≥ f_floor(b)`              (floor rounds down)

    Combining: `f_floor(⌊b*⌋) > f_floor(b) - (L + ε)`, hence `≥`. -/
theorem abstract_discrete_argmax_proximity
    (f_cont f_floor : ℝ → ℝ) (L ε : ℝ) (b_star b : ℝ)
    (hL : L ≥ 0)
    (h_floor_err_at_bstar : f_cont ↑⌊b_star⌋ - f_floor ↑⌊b_star⌋ < ε)
    (h_floor_le_at_b : f_floor b ≤ f_cont b)
    (h_lipschitz : ∀ x y : ℝ, |f_cont x - f_cont y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ, f_cont x ≤ f_cont b_star)
    : f_floor ↑⌊b_star⌋ ≥ f_floor b - (L + ε) := by
  have h_floor_prox := concave_floor_L_optimal f_cont L b_star hL h_lipschitz h_max
  linarith [h_floor_err_at_bstar, h_floor_le_at_b, h_floor_prox, h_max b]

/-- **Theorem 2 (CPMM)**: Discrete argmax proximity for the CPMM 2-pool split.
    The floored split function at `⌊b*⌋` achieves at least `(L + 2)` of the
    discrete optimum, where `L` is the Lipschitz constant (max spot price).

    This is the theorem that justifies the production ternary search DP:
    the continuous-guided search achieves a provably near-optimal value.

    Parameters:
    - `K0, K1`: pool output reserves (`R_out`) ≥ 0
    - `M0, M1`: pool input reserves (`R_in`) > 0
    - `c0, c1`: effective input coefficients (`1 - fee`) ≥ 0
    - `D`: total input > 0
    - `b_star`: continuous maximizer, `0 ≤ b_star ≤ D`
    - `b`: any evaluation point, `0 ≤ b ≤ D`
    - `L`: Lipschitz constant ≥ 0 (max spot price `= max(c0*K0/M0, c1*K1/M1)`) -/
theorem cpmm_discrete_argmax_proximity
    (K0 M0 c0 K1 M1 c1 D L b_star b : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0) (hb_star_nn : 0 ≤ b_star) (hb_star_le_D : b_star ≤ D)
    (hb_nn : 0 ≤ b) (hb_le_D : b ≤ D)
    (hL : L ≥ 0)
    (h_lipschitz : ∀ x y : ℝ,
      |splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
       splitFunctionCont K0 M0 c0 K1 M1 c1 D y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    : splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ ≥
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D b - (L + 2) := by
  -- Domain non-degeneracy: D > 0 ensures the split interval [0, D] is non-trivial.
  -- This is a contract precondition; the floor-error bounds below depend on it
  -- only indirectly (via the interval being well-defined).
  have hD_pos : D > 0 := hD
  -- Floor of b_star is in [0, D]
  have h_floor_bstar_nn : (0 : ℝ) ≤ ↑⌊b_star⌋ := floor_nonneg_of_nonneg b_star hb_star_nn
  have h_floor_bstar_le_D : (↑⌊b_star⌋ : ℝ) ≤ D := by
    have h_fl : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
    linarith
  -- Floor error at ⌊b_star⌋: cont(⌊b*⌋) - floor(⌊b*⌋) < 2
  have hc0_fbstar_nn : c0 * ↑⌊b_star⌋ ≥ 0 := mul_nonneg hc0 h_floor_bstar_nn
  have hM0c0_fbstar : M0 + c0 * ↑⌊b_star⌋ > 0 := by nlinarith [hM0, hc0_fbstar_nn]
  have hD_fbstar_nn : D - ↑⌊b_star⌋ ≥ 0 := by nlinarith [hD_pos, h_floor_bstar_le_D]
  have hc1D_fbstar_nn : c1 * (D - ↑⌊b_star⌋) ≥ 0 := mul_nonneg hc1 hD_fbstar_nn
  have hM1c1D_fbstar : M1 + c1 * (D - ↑⌊b_star⌋) > 0 := by nlinarith [hM1, hc1D_fbstar_nn]
  have h_floor_err_bstar :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ -
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ < 2 := by
    have h := split_floor_error_bound K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋
      hK0 hc0_fbstar_nn hM0c0_fbstar hK1 hc1D_fbstar_nn hM1c1D_fbstar
    exact h.2
  -- Floor ≤ cont at b: floor(b) ≤ cont(b)
  have hc0b_nn : c0 * b ≥ 0 := mul_nonneg hc0 hb_nn
  have hM0c0b : M0 + c0 * b > 0 := by nlinarith [hM0, hc0b_nn]
  have hDb_nn : D - b ≥ 0 := by nlinarith
  have hc1Db_nn : c1 * (D - b) ≥ 0 := mul_nonneg hc1 hDb_nn
  have hM1c1Db : M1 + c1 * (D - b) > 0 := by nlinarith [hM1, hc1Db_nn]
  have h_floor_le_b :
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D b ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b := by
    exact split_floor_le_cont K0 M0 c0 K1 M1 c1 D b
      hK0 hc0b_nn hM0c0b hK1 hc1Db_nn hM1c1Db
  -- Apply the abstract theorem with ε = 2
  exact abstract_discrete_argmax_proximity
    (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
    (splitFunctionFloor K0 M0 c0 K1 M1 c1 D)
    L 2 b_star b hL h_floor_err_bstar h_floor_le_b h_lipschitz h_max

/-- **Theorem 3 (Abstract)**: Window sufficiency under strong concavity.
    If `f_cont` is `L`-Lipschitz and strongly concave with parameter `m > 0`
    (i.e., `f_cont(b) ≤ f_cont(b*) - (m/2)(b - b*)²`), and the floor error
    is bounded by `ε`, then any discrete point `b` that beats `⌊b*⌋` must lie
    within `√(2(L + ε) / m)` of `b*`.

    This gives the adaptive window formula `W = ⌈√(2(L + ε) / m)⌉ + 1`:
    the discrete argmax is guaranteed to lie within this window of `b*`.

    **Proof**:
    - `f_floor(b) > f_floor(⌊b*⌋)` (assumption: b beats the floor-guided point)
    - `f_floor(b) ≤ f_cont(b) ≤ f_cont(b*) - (m/2)(b - b*)²` (floor + strong concavity)
    - `f_floor(⌊b*⌋) > f_cont(b*) - (L + ε)` (floor error + floor proximity)
    - Combining: `(m/2)(b - b*)² < L + ε`, i.e., `|b - b*| < √(2(L + ε) / m)` -/
theorem abstract_window_sufficiency
    (f_cont f_floor : ℝ → ℝ) (L ε m : ℝ) (b_star b : ℝ)
    (hL : L ≥ 0) (hε : ε > 0) (hm : m > 0)
    (h_floor_err_at_bstar : f_cont ↑⌊b_star⌋ - f_floor ↑⌊b_star⌋ < ε)
    (h_floor_le_at_b : f_floor b ≤ f_cont b)
    (h_lipschitz : ∀ x y : ℝ, |f_cont x - f_cont y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ, f_cont x ≤ f_cont b_star)
    (h_strong_concave : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    (h_disc_better : f_floor b > f_floor ↑⌊b_star⌋)
    : |b - b_star| < Real.sqrt (2 * (L + ε) / m) := by
  have h_floor_prox := concave_floor_L_optimal f_cont L b_star hL h_lipschitz h_max
  have h_sc := h_strong_concave b
  -- Key inequality: (m/2) * (b - b*)² < L + ε
  have h_key : (m / 2) * (b - b_star)^2 < L + ε := by
    linarith [h_sc, h_floor_err_at_bstar, h_floor_le_at_b, h_disc_better, h_floor_prox]
  -- Derive: (b - b*)² < 2*(L+ε)/m
  have h_m_pos : m > 0 := hm
  have h_cross : (b - b_star)^2 * m < 2 * (L + ε) := by
    have h_2m : 2 * (m / 2 : ℝ) = m := by field_simp
    nlinarith [h_key, hm, h_2m]
  have h_sq_lt : (b - b_star)^2 < 2 * (L + ε) / m := by
    rw [lt_div_iff₀ h_m_pos]
    linarith [h_cross]
  -- Convert to |b - b*| < sqrt(2*(L+ε)/m)
  have h_abs_sq : |b - b_star|^2 = (b - b_star)^2 := sq_abs (b - b_star)
  have h_abs_nn : 0 ≤ |b - b_star| := abs_nonneg (b - b_star)
  have h_rhs_nn : 0 ≤ 2 * (L + ε) / m := by
    have h_LE_nn : 0 ≤ L + ε := add_nonneg hL (le_of_lt hε)
    exact div_nonneg (mul_nonneg (by norm_num) h_LE_nn) (le_of_lt hm)
  have h_abs_eq_sqrt : |b - b_star| = Real.sqrt (|b - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_abs_sq]
  exact Real.sqrt_lt_sqrt (sq_nonneg (b - b_star)) h_sq_lt

/-- **Theorem 4 (CPMM)**: Window sufficiency for the CPMM 2-pool split.
    If a discrete point `b` beats the continuous-guided point `⌊b*⌋`, then
    `|b - b*| < √(2(L + 2) / m)`, where `L` is the Lipschitz constant and
    `m` is the strong concavity parameter.

    This gives the production adaptive window formula:
    `W = ⌈√(2(L + 2) / m)⌉ + 1`. -/
theorem cpmm_window_sufficiency
    (K0 M0 c0 K1 M1 c1 D L m b_star b : ℝ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD : D > 0) (hb_star_nn : 0 ≤ b_star) (hb_star_le_D : b_star ≤ D)
    (hb_nn : 0 ≤ b) (hb_le_D : b ≤ D)
    (hL : L ≥ 0) (hm : m > 0)
    (h_lipschitz : ∀ x y : ℝ,
      |splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
       splitFunctionCont K0 M0 c0 K1 M1 c1 D y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - (m / 2) * (x - b_star)^2)
    (h_disc_better :
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D b >
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋)
    : |b - b_star| < Real.sqrt (2 * (L + 2) / m) := by
  -- Domain non-degeneracy (contract precondition; same as Theorem 2).
  have hD_pos : D > 0 := hD
  -- Floor of b_star is in [0, D]
  have h_floor_bstar_nn : (0 : ℝ) ≤ ↑⌊b_star⌋ := floor_nonneg_of_nonneg b_star hb_star_nn
  have h_floor_bstar_le_D : (↑⌊b_star⌋ : ℝ) ≤ D := by
    have h_fl : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
    linarith
  -- Floor error at ⌊b_star⌋
  have hc0_fbstar_nn : c0 * ↑⌊b_star⌋ ≥ 0 := mul_nonneg hc0 h_floor_bstar_nn
  have hM0c0_fbstar : M0 + c0 * ↑⌊b_star⌋ > 0 := by nlinarith [hM0, hc0_fbstar_nn]
  have hD_fbstar_nn : D - ↑⌊b_star⌋ ≥ 0 := by nlinarith [hD_pos, h_floor_bstar_le_D]
  have hc1D_fbstar_nn : c1 * (D - ↑⌊b_star⌋) ≥ 0 := mul_nonneg hc1 hD_fbstar_nn
  have hM1c1D_fbstar : M1 + c1 * (D - ↑⌊b_star⌋) > 0 := by nlinarith [hM1, hc1D_fbstar_nn]
  have h_floor_err_bstar :
      splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ -
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ < 2 := by
    have h := split_floor_error_bound K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋
      hK0 hc0_fbstar_nn hM0c0_fbstar hK1 hc1D_fbstar_nn hM1c1D_fbstar
    exact h.2
  -- Floor ≤ cont at b
  have hc0b_nn : c0 * b ≥ 0 := mul_nonneg hc0 hb_nn
  have hM0c0b : M0 + c0 * b > 0 := by nlinarith [hM0, hc0b_nn]
  have hDb_nn : D - b ≥ 0 := by nlinarith
  have hc1Db_nn : c1 * (D - b) ≥ 0 := mul_nonneg hc1 hDb_nn
  have hM1c1Db : M1 + c1 * (D - b) > 0 := by nlinarith [hM1, hc1Db_nn]
  have h_floor_le_b :
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D b ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b := by
    exact split_floor_le_cont K0 M0 c0 K1 M1 c1 D b
      hK0 hc0b_nn hM0c0b hK1 hc1Db_nn hM1c1Db
  -- Apply abstract window sufficiency with ε = 2
  exact abstract_window_sufficiency
    (splitFunctionCont K0 M0 c0 K1 M1 c1 D)
    (splitFunctionFloor K0 M0 c0 K1 M1 c1 D)
    L 2 m b_star b hL (by norm_num : (2 : ℝ) > 0) hm
    h_floor_err_bstar h_floor_le_b h_lipschitz h_max h_strong_concave h_disc_better

/-- **Argmax Window Corollary**: For the integer argmax `n*` of the floored
    CPMM split function (domain-restricted to `0 ≤ n ≤ D`), the distance to
    `b*` is bounded by `max(1, √(2(L+2)/m))`.

    This handles both cases:
    - If `n*` strictly beats `⌊b*⌋` in floor value, the window theorem gives
      `|n* - b*| < √(2(L+2)/m)`.
    - If `n*` does not strictly beat `⌊b*⌋` (tie/equal floor value), the
      strong-concavity plus floor-error chain gives the same bound
      `(m/2)(n*-b*)² < L + 2`, hence `|n* - b*| < √(2(L+2)/m)`.

    The combined bound `max(1, √(2(L+2)/m))` covers both cases universally:
    the `max(1, …)` handles the large-`m` regime where the window could be
    `< 1`, using the trivial floor-proximity bound `< 1` as a fallback.

    **Note**: The strong concavity parameter `m` is an EXTERNAL hypothesis.
    It is not derived from CPMM structure here. See file header for details. -/
theorem argmax_window_corollary
    (K0 M0 c0 K1 M1 c1 D L m b_star : ℝ) (n_star : ℤ)
    (hK0 : K0 ≥ 0) (hM0 : M0 > 0) (hc0 : c0 ≥ 0)
    (hK1 : K1 ≥ 0) (hM1 : M1 > 0) (hc1 : c1 ≥ 0)
    (hD_pos : D > 0) (hb_star_nn : 0 ≤ b_star) (hb_star_le_D : b_star ≤ D)
    (hL : L ≥ 0) (hm : m > 0)
    (h_lipschitz : ∀ x y : ℝ,
      |splitFunctionCont K0 M0 c0 K1 M1 c1 D x -
       splitFunctionCont K0 M0 c0 K1 M1 c1 D y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star)
    (h_strong_concave : ∀ x : ℝ,
      splitFunctionCont K0 M0 c0 K1 M1 c1 D x ≤
      splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - (m / 2) * (x - b_star)^2)
    (h_nstar_max : ∀ n : ℤ, (0 : ℝ) ≤ ↑n → (↑n : ℝ) ≤ D →
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n ≤
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star)
    (h_nstar_nn : (0 : ℝ) ≤ ↑n_star)
    (h_nstar_le_D : (↑n_star : ℝ) ≤ D)
    : ↑n_star - b_star ≤ max 1 (Real.sqrt (2 * (L + 2) / m)) ∧
      b_star - ↑n_star ≤ max 1 (Real.sqrt (2 * (L + 2) / m)) := by
  -- The argmax n* either strictly beats ⌊b*⌋ or doesn't.
  by_cases h_strict : splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star >
                     splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋
  · -- Strict beat: apply the window sufficiency theorem
    have h_window : |(↑n_star : ℝ) - b_star| < Real.sqrt (2 * (L + 2) / m) := by
      apply cpmm_window_sufficiency K0 M0 c0 K1 M1 c1 D L m b_star ↑n_star
        hK0 hM0 hc0 hK1 hM1 hc1 hD_pos hb_star_nn hb_star_le_D
        h_nstar_nn h_nstar_le_D hL hm h_lipschitz h_max h_strong_concave
      exact h_strict
    -- |n* - b*| < sqrt ≤ max(1, sqrt)
    have h_sqrt_le_max : Real.sqrt (2 * (L + 2) / m) ≤ max 1 (Real.sqrt (2 * (L + 2) / m)) :=
      le_max_right _ _
    have h_abs_lt_max : |(↑n_star : ℝ) - b_star| < max 1 (Real.sqrt (2 * (L + 2) / m)) :=
      lt_of_lt_of_le h_window h_sqrt_le_max
    have h_le1 : ↑n_star - b_star ≤ |(↑n_star : ℝ) - b_star| := le_abs_self _
    have h_le2 : b_star - ↑n_star ≤ |(↑n_star : ℝ) - b_star| := by
      have h_neg : b_star - ↑n_star = -((↑n_star : ℝ) - b_star) := by ring
      have h_le : -((↑n_star : ℝ) - b_star) ≤ |((↑n_star : ℝ) - b_star)| := by
        have := le_abs_self (-((↑n_star : ℝ) - b_star))
        rwa [abs_neg] at this
      rw [h_neg]; exact h_le
    constructor
    · exact le_of_lt (lt_of_le_of_lt h_le1 h_abs_lt_max)
    · exact le_of_lt (lt_of_le_of_lt h_le2 h_abs_lt_max)
  · -- Not strict: floor(n*) ≤ floor(⌊b*⌋).
    -- Since n* is the argmax, floor(n*) ≥ floor(⌊b*⌋) (⌊b*⌋ is an integer).
    -- So floor(n*) = floor(⌊b*⌋).
    -- The trivial bound gives |n* - b*| ≤ |n* - ⌊b*⌋| + 1.
    -- We show |n* - b*| ≤ max(1, sqrt) using:
    -- |n* - b*| < |n* - ⌊b*⌋| + 1, and we need this ≤ max(1, sqrt).
    -- This requires |n* - ⌊b*⌋| + 1 ≤ max(1, sqrt), which is NOT always true
    -- for plateau argmax far from ⌊b*⌋.
    --
    -- However, for the CPMM function with strong concavity, plateaus are
    -- bounded: the function value drops by at least (m/2)*d² away from b*,
    -- so a plateau can't extend more than sqrt(2*(L+2)/m) from b*.
    -- A point n* with floor(n*) = floor(⌊b*⌋) that is far from ⌊b*⌋
    -- would need f_cont(n*) ≈ f_cont(⌊b*⌋), but strong concavity gives
    -- f_cont(n*) ≤ f_cont(b*) - (m/2)*(n*-b*)², while
    -- f_cont(⌊b*⌋) ≥ f_cont(b*) - L (floor proximity).
    -- So (m/2)*(n*-b*)² ≤ L + 2 (the floor error), giving
    -- |n*-b*| ≤ sqrt(2*(L+2)/m) = the window bound.
    --
    -- Formalize this:
    have h_nstar_le_floor_bstar : splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star ≤
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ := by
      push_neg at h_strict
      exact h_strict
    have h_eq : splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star =
      splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ := by
      -- Domain proofs for ⌊b_star⌋: 0 ≤ ⌊b_star⌋ and ⌊b_star⌋ ≤ D
      have h_fb_nn : (0 : ℝ) ≤ ↑⌊b_star⌋ := floor_nonneg_of_nonneg b_star hb_star_nn
      have h_fb_le_D : (↑⌊b_star⌋ : ℝ) ≤ D := by
        have h_fl : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
        linarith
      have h_ge := h_nstar_max ⌊b_star⌋ h_fb_nn h_fb_le_D
      have h_le := h_nstar_le_floor_bstar
      linarith
    -- Use strong concavity to bound |n* - b*|
    -- f_cont(n*) ≤ f_cont(b*) - (m/2)*(n*-b*)²
    -- f_cont(⌊b*⌋) ≥ f_cont(b*) - L (floor proximity)
    -- f_floor(n*) = f_floor(⌊b*⌋) (from h_eq)
    -- f_cont(n*) - f_floor(n*) < 2 (floor error at n*)
    -- f_cont(⌊b*⌋) - f_floor(⌊b*⌋) < 2 (floor error at ⌊b*⌋)
    -- So f_cont(n*) < f_floor(n*) + 2 = f_floor(⌊b*⌋) + 2 ≤ f_cont(⌊b*⌋) + 2
    -- And f_cont(⌊b*⌋) ≤ f_cont(b*) + 0 (max property, actually ≤)
    -- Combining with strong concavity:
    -- f_cont(b*) - (m/2)*(n*-b*)² ≤ f_cont(n*) < f_cont(⌊b*⌋) + 2 ≤ f_cont(b*) + 2
    -- So (m/2)*(n*-b*)² > -2, which gives |n*-b*|² < 4/m... wait that's wrong.
    -- Let me redo:
    -- f_cont(n*) ≤ f_cont(b*) - (m/2)*(n*-b*)²  (strong concavity)
    -- f_cont(⌊b*⌋) ≥ f_cont(b*) - L  (floor proximity via Lipschitz)
    -- f_floor(n*) ≤ f_cont(n*)  (floor rounds down)
    -- f_floor(⌊b*⌋) ≤ f_cont(⌊b*⌋)  (floor rounds down)
    -- f_floor(n*) = f_floor(⌊b*⌋)  (from h_eq)
    -- Also: f_cont(⌊b*⌋) - f_floor(⌊b*⌋) < 2  (floor error)
    -- So: f_cont(⌊b*⌋) < f_floor(⌊b*⌋) + 2 = f_floor(n*) + 2 ≤ f_cont(n*) + 2
    -- And: f_cont(n*) ≤ f_cont(b*) - (m/2)*(n*-b*)²
    -- So: f_cont(⌊b*⌋) < f_cont(b*) - (m/2)*(n*-b*)² + 2
    -- And: f_cont(⌊b*⌋) ≥ f_cont(b*) - L
    -- So: f_cont(b*) - L < f_cont(b*) - (m/2)*(n*-b*)² + 2
    -- -L < -(m/2)*(n*-b*)² + 2
    -- (m/2)*(n*-b*)² < L + 2
    -- (n*-b*)² < 2*(L+2)/m
    -- |n*-b*| < sqrt(2*(L+2)/m)
    --
    -- We need the floor error at n* and at ⌊b*⌋, and the floor proximity.
    -- Floor proximity at ⌊b*⌋:
    have h_floor_prox := concave_floor_L_optimal
      (splitFunctionCont K0 M0 c0 K1 M1 c1 D) L b_star hL h_lipschitz h_max
    -- Floor error at ⌊b*⌋:
    have h_floor_bstar_nn : (0 : ℝ) ≤ ↑⌊b_star⌋ := floor_nonneg_of_nonneg b_star hb_star_nn
    have h_floor_bstar_le_D : (↑⌊b_star⌋ : ℝ) ≤ D := by
      have h_fl : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
      linarith
    have hc0_fbstar_nn : c0 * ↑⌊b_star⌋ ≥ 0 := mul_nonneg hc0 h_floor_bstar_nn
    have hM0c0_fbstar : M0 + c0 * ↑⌊b_star⌋ > 0 := by nlinarith [hM0, hc0_fbstar_nn]
    have hD_fbstar_nn : D - ↑⌊b_star⌋ ≥ 0 := by nlinarith [hD_pos, h_floor_bstar_le_D]
    have hc1D_fbstar_nn : c1 * (D - ↑⌊b_star⌋) ≥ 0 := mul_nonneg hc1 hD_fbstar_nn
    have hM1c1D_fbstar : M1 + c1 * (D - ↑⌊b_star⌋) > 0 := by nlinarith [hM1, hc1D_fbstar_nn]
    have h_floor_err_bstar :
        splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ -
        splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ < 2 := by
      have h := split_floor_error_bound K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋
        hK0 hc0_fbstar_nn hM0c0_fbstar hK1 hc1D_fbstar_nn hM1c1D_fbstar
      exact h.2
    -- Floor ≤ cont at n*:
    have hc0n_nn : c0 * ↑n_star ≥ 0 := mul_nonneg hc0 h_nstar_nn
    have hM0c0n : M0 + c0 * ↑n_star > 0 := by nlinarith [hM0, hc0n_nn]
    have hDn_nn : D - ↑n_star ≥ 0 := by nlinarith [hD_pos, h_nstar_le_D]
    have hc1Dn_nn : c1 * (D - ↑n_star) ≥ 0 := mul_nonneg hc1 hDn_nn
    have hM1c1Dn : M1 + c1 * (D - ↑n_star) > 0 := by nlinarith [hM1, hc1Dn_nn]
    have h_floor_le_nstar :
        splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star ≤
        splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑n_star := by
      exact split_floor_le_cont K0 M0 c0 K1 M1 c1 D ↑n_star
        hK0 hc0n_nn hM0c0n hK1 hc1Dn_nn hM1c1Dn
    -- Strong concavity at n*:
    have h_sc_nstar := h_strong_concave ↑n_star
    -- Chain: f_cont(⌊b*⌋) < f_floor(⌊b*⌋) + 2 = f_floor(n*) + 2 ≤ f_cont(n*) + 2
    -- ≤ f_cont(b*) - (m/2)*(n*-b*)² + 2
    -- And f_cont(⌊b*⌋) ≥ f_cont(b*) - L
    -- So: f_cont(b*) - L < f_cont(b*) - (m/2)*(n*-b*)² + 2
    -- (m/2)*(n*-b*)² < L + 2
    have h_key : (m / 2) * ((↑n_star : ℝ) - b_star)^2 < L + 2 := by
      have h1 : splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ <
                 splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ + 2 := by
        linarith
      rw [← h_eq] at h1
      have h2 : splitFunctionFloor K0 M0 c0 K1 M1 c1 D ↑n_star ≤
                 splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑n_star := h_floor_le_nstar
      have h3 : splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑n_star ≤
                 splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - (m / 2) * ((↑n_star : ℝ) - b_star)^2 := h_sc_nstar
      have h4 : splitFunctionCont K0 M0 c0 K1 M1 c1 D ↑⌊b_star⌋ ≥
                 splitFunctionCont K0 M0 c0 K1 M1 c1 D b_star - L := h_floor_prox
      linarith
    -- (m/2)*(n*-b*)² < L+2  ⟹  (n*-b*)² < 2*(L+2)/m  ⟹  |n*-b*| < sqrt(2*(L+2)/m)
    have h_m_pos : m > 0 := hm
    have h_cross : ((↑n_star : ℝ) - b_star)^2 * m < 2 * (L + 2) := by
      have h_2m : 2 * (m / 2 : ℝ) = m := by field_simp
      nlinarith [h_key, hm, h_2m]
    have h_sq_lt : ((↑n_star : ℝ) - b_star)^2 < 2 * (L + 2) / m := by
      rw [lt_div_iff₀ h_m_pos]
      linarith [h_cross]
    have h_abs_sq : |(↑n_star : ℝ) - b_star|^2 = ((↑n_star : ℝ) - b_star)^2 := sq_abs _
    have h_abs_nn : 0 ≤ |(↑n_star : ℝ) - b_star| := abs_nonneg _
    have h_rhs_nn : 0 ≤ 2 * (L + 2) / m := by
      have h_LE_nn : 0 ≤ L + 2 := add_nonneg hL (by norm_num)
      exact div_nonneg (mul_nonneg (by norm_num) h_LE_nn) (le_of_lt hm)
    have h_abs_eq_sqrt : |(↑n_star : ℝ) - b_star| = Real.sqrt (|(↑n_star : ℝ) - b_star|^2) := by
      rw [Real.sqrt_sq h_abs_nn]
    -- Convert h_sq_lt to use |n*-b*|^2 instead of (n*-b*)^2
    have h_abs_sq_lt : |(↑n_star : ℝ) - b_star|^2 < 2 * (L + 2) / m := by
      rw [h_abs_sq]; exact h_sq_lt
    have h_abs_lt_sqrt : |(↑n_star : ℝ) - b_star| < Real.sqrt (2 * (L + 2) / m) := by
      rw [h_abs_eq_sqrt]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) h_abs_sq_lt
    -- |n* - b*| < sqrt ≤ max(1, sqrt)
    have h_sqrt_le_max : Real.sqrt (2 * (L + 2) / m) ≤ max 1 (Real.sqrt (2 * (L + 2) / m)) :=
      le_max_right _ _
    have h_abs_lt_max : |(↑n_star : ℝ) - b_star| < max 1 (Real.sqrt (2 * (L + 2) / m)) :=
      lt_of_lt_of_le h_abs_lt_sqrt h_sqrt_le_max
    have h_le1 : ↑n_star - b_star ≤ |(↑n_star : ℝ) - b_star| := le_abs_self _
    have h_le2 : b_star - ↑n_star ≤ |(↑n_star : ℝ) - b_star| := by
      have h_neg : b_star - ↑n_star = -((↑n_star : ℝ) - b_star) := by ring
      have h_le : -((↑n_star : ℝ) - b_star) ≤ |((↑n_star : ℝ) - b_star)| := by
        have := le_abs_self (-((↑n_star : ℝ) - b_star))
        rwa [abs_neg] at this
      rw [h_neg]; exact h_le
    constructor
    · exact le_of_lt (lt_of_le_of_lt h_le1 h_abs_lt_max)
    · exact le_of_lt (lt_of_le_of_lt h_le2 h_abs_lt_max)
