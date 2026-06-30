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
7. **Certified-anchor argmax distance**: if a perturbed argmax beats a
   certified anchor whose total value deficit is at most `τ`, every perturbed
   argmax lies within `√(2τ/m)` of `b*`.
8. **Oracle-tight perturbation distance**: if the perturbed argmax value is
   known, the sharp generic radius is `√(2(f_cont(b*) - f_disc(b_arg))/m)`.
9. **One-sided perturbation argmax distance**: if a perturbed objective lies
   below the strongly concave objective with error at most `ε`, and the
   candidate set has an anchor within value loss `α` of the continuous
   optimum, every perturbed argmax lies within `√(2(α+ε)/m)` of `b*`.
10. **Sharpness witness**: a quadratic strongly-concave objective attains the
    `√(2(α+ε)/m)` radius under the abstract one-sided hypotheses, so this
    generic constant cannot be improved without stronger assumptions.
11. **Anchorless negative result**: without an anchor/lower-value premise, even
    a two-point candidate set has no finite generic argmax-distance bound.

## Argmax Corollary (PROVEN)

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
v8 kernel) has two empirical lanes in
`docs/research/discrete_argmax_proximity_test.py`: the older effective-`L`
`2L + 2` / `3L + 2` lane is retained as a low-fee regression, and a high-fee
falsifier prevents promoting that effective-`L` fee bound as universal. The
universal ceiling-fee perturbation lane uses gross spot `R_out/R_in` because
fee-ceil changes net input by less than one unit and the output curve is
gross-spot Lipschitz in net input.
The tight generic location theorem is `√(2τ/m)`, where
`τ = f_cont(b*) - f_prod(anchor)` is the certified anchor value deficit. The
common ceiling-fee corollary sets `τ <= α + ε`, where `α` is the candidate-set
anchor loss and `ε` is the one-sided production perturbation size. For an
integer grid with nearest-integer anchoring, `α` can be bounded separately; for
a candidate set containing `b*`, `α = 0`.

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

/-- **Certified-anchor argmax distance**.

    This is the sharpest generic certificate form for a chosen anchor:

    `τ = f_cont(b_star) - f_disc(anchor)`

    If `b_arg` is at least as good as `anchor` under the one-sided perturbed
    objective, and the perturbed objective never exceeds the continuous
    objective at `b_arg`, then strong concavity forces:

    `|b_arg - b_star| ≤ √(2τ/m)`.

    Minimizing `τ` over the certified candidate set gives the tightest radius
    available from this information. The `α + ε` theorem below is the standard
    ceiling-fee instantiation when only an anchor loss and perturbation envelope
    are available. -/
theorem abstract_certified_anchor_argmax_distance
    (f_cont f_disc : ℝ → ℝ) (τ m : ℝ) (b_star anchor b_arg : ℝ)
    (_hτ : τ ≥ 0) (hm : m > 0)
    (h_anchor_total_loss : f_cont b_star - f_disc anchor ≤ τ)
    (h_disc_le_arg : f_disc b_arg ≤ f_cont b_arg)
    (h_argmax : f_disc anchor ≤ f_disc b_arg)
    (h_strong_concave : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ Real.sqrt (2 * τ / m) := by
  have h_sc := h_strong_concave b_arg
  have h_key : (m / 2) * (b_arg - b_star)^2 ≤ τ := by
    linarith [h_anchor_total_loss, h_disc_le_arg, h_argmax, h_sc]
  have h_cross : (b_arg - b_star)^2 * m ≤ 2 * τ := by
    have h_2m : 2 * (m / 2 : ℝ) = m := by field_simp
    nlinarith [h_key, hm, h_2m]
  have h_sq_le : (b_arg - b_star)^2 ≤ 2 * τ / m := by
    rw [le_div_iff₀ hm]
    linarith [h_cross]
  have h_abs_sq : |b_arg - b_star|^2 = (b_arg - b_star)^2 := sq_abs (b_arg - b_star)
  have h_abs_nn : 0 ≤ |b_arg - b_star| := abs_nonneg (b_arg - b_star)
  have h_abs_eq_sqrt : |b_arg - b_star| = Real.sqrt (|b_arg - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_abs_sq]
  exact Real.sqrt_le_sqrt h_sq_le

/-- **Oracle-tight one-sided perturbation distance**.

    If the value of the perturbed argmax itself is known, no anchor slack is
    needed. Strong concavity and the one-sided relation `f_disc b_arg <=
    f_cont b_arg` give the exact generic certificate:

    `|b_arg - b_star| <= sqrt(2 * (f_cont b_star - f_disc b_arg) / m)`.

    For a finite candidate set, the oracle value is `max f_disc`. A practical
    checker can replace it with any certified anchor value, which gives the
    `abstract_certified_anchor_argmax_distance` theorem above. -/
theorem abstract_oracle_perturbed_argmax_distance
    (f_cont f_disc : ℝ → ℝ) (m : ℝ) (b_star b_arg : ℝ)
    (hm : m > 0)
    (h_disc_le_arg : f_disc b_arg ≤ f_cont b_arg)
    (h_strong_concave : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤
      Real.sqrt (2 * (f_cont b_star - f_disc b_arg) / m) := by
  have h_sc := h_strong_concave b_arg
  have h_sq_nn : 0 ≤ (b_arg - b_star)^2 := sq_nonneg (b_arg - b_star)
  have h_drop_nn : 0 ≤ (m / 2) * (b_arg - b_star)^2 := by
    have hm2 : 0 ≤ m / 2 := by nlinarith
    exact mul_nonneg hm2 h_sq_nn
  have hτ : f_cont b_star - f_disc b_arg ≥ 0 := by
    linarith [h_disc_le_arg, h_sc, h_drop_nn]
  exact abstract_certified_anchor_argmax_distance
    f_cont f_disc (f_cont b_star - f_disc b_arg) m b_star b_arg b_arg
    hτ hm le_rfl h_disc_le_arg le_rfl h_strong_concave

/-- **Tight one-sided perturbation argmax distance**.

    Let `f_cont` be strongly concave with maximizer `b_star`. Let `f_disc` be a
    one-sided downward perturbation of `f_cont` on the candidate set: at the
    chosen anchor, `f_cont anchor - f_disc anchor ≤ ε`, and at the perturbed
    argmax, `f_disc b_arg ≤ f_cont b_arg`. If `b_arg` maximizes `f_disc` over
    the candidate set and the anchor has continuous value loss at most `α`, then

    `|b_arg - b_star| ≤ √(2(α + ε) / m)`.

    This is the tight generic constant for one-sided perturbations. If the
    candidate set contains `b_star`, take `anchor = b_star` and `α = 0`. For an
    integer grid, `α` is the value lost by the best certified grid anchor near
    `b_star`; bounding `α` is a separate lattice/rounding obligation. -/
theorem abstract_one_sided_perturbed_argmax_distance
    (f_cont f_disc : ℝ → ℝ) (α ε m : ℝ) (b_star anchor b_arg : ℝ)
    (_hα : α ≥ 0) (_hε : ε ≥ 0) (hm : m > 0)
    (h_anchor_loss : f_cont b_star - f_cont anchor ≤ α)
    (h_disc_err_anchor : f_cont anchor - f_disc anchor ≤ ε)
    (h_disc_le_arg : f_disc b_arg ≤ f_cont b_arg)
    (h_argmax : f_disc anchor ≤ f_disc b_arg)
    (h_strong_concave : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ Real.sqrt (2 * (α + ε) / m) := by
  have h_sc := h_strong_concave b_arg
  have h_key : (m / 2) * (b_arg - b_star)^2 ≤ α + ε := by
    linarith [h_anchor_loss, h_disc_err_anchor, h_disc_le_arg, h_argmax, h_sc]
  have h_cross : (b_arg - b_star)^2 * m ≤ 2 * (α + ε) := by
    have h_2m : 2 * (m / 2 : ℝ) = m := by field_simp
    nlinarith [h_key, hm, h_2m]
  have h_sq_le : (b_arg - b_star)^2 ≤ 2 * (α + ε) / m := by
    rw [le_div_iff₀ hm]
    linarith [h_cross]
  have h_abs_sq : |b_arg - b_star|^2 = (b_arg - b_star)^2 := sq_abs (b_arg - b_star)
  have h_abs_nn : 0 ≤ |b_arg - b_star| := abs_nonneg (b_arg - b_star)
  have h_abs_eq_sqrt : |b_arg - b_star| = Real.sqrt (|b_arg - b_star|^2) := by
    rw [Real.sqrt_sq h_abs_nn]
  rw [h_abs_eq_sqrt, h_abs_sq]
  exact Real.sqrt_le_sqrt h_sq_le

/-- **Exact-anchor perturbation distance**.

    If the candidate set contains the continuous maximizer itself, the anchor
    loss is `α = 0`. A one-sided perturbation envelope at `b_star` then gives
    the tight generic ceiling-fee radius:

    `|b_arg - b_star| ≤ sqrt(2*epsilon/m)`.

    For integer grids this corollary usually cannot be used directly because
    `b_star` need not be a candidate. In that case the caller must supply an
    anchor loss `alpha` or an oracle value. -/
theorem abstract_exact_anchor_perturbed_argmax_distance
    (f_cont f_disc : ℝ → ℝ) (ε m : ℝ) (b_star b_arg : ℝ)
    (hε : ε ≥ 0) (hm : m > 0)
    (h_disc_err_at_bstar : f_cont b_star - f_disc b_star ≤ ε)
    (h_disc_le_arg : f_disc b_arg ≤ f_cont b_arg)
    (h_argmax : f_disc b_star ≤ f_disc b_arg)
    (h_strong_concave : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ Real.sqrt (2 * ε / m) := by
  have hα : (0 : ℝ) ≥ 0 := by norm_num
  have h_anchor_loss : f_cont b_star - f_cont b_star ≤ (0 : ℝ) := by linarith
  have h_bound := abstract_one_sided_perturbed_argmax_distance
    f_cont f_disc 0 ε m b_star b_star b_arg hα hε hm
    h_anchor_loss h_disc_err_at_bstar h_disc_le_arg h_argmax h_strong_concave
  simpa [zero_add] using h_bound

/-- **Lipschitz-perturbation argmax movement bound**.

    This is the theorem-search/prior-art companion to the value-deficit
    radius above. Let `f_cont` have quadratic growth from its maximizer
    `b_star` with parameter `m`, and let `e` be the perturbation term at the
    two candidate points. If the perturbed value at `b_arg` is at least the
    perturbed value at `b_star`, and the perturbation advantage is bounded by
    `L_e * |b_arg - b_star|`, then

    `|b_arg - b_star| <= 2 * L_e / m`.

    The factor `2` matches this file's convention
    `f(x) <= f(b*) - (m/2)*(x-b*)^2`. It is a candidate-set/pairwise theorem:
    a full candidate-set argmax may instantiate `h_pert_arg_ge_star` because
    `b_star` is one candidate, while a checker must still provide the
    perturbation-variation certificate for the selected pair. -/
theorem abstract_lipschitz_pair_perturbed_argmax_distance
    (f_cont e : ℝ → ℝ) (L_e m : ℝ) (b_star b_arg : ℝ)
    (hLe : L_e ≥ 0) (hm : m > 0)
    (h_pert_arg_ge_star : f_cont b_star + e b_star ≤ f_cont b_arg + e b_arg)
    (h_perturbation_pair : e b_arg - e b_star ≤ L_e * |b_arg - b_star|)
    (h_quadratic_growth : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ 2 * L_e / m := by
  have h_bound_nonneg : 0 ≤ 2 * L_e / m := by
    exact div_nonneg (mul_nonneg (by norm_num) hLe) (le_of_lt hm)
  by_cases hzero : |b_arg - b_star| = 0
  · simpa [hzero] using h_bound_nonneg
  · have hd_nonneg : 0 ≤ |b_arg - b_star| := abs_nonneg (b_arg - b_star)
    have hd_pos : 0 < |b_arg - b_star| := lt_of_le_of_ne hd_nonneg (Ne.symm hzero)
    have h_sc := h_quadratic_growth b_arg
    have h_loss_lower :
        (m / 2) * (b_arg - b_star)^2 ≤ f_cont b_star - f_cont b_arg := by
      linarith
    have h_loss_upper :
        f_cont b_star - f_cont b_arg ≤ e b_arg - e b_star := by
      linarith [h_pert_arg_ge_star]
    have h_key :
        (m / 2) * |b_arg - b_star|^2 ≤ L_e * |b_arg - b_star| := by
      rw [sq_abs]
      linarith [h_loss_lower, h_loss_upper, h_perturbation_pair]
    have h_mul : |b_arg - b_star| * m ≤ 2 * L_e := by
      nlinarith [h_key, hd_pos]
    rw [le_div_iff₀ hm]
    exact h_mul

/-- Full pairwise Lipschitz form of
    `abstract_lipschitz_pair_perturbed_argmax_distance`. -/
theorem abstract_lipschitz_pair_perturbed_argmax_distance_of_abs
    (f_cont e : ℝ → ℝ) (L_e m : ℝ) (b_star b_arg : ℝ)
    (hLe : L_e ≥ 0) (hm : m > 0)
    (h_pert_arg_ge_star : f_cont b_star + e b_star ≤ f_cont b_arg + e b_arg)
    (h_perturbation_abs : |e b_arg - e b_star| ≤ L_e * |b_arg - b_star|)
    (h_quadratic_growth : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ 2 * L_e / m := by
  have h_pair : e b_arg - e b_star ≤ L_e * |b_arg - b_star| := by
    exact le_trans (le_abs_self (e b_arg - e b_star)) h_perturbation_abs
  exact abstract_lipschitz_pair_perturbed_argmax_distance
    f_cont e L_e m b_star b_arg hLe hm
    h_pert_arg_ge_star h_pair h_quadratic_growth

/-- **Anchored pairwise perturbation argmax distance**.

    This theorem is the production-candidate bridge for integer or otherwise
    restricted candidate sets where the continuous maximizer `b_star` is not
    itself a perturbed-objective candidate. A checker supplies:

    * an anchor candidate `anchor`,
    * a clean anchor loss `alpha >= f(b*) - f(anchor)`,
    * an anchor distance `rho >= |anchor - b*|`,
    * a pairwise perturbation-variation budget `L_e`, and
    * a radius `R` that solves the quadratic certificate obligations.

    If the perturbed value at `b_arg` dominates the anchor, and the pairwise
    perturbation advantage from `anchor` to `b_arg` is bounded by
    `L_e * |b_arg - anchor|`, then `|b_arg - b_star| <= R`.

    The two radius-side obligations are intentionally explicit:

    `alpha + L_e * (R + rho) <= (m/2) * R^2`
    `L_e <= m * R`

    A verifier can compute the smallest nonnegative such `R` as the larger root
    of the quadratic. Lean consumes the checked certificate rather than trusting
    the formula or any caller-supplied radius. -/
theorem abstract_anchor_lipschitz_perturbed_argmax_distance
    (f_cont : ℝ → ℝ)
    (m L_e alpha rho R b_star anchor b_arg g_anchor g_arg : ℝ)
    (hm : m > 0) (hLe : L_e ≥ 0) (_halpha : alpha ≥ 0)
    (_hrho : rho ≥ 0) (_hR : R ≥ 0)
    (h_anchor_loss : f_cont b_star - f_cont anchor ≤ alpha)
    (h_anchor_distance : |anchor - b_star| ≤ rho)
    (h_pert_arg_ge_anchor : g_anchor ≤ g_arg)
    (h_perturbation_pair :
      (g_arg - f_cont b_arg) - (g_anchor - f_cont anchor) ≤
        L_e * |b_arg - anchor|)
    (h_radius_certificate : alpha + L_e * (R + rho) ≤ (m / 2) * R^2)
    (h_root_side : L_e ≤ m * R)
    (h_quadratic_growth : ∀ x : ℝ,
      f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2)
    : |b_arg - b_star| ≤ R := by
  set r : ℝ := |b_arg - b_star|
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact abs_nonneg _
  have h_sc := h_quadratic_growth b_arg
  have h_loss_lower :
      (m / 2) * r^2 ≤ f_cont b_star - f_cont b_arg := by
    dsimp [r]
    rw [sq_abs]
    linarith
  have h_anchor_to_arg :
      f_cont anchor - f_cont b_arg ≤
        (g_arg - f_cont b_arg) - (g_anchor - f_cont anchor) := by
    linarith [h_pert_arg_ge_anchor]
  have h_pair_distance :
      |b_arg - anchor| ≤ r + rho := by
    have h_tri :
        |b_arg - anchor| ≤ |b_arg - b_star| + |anchor - b_star| := by
      calc
        |b_arg - anchor| = |(b_arg - b_star) + (b_star - anchor)| := by ring_nf
        _ ≤ |b_arg - b_star| + |b_star - anchor| := abs_add_le _ _
        _ = |b_arg - b_star| + |anchor - b_star| := by rw [abs_sub_comm b_star anchor]
    dsimp [r]
    linarith
  have h_pair_scaled :
      L_e * |b_arg - anchor| ≤ L_e * (r + rho) := by
    exact mul_le_mul_of_nonneg_left h_pair_distance hLe
  have h_loss_upper :
      f_cont b_star - f_cont b_arg ≤ alpha + L_e * (r + rho) := by
    linarith [h_anchor_loss, h_anchor_to_arg, h_perturbation_pair, h_pair_scaled]
  have h_key : (m / 2) * r^2 ≤ alpha + L_e * (r + rho) := by
    linarith [h_loss_lower, h_loss_upper]
  by_contra h_not
  have hR_lt_r : R < r := lt_of_not_ge h_not
  have h_diff_le : (m / 2) * (r^2 - R^2) ≤ L_e * (r - R) := by
    nlinarith [h_key, h_radius_certificate]
  have h_delta_nonneg : 0 ≤ r - R := by linarith
  have h_linear_le : L_e * (r - R) ≤ (m * R) * (r - R) := by
    exact mul_le_mul_of_nonneg_right h_root_side h_delta_nonneg
  have h_chain : (m / 2) * (r^2 - R^2) ≤ (m * R) * (r - R) :=
    le_trans h_diff_le h_linear_le
  have h_strict : (m * R) * (r - R) < (m / 2) * (r^2 - R^2) := by
    have h_delta_pos : 0 < r - R := by linarith
    have h_delta_sq_pos : 0 < (r - R)^2 := sq_pos_of_ne_zero (by linarith)
    have h_m_half_pos : 0 < m / 2 := by nlinarith
    have h_gap_pos : 0 < (m / 2) * (r - R)^2 :=
      mul_pos h_m_half_pos h_delta_sq_pos
    have h_gap_identity :
        (m / 2) * (r^2 - R^2) - (m * R) * (r - R) =
          (m / 2) * (r - R)^2 := by
      ring
    nlinarith [h_gap_pos, h_gap_identity]
  linarith

/-- **Sharpness witness for the pairwise Lipschitz perturbation radius**.

    For every `L_e >= 0` and `m > 0`, the quadratic objective
    `f(x) = -(m/2)*x^2` and linear perturbation `e(x) = L_e*x` make the
    candidate `b_arg = 2*L_e/m` tie the original maximizer `0` under the
    perturbed objective. The perturbation variation exactly equals
    `L_e * |b_arg|`, and the distance exactly equals `2*L_e/m`.

    This shows the generic pairwise theorem cannot improve the constant from
    these hypotheses alone. A smaller constant needs more structure, such as
    a stronger global optimality premise, smooth first-order conditions, or a
    tighter perturbation certificate. -/
theorem abstract_lipschitz_pair_perturbed_argmax_distance_sharp_quadratic
    (L_e m : ℝ) (hLe : L_e ≥ 0) (hm : m > 0) :
    let b_arg : ℝ := 2 * L_e / m
    let f_cont : ℝ → ℝ := fun x => - (m / 2) * x^2
    let e : ℝ → ℝ := fun x => L_e * x
    |b_arg - 0| = 2 * L_e / m ∧
      f_cont 0 + e 0 = f_cont b_arg + e b_arg ∧
      e b_arg - e 0 = L_e * |b_arg - 0| ∧
      (∀ x : ℝ, f_cont x ≤ f_cont 0 - (m / 2) * (x - 0)^2) := by
  dsimp
  have h_bound_nonneg : 0 ≤ 2 * L_e / m := by
    exact div_nonneg (mul_nonneg (by norm_num) hLe) (le_of_lt hm)
  constructor
  · rw [sub_zero]
    exact abs_of_nonneg h_bound_nonneg
  constructor
  · field_simp [ne_of_gt hm]
    ring
  constructor
  · rw [sub_zero, abs_of_nonneg h_bound_nonneg]
    ring
  · intro x
    ring_nf
    exact le_rfl

/-- **Closed-form additive radius for the anchored Lipschitz bound**.

    The certificate-parametric theorem
    `abstract_anchor_lipschitz_perturbed_argmax_distance` consumes a checked
    radius `R` satisfying two obligations. This corollary proves that the
    explicit additive form
    `R = rho + 2*L_e/m + sqrt(2*alpha/m)`
    satisfies both obligations, giving a closed-form radius that a checker
    can compute without solving a quadratic.

    The additive form is conservative relative to the tightest certified
    radius (the larger root of the quadratic), but it is simple to compute
    and verify. -/
theorem abstract_anchor_lipschitz_additive_radius_certificate
    (m L_e alpha rho : ℝ)
    (hm : m > 0) (hLe : L_e ≥ 0) (halpha : alpha ≥ 0) (hrho : rho ≥ 0) :
    let R : ℝ := rho + 2 * L_e / m + Real.sqrt (2 * alpha / m)
    alpha + L_e * (R + rho) ≤ (m / 2) * R^2 ∧ L_e ≤ m * R := by
  dsimp
  set s : ℝ := 2 * L_e / m
  set t : ℝ := Real.sqrt (2 * alpha / m)
  have hs_nn : 0 ≤ s := div_nonneg (mul_nonneg (by norm_num) hLe) (le_of_lt hm)
  have ht_nn : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = 2 * alpha / m := by
    have h_arg_nn : 0 ≤ 2 * alpha / m :=
      div_nonneg (mul_nonneg (by norm_num) halpha) (le_of_lt hm)
    exact Real.sq_sqrt h_arg_nn
  have h_ms_eq : m * s = 2 * L_e := by
    show m * (2 * L_e / m) = 2 * L_e
    field_simp [ne_of_gt hm]
  have h_ms_sq : (m / 2) * s ^ 2 = L_e * s := by
    show (m / 2) * (2 * L_e / m) ^ 2 = L_e * (2 * L_e / m)
    field_simp [ne_of_gt hm]
  have h_half_t_sq : (m / 2) * t ^ 2 = alpha := by
    show (m / 2) * Real.sqrt (2 * alpha / m) ^ 2 = alpha
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) halpha) (le_of_lt hm))]
    field_simp [ne_of_gt hm]
  -- Obligation 2: L_e <= m * R
  have h_obl2 : L_e ≤ m * (rho + s + t) := by
    show L_e ≤ m * (rho + 2 * L_e / m + Real.sqrt (2 * alpha / m))
    have h_mrho_nn : 0 ≤ m * rho := mul_nonneg (le_of_lt hm) hrho
    have h_mt_nn : 0 ≤ m * Real.sqrt (2 * alpha / m) :=
      mul_nonneg (le_of_lt hm) (Real.sqrt_nonneg _)
    nlinarith [h_mrho_nn, h_mt_nn]
  -- Obligation 1: alpha + L_e * (R + rho) <= (m/2) * R^2
  -- After expansion: RHS - LHS = (m/2)*rho^2 + m*rho*t + L_e*t >= 0
  have h_obl1 : alpha + L_e * ((rho + s + t) + rho) ≤ (m / 2) * (rho + s + t) ^ 2 := by
    show alpha + L_e * ((rho + 2 * L_e / m + Real.sqrt (2 * alpha / m)) + rho) ≤
          (m / 2) * (rho + 2 * L_e / m + Real.sqrt (2 * alpha / m)) ^ 2
    set t2 := Real.sqrt (2 * alpha / m)
    have ht2_sq : t2 ^ 2 = 2 * alpha / m := by
      exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) halpha) (le_of_lt hm))
    have ht2_nn : 0 ≤ t2 := Real.sqrt_nonneg _
    -- Expand and simplify: the difference is (m/2)*rho^2 + m*rho*t2 + L_e*t2
    have h_diff :
        (m / 2) * (rho + 2 * L_e / m + t2) ^ 2 -
        (alpha + L_e * ((rho + 2 * L_e / m + t2) + rho)) =
        (m / 2) * rho ^ 2 + m * rho * t2 + L_e * t2 := by
      field_simp [ne_of_gt hm]
      ring_nf
      rw [ht2_sq]
      field_simp [ne_of_gt hm]
      ring
    have h_diff_nn : 0 ≤ (m / 2) * rho ^ 2 + m * rho * t2 + L_e * t2 := by
      have h1 : 0 ≤ (m / 2) * rho ^ 2 := mul_nonneg (by linarith) (sq_nonneg rho)
      have h2 : 0 ≤ m * rho * t2 := mul_nonneg (mul_nonneg (le_of_lt hm) hrho) ht2_nn
      have h3 : 0 ≤ L_e * t2 := mul_nonneg hLe ht2_nn
      linarith
    linarith [h_diff, h_diff_nn]
  exact ⟨h_obl1, h_obl2⟩

private lemma quadratic_loss_at_sqrt_radius
    (m t : ℝ) (hm : m > 0) (ht : t ≥ 0) :
    0 - (-(m / 2) * (Real.sqrt (2 * t / m)) ^ 2) = t := by
  have h_arg_nn : 0 ≤ 2 * t / m := by
    exact div_nonneg (mul_nonneg (by norm_num) ht) (le_of_lt hm)
  have h_sq : (Real.sqrt (2 * t / m)) ^ 2 = 2 * t / m :=
    Real.sq_sqrt h_arg_nn
  calc
    0 - (-(m / 2) * (Real.sqrt (2 * t / m)) ^ 2)
        = (m / 2) * (Real.sqrt (2 * t / m)) ^ 2 := by ring
    _ = (m / 2) * (2 * t / m) := by rw [h_sq]
    _ = t := by
      field_simp [ne_of_gt hm]

/-- **Sharpness witness for the one-sided perturbation radius**.

    The abstract `sqrt(2*(alpha+epsilon)/m)` radius is not an artifact of a
    loose proof. For every nonnegative `alpha`, nonnegative `epsilon`, and
    `m > 0`, the quadratic objective `f(x) = -(m/2)*x^2` with an anchor at
    radius `sqrt(2*alpha/m)` and a dominated perturbed objective value at
    radius `sqrt(2*(alpha+epsilon)/m)` satisfies the one-sided theorem's
    hypotheses and attains the stated radius exactly. Any smaller generic
    radius would reject this valid witness family. -/
theorem abstract_one_sided_perturbed_argmax_distance_sharp_quadratic
    (α ε m : ℝ) (hα : α ≥ 0) (hε : ε ≥ 0) (hm : m > 0) :
    let anchor : ℝ := Real.sqrt (2 * α / m)
    let b_arg : ℝ := Real.sqrt (2 * (α + ε) / m)
    let f_cont : ℝ → ℝ := fun x => - (m / 2) * x^2
    let f_disc : ℝ → ℝ := fun _ => f_cont b_arg
    |b_arg - 0| = Real.sqrt (2 * (α + ε) / m) ∧
      f_cont 0 - f_cont anchor = α ∧
      f_cont anchor - f_disc anchor = ε ∧
      f_disc b_arg ≤ f_cont b_arg ∧
      f_disc anchor ≤ f_disc b_arg ∧
      (∀ x : ℝ, f_cont x ≤ f_cont 0 - (m / 2) * (x - 0)^2) := by
  dsimp
  have h_anchor_loss := quadratic_loss_at_sqrt_radius m α hm hα
  have h_total_nonneg : 0 ≤ α + ε := add_nonneg hα hε
  have h_total_loss := quadratic_loss_at_sqrt_radius m (α + ε) hm h_total_nonneg
  constructor
  · rw [sub_zero]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  constructor
  · simpa using h_anchor_loss
  constructor
  · linarith [h_anchor_loss, h_total_loss]
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  · intro x
    ring_nf
    exact le_rfl

/-- **Sharpness witness for the oracle perturbation radius**.

    The oracle bound `sqrt(2*(f_cont(b_star) - f_disc(b_arg))/m)` is tight.
    For every `m > 0` and `τ ≥ 0`, the quadratic objective `f(x) = -(m/2)*x^2`
    with `f_disc` constant at `f_cont(b_arg)` satisfies the oracle theorem's
    hypotheses and attains the stated radius exactly. Any smaller generic
    radius would reject this valid witness family. -/
theorem abstract_oracle_perturbed_argmax_distance_sharp_quadratic
    (τ m : ℝ) (hτ : τ ≥ 0) (hm : m > 0) :
    let b_arg : ℝ := Real.sqrt (2 * τ / m)
    let f_cont : ℝ → ℝ := fun x => - (m / 2) * x^2
    let f_disc : ℝ → ℝ := fun _ => f_cont b_arg
    |b_arg - 0| = Real.sqrt (2 * τ / m) ∧
      f_cont 0 - f_disc b_arg = τ ∧
      f_disc b_arg ≤ f_cont b_arg ∧
      (∀ x : ℝ, f_cont x ≤ f_cont 0 - (m / 2) * (x - 0)^2) := by
  dsimp
  have h_total_loss := quadratic_loss_at_sqrt_radius m τ hm hτ
  constructor
  · rw [sub_zero]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  constructor
  · have : -(m / 2) * 0 ^ 2 = 0 := by ring
    linarith [h_total_loss, this]
  constructor
  · exact le_rfl
  · intro x
    ring_nf
    exact le_rfl

/-- **Anchorless candidate-set counterexample**.

    Strong concavity plus the one-sided relation at the chosen argmax does not
    by itself imply any finite location window. For every proposed radius `R`,
    a quadratic strongly-concave objective and a two-point candidate set can
    make a distant point the perturbed argmax by suppressing the value at the
    continuous maximizer. This is the formal reason the certified-anchor,
    oracle-value, or perturbation-lower-bound premise is load-bearing. -/
theorem abstract_anchorless_candidate_argmax_unbounded
    (R m : ℝ) (hR : R ≥ 0) (hm : m > 0) :
    ∃ (f_cont f_disc : ℝ → ℝ) (candidate : ℝ → Prop) (b_star b_arg : ℝ),
      candidate b_star ∧
      candidate b_arg ∧
      R < |b_arg - b_star| ∧
      (∀ x : ℝ, candidate x → f_disc x ≤ f_cont x) ∧
      (∀ x : ℝ, candidate x → f_disc x ≤ f_disc b_arg) ∧
      (∀ x : ℝ, f_cont x ≤ f_cont b_star - (m / 2) * (x - b_star)^2) := by
  let B : ℝ := R + 1
  let f_cont : ℝ → ℝ := fun x => - (m / 2) * x^2
  let f_disc : ℝ → ℝ := fun x => if x = B then f_cont B else f_cont B - 1
  let candidate : ℝ → Prop := fun x => x = 0 ∨ x = B
  have hB_pos : 0 < B := by linarith
  have hB_ne_zero : B ≠ 0 := ne_of_gt hB_pos
  have hzero_ne_B : (0 : ℝ) ≠ B := by exact Ne.symm hB_ne_zero
  have hdist : R < |B - 0| := by
    have h_abs : |B - 0| = B := by
      rw [sub_zero]
      exact abs_of_pos hB_pos
    rw [h_abs]
    linarith
  use f_cont, f_disc, candidate, 0, B
  constructor
  · exact Or.inl rfl
  constructor
  · exact Or.inr rfl
  constructor
  · exact hdist
  constructor
  · intro x hx
    rcases hx with rfl | rfl
    · dsimp [f_disc, f_cont]
      simp [hzero_ne_B]
      nlinarith [hm, sq_nonneg B]
    · dsimp [f_disc]
      simp
  constructor
  · intro x hx
    rcases hx with rfl | rfl
    · dsimp [f_disc]
      simp [hzero_ne_B]
    · dsimp [f_disc]
      simp
  · intro x
    dsimp [f_cont]
    ring_nf
    exact le_rfl

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
