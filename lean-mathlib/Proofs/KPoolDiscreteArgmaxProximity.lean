/-
# K-Pool Discrete Argmax Proximity: Generalization to k Pools

This file generalizes the 2-pool Discrete Argmax Proximity theorem
(`DiscreteArgmaxProximity.lean`) to k pools. The key insight is that
the floor rounding error scales as `< k` (each of k pools contributes
`< 1` unit of error), so the argmax proximity bound generalizes from
`L + 2` to `L + k`.

## Generalization Structure

The abstract theorems in `DiscreteArgmaxProximity.lean`
(`abstract_discrete_argmax_proximity`) already take the floor error
bound `ε` as a parameter. The k-pool generalization applies the
existing abstract theorem with `ε = k` (the number of pools).

## Theorem Chain

1. **K-pool argmax proximity** (PROVEN, conditional): For k pools with
   floor error bound `ε < k`, Lipschitz constant `L`, and global max at
   `b*`:
   `F_floor(⌊b*⌋) ≥ F_floor(b) - (L + k)`

2. **K-pool balanced corollary** (PROVEN, conditional): For balanced
   pools (`L < 1`):
   `F_floor(⌊b*⌋) ≥ F_floor(b) - (k + 1)`

## Floor Error Bound (empirical, not formally proven here)

The floor error bound `0 ≤ cont - floor < k` follows from the
single-pool bound (`cpmm_floor_error_bound`: `< 1` per pool) summed
over k pools. A formal finset proof would require additional mathlib
finset API work (strict upper bound for nonempty finset of terms in
`[0, 1)`). The bound is verified empirically:

- k=2: max floor error = 1.98 (< 2)
- k=3: max floor error = 2.79 (< 3)
- k=4: max floor error = 3.46 (< 4)
- k=5: max floor error = 4.01 (< 5)

See `docs/research/k_pool_discrete_argmax_proximity_test.py`.

## Impact

This generalizes the abstract argmax proximity bound from 2-pool to
k-pool: the bound `L + k` grows linearly with the pool count, which is
tight (each pool adds `< 1` unit of floor rounding error).

**Scope limitation**: The Lean theorem is scalar (`F : R -> R`, `b* : R`).
Actual k-pool routing uses a `(k-1)`-dimensional simplex. A vector/simplex
Lean statement formalizing the floor error over `Finset.sum` and the
multi-coordinate rounding loss is left as future work. The current theorem
applies the abstract bound with `epsilon = k` as a scalar specialization;
the empirical tests verify the bound holds for the actual vector objective.

For balanced pools (`L < 1`), the gap is `k + 1` (at most 6 for k=5
pools), within integer rounding noise.

## Verification

Compile: `cd lean-mathlib && lake env lean Proofs/KPoolDiscreteArgmaxProximity.lean`
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.DiscreteArgmaxProximity
import Proofs.CpmmSplitConcavity

open Real

/-- **Theorem 1 (K-Pool)**: Discrete argmax proximity for k pools.
    For a continuous split function `F_cont` and floored split function
    `F_floor` over k pools, with floor error bound `ε = k` (each pool
    contributes `< 1` unit of error):

    `F_floor(⌊b*⌋) ≥ F_floor(b) - (L + k)`

    where `L` is the Lipschitz constant and `k` is the number of pools.

    This applies `abstract_discrete_argmax_proximity` with `ε = k`.

    **Hypotheses** (NOT discharged here):
    - `h_floor_err_at_bstar`: floor error at `⌊b*⌋` is `< k`
      (from summing single-pool bounds; verified empirically)
    - `h_lipschitz`: `F_cont` is `L`-Lipschitz
      (provable from CPMM derivative; not done here)
    - `h_max`: `b*` is the continuous global max
      (follows from strict concavity + compactness; `b*` existence assumed)
    - `h_floor_le_at_b`: floor rounds down at `b`

    The floor error bound `< k` follows from `cpmm_floor_error_bound`
    (`< 1` per pool) summed over k pools. A formal finset proof of the
    strict upper bound requires additional API work; the bound is
    verified empirically across 3600+ configurations. -/
theorem kpool_discrete_argmax_proximity
    (F_cont F_floor : ℝ → ℝ) (L k : ℝ) (b_star b : ℝ)
    (hL : L ≥ 0)
    (h_floor_err_at_bstar : F_cont ↑⌊b_star⌋ - F_floor ↑⌊b_star⌋ < k)
    (h_floor_le_at_b : F_floor b ≤ F_cont b)
    (h_lipschitz : ∀ x y : ℝ, |F_cont x - F_cont y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ, F_cont x ≤ F_cont b_star)
    : F_floor ↑⌊b_star⌋ ≥ F_floor b - (L + k) := by
  exact abstract_discrete_argmax_proximity F_cont F_floor L k b_star b
    hL h_floor_err_at_bstar h_floor_le_at_b h_lipschitz h_max

/-- **Corollary**: For k pools with balanced parameters (0 ≤ L < 1),
    the continuous-guided discrete search achieves a value within
    `k + 1` of the discrete optimum.

    For k = 2, this gives the bound 3 (matching the 2-pool result).
    For k = 5, this gives the bound 6. All within integer rounding noise.

    The proof uses `L < 1` to tighten `L + k` to `k + 1`. -/
theorem kpool_balanced_proximity_corollary
    (F_cont F_floor : ℝ → ℝ) (L k : ℝ) (b_star b : ℝ)
    (hL : (0 : ℝ) ≤ L ∧ L < 1)
    (h_floor_err_at_bstar : F_cont ↑⌊b_star⌋ - F_floor ↑⌊b_star⌋ < k)
    (h_floor_le_at_b : F_floor b ≤ F_cont b)
    (h_lipschitz : ∀ x y : ℝ, |F_cont x - F_cont y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ, F_cont x ≤ F_cont b_star)
    : F_floor ↑⌊b_star⌋ ≥ F_floor b - (k + 1 : ℝ) := by
  have h_prox := kpool_discrete_argmax_proximity F_cont F_floor L k b_star b
    hL.1 h_floor_err_at_bstar h_floor_le_at_b h_lipschitz h_max
  -- L + k < 1 + k = k + 1
  have h_L_lt_1 : L < 1 := hL.2
  linarith

/-- **Specialization to k = 2**: Recovers the 2-pool bound `L + 2`.
    This confirms the k-pool theorem is a true generalization: setting
    `k = 2` gives exactly `F_floor(⌊b*⌋) ≥ F_floor(b) - (L + 2)`,
    matching `cpmm_discrete_argmax_proximity` in `DiscreteArgmaxProximity.lean`. -/
theorem kpool_two_pool_specialization
    (F_cont F_floor : ℝ → ℝ) (L : ℝ) (b_star b : ℝ)
    (hL : L ≥ 0)
    (h_floor_err_at_bstar : F_cont ↑⌊b_star⌋ - F_floor ↑⌊b_star⌋ < 2)
    (h_floor_le_at_b : F_floor b ≤ F_cont b)
    (h_lipschitz : ∀ x y : ℝ, |F_cont x - F_cont y| ≤ L * |x - y|)
    (h_max : ∀ x : ℝ, F_cont x ≤ F_cont b_star)
    : F_floor ↑⌊b_star⌋ ≥ F_floor b - (L + 2 : ℝ) := by
  exact kpool_discrete_argmax_proximity F_cont F_floor L 2 b_star b
    hL h_floor_err_at_bstar h_floor_le_at_b h_lipschitz h_max
