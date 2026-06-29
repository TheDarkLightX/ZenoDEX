/-
# K-Pool CPMM Split Function: Coordinate-Wise Negative Second Forward Difference

This file proves that the k-pool CPMM split function has a strictly negative
second forward difference in each coordinate direction, generalizing the
2-pool result from `CpmmSplitConcavity.lean` to 3 pools.

## Key Insight: Separability

The k-pool split function is:
  F(a1, ..., a_{k-1}) = sum_i f_i(c_i * a_i)

where a_k = D - sum_{j<k} a_j (the remainder goes to pool k-1).

The second forward difference in coordinate j is:
  Δ²_j F = F(..., a_j + 2h, ...) - 2*F(..., a_j + h, ...) + F(..., a_j, ...)

By linearity of the second difference:
  Δ²_j F = Δ²f_j(c_j*a_j, c_j*h) + Δ²f_{k-1}(c_{k-1}*(D - sum - 2h), c_{k-1}*h)

Only pool j (increasing input) and pool k-1 (decreasing input) change.
All other pools are unchanged (their Δ² = 0).

Each Δ²f_i < 0 (from `cpmmOutputCont_secondDiff_neg` in CpmmSplitConcavity.lean),
so the sum is strictly negative.

## Backward Difference = Forward Difference

For pool k-1, as a_j increases, the input DECREASES. The second difference is:
  f_{k-1}(x - 2*c*h) - 2*f_{k-1}(x - c*h) + f_{k-1}(x)

This equals the forward difference at (x - 2*c*h) with step c*h:
  f_{k-1}((x-2ch) + 2ch) - 2*f_{k-1}((x-2ch) + ch) + f_{k-1}(x-2ch)

Which is negative by `cpmmOutputCont_secondDiff_neg` with x' = x - 2ch.

## Theorem (3-Pool, Coordinate 1)

F(a1, a2) = f_0(c0*a1) + f_1(c1*a2) + f_2(c2*(D - a1 - a2))

Δ²_1 F = Δ²f_0(c0*a1, c0*h) + Δ²f_2(c2*(D-a1-a2) - 2*c2*h, c2*h) < 0

## Scope and Non-Claims

- This proves coordinate-wise negative second difference for 3 pools
- The k-pool generalization follows by the same separability argument
  (only 2 pools change per coordinate step)
- This does NOT prove joint concavity (Hessian negative definite) directly,
  but coordinate-wise concavity + separability implies joint concavity
- Same continuous-vs-discrete scope as CpmmSplitConcavity.lean

## Verification

Compile: cd lean-mathlib && lake env lean Proofs/KPoolSplitConcavity.lean
Zero errors, zero warnings, zero placeholders.
-/

import Mathlib.Tactic
import Proofs.CpmmSplitConcavity

/-- The 3-pool continuous split function.
    F(a1, a2) = f_0(c0*a1) + f_1(c1*a2) + f_2(c2*(D - a1 - a2))
    where f_i(x) = K_i * x / (M_i + x). -/
noncomputable def splitFunction3PoolCont
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 D a1 a2 : ℝ) : ℝ :=
  cpmmOutputCont K0 M0 (c0 * a1) +
  cpmmOutputCont K1 M1 (c1 * a2) +
  cpmmOutputCont K2 M2 (c2 * (D - a1 - a2))

/-- The second forward difference in coordinate 1 (a1 direction) with step h.
    Δ²_1 F = F(a1+2h, a2) - 2*F(a1+h, a2) + F(a1, a2) -/
def secondDiffCoord1
    (f : ℝ → ℝ → ℝ) (a1 a2 h : ℝ) : ℝ :=
  f (a1 + 2*h) a2 - 2 * f (a1 + h) a2 + f a1 a2

/-- **3-Pool Coordinate 1 Concavity**: The second forward difference of the
    3-pool split function in the a1 direction is strictly negative.

    This follows from separability: only pool 0 (increasing) and pool 2
    (decreasing) change when a1 moves. Pool 1 is unchanged (Δ² = 0).
    Each changing pool's contribution is negative by `cpmmOutputCont_secondDiff_neg`. -/
theorem splitFunction3PoolCont_concave_coord1
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 D a1 a2 h : ℝ)
    (hK0 : K0 > 0) (hM0 : M0 > 0) (hc0 : c0 > 0)
    (_hK1 : K1 > 0) (_hM1 : M1 > 0) (_hc1 : c1 > 0)
    (hK2 : K2 > 0) (hM2 : M2 > 0) (hc2 : c2 > 0)
    (_hD : D > 0) (hh : h > 0)
    (h_denom0 : M0 + c0 * a1 > 0)
    (_h_denom1 : M1 + c1 * a2 > 0)
    (_h_remainder_pos : D - a1 - a2 - 2*h > 0)
    (h_denom2_base : M2 + c2 * (D - a1 - a2 - 2*h) > 0)
    : secondDiffCoord1
      (splitFunction3PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 D) a1 a2 h < 0 := by
  -- Δ²_1 F = Δ²f_0(c0*a1, c0*h) + 0 + Δ²f_2(c2*(D-a1-a2-2h), c2*h)
  --
  -- Pool 0: forward difference at x = c0*a1, step = c0*h
  --   = f_0(c0*(a1+2h)) - 2*f_0(c0*(a1+h)) + f_0(c0*a1)
  --   = secondDiff (cpmmOutputCont K0 M0) (c0*a1) (c0*h) < 0
  --
  -- Pool 1: unchanged (a2 fixed), Δ² = 0
  --
  -- Pool 2: as a1 increases by h, input decreases by c2*h
  --   = f_2(c2*(D-a1-2h-a2)) - 2*f_2(c2*(D-a1-h-a2)) + f_2(c2*(D-a1-a2))
  --   = f_2(x-2*c2*h) - 2*f_2(x-c2*h) + f_2(x)  where x = c2*(D-a1-a2)
  --   = secondDiff (cpmmOutputCont K2 M2) (x - 2*c2*h) (c2*h)  (backward = forward at x-2ch)
  --   < 0 by cpmmOutputCont_secondDiff_neg with x' = x - 2*c2*h

  -- Pool 0 contribution
  have h_pool0 : secondDiff (cpmmOutputCont K0 M0) (c0 * a1) (c0 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK0
    · exact hM0
    · exact mul_pos hc0 hh
    · exact h_denom0

  -- Pool 2 contribution: backward difference = forward difference at (x - 2*c2*h)
  -- x = c2 * (D - a1 - a2), x' = c2 * (D - a1 - a2) - 2 * c2 * h = c2 * (D - a1 - a2 - 2*h)
  let x2 := c2 * (D - a1 - a2 - 2*h)
  have h_pool2 : secondDiff (cpmmOutputCont K2 M2) x2 (c2 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK2
    · exact hM2
    · exact mul_pos hc2 hh
    · exact h_denom2_base

  -- Show the total equals pool0 + pool2 (pool1 = 0)
  -- Δ²_1 F = [f0(a1+2h) - 2*f0(a1+h) + f0(a1)] + [f1(a2) - 2*f1(a2) + f1(a2)] + [f2(...) - 2*f2(...) + f2(...)]
  -- Pool 1 terms cancel: f1(a2) - 2*f1(a2) + f1(a2) = 0
  have h_eq : secondDiff (cpmmOutputCont K0 M0) (c0 * a1) (c0 * h) +
              secondDiff (cpmmOutputCont K2 M2) x2 (c2 * h) =
              secondDiffCoord1 (splitFunction3PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 D) a1 a2 h := by
    unfold secondDiffCoord1 secondDiff splitFunction3PoolCont cpmmOutputCont
    -- Pool 1 terms: cpmmOutputCont K1 M1 (c1 * a2) appears 3 times with coefficients 1, -2, 1
    -- These cancel: 1 - 2 + 1 = 0
    ring

  rw [← h_eq]
  -- Sum of two negative numbers is negative
  have h_sum_neg : secondDiff (cpmmOutputCont K0 M0) (c0 * a1) (c0 * h) +
                   secondDiff (cpmmOutputCont K2 M2) x2 (c2 * h) < 0 := by
    exact add_neg h_pool0 h_pool2
  exact h_sum_neg

/-- The second forward difference in coordinate 2 (a2 direction) with step h.
    Δ²_2 F = F(a1, a2+2h) - 2*F(a1, a2+h) + F(a1, a2) -/
def secondDiffCoord2
    (f : ℝ → ℝ → ℝ) (a1 a2 h : ℝ) : ℝ :=
  f a1 (a2 + 2*h) - 2 * f a1 (a2 + h) + f a1 a2

/-- **3-Pool Coordinate 2 Concavity**: The second forward difference of the
    3-pool split function in the a2 direction is strictly negative.

    By symmetry with coordinate 1: only pool 1 (increasing) and pool 2
    (decreasing) change. Pool 0 is unchanged. -/
theorem splitFunction3PoolCont_concave_coord2
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 D a1 a2 h : ℝ)
    (_hK0 : K0 > 0) (_hM0 : M0 > 0) (_hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (hK2 : K2 > 0) (hM2 : M2 > 0) (hc2 : c2 > 0)
    (_hD : D > 0) (hh : h > 0)
    (_h_denom0 : M0 + c0 * a1 > 0)
    (h_denom1 : M1 + c1 * a2 > 0)
    (_h_remainder_pos : D - a1 - a2 - 2*h > 0)
    (h_denom2_base : M2 + c2 * (D - a1 - a2 - 2*h) > 0)
    : secondDiffCoord2
      (splitFunction3PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 D) a1 a2 h < 0 := by
  -- Pool 1: forward difference at x = c1*a2, step = c1*h
  have h_pool1 : secondDiff (cpmmOutputCont K1 M1) (c1 * a2) (c1 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK1
    · exact hM1
    · exact mul_pos hc1 hh
    · exact h_denom1

  -- Pool 2: backward difference = forward at x' = c2*(D-a1-a2-2h)
  let x2 := c2 * (D - a1 - a2 - 2*h)
  have h_pool2 : secondDiff (cpmmOutputCont K2 M2) x2 (c2 * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hK2
    · exact hM2
    · exact mul_pos hc2 hh
    · exact h_denom2_base

  -- Pool 0 unchanged (a1 fixed), Δ² = 0
  have h_eq : secondDiff (cpmmOutputCont K1 M1) (c1 * a2) (c1 * h) +
              secondDiff (cpmmOutputCont K2 M2) x2 (c2 * h) =
              secondDiffCoord2 (splitFunction3PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 D) a1 a2 h := by
    unfold secondDiffCoord2 secondDiff splitFunction3PoolCont cpmmOutputCont
    ring

  rw [← h_eq]
  exact add_neg h_pool1 h_pool2

-- **Informal Note: K-Pool Generalization Principle** (NOT a checked theorem).
--
-- The k-pool split function F(a1, ..., a_{k-1}) = sum_i f_i(c_i * a_i) has
-- coordinate-wise negative second forward difference because:
--
-- 1. Only 2 pools change per coordinate step (pool j increasing, pool k-1 decreasing)
-- 2. Each changing pool's contribution is negative by `cpmmOutputCont_secondDiff_neg`
-- 3. The sum of two negative numbers is negative
--
-- This principle extends the 2-pool proof to any k >= 2. The formal Lean proof
-- for k > 3 would use a sum over a Finset or List of pool parameters, but the
-- mathematical argument is identical: separability + per-pool negativity.
--
-- **Non-claim**: This is an INFORMAL NOTE, not a checked theorem. The formal
-- checked theorems above cover k = 3 (coordinates 1 and 2). The k > 3 case
-- follows by the same argument but requires additional Lean infrastructure
-- (Finset sums) not developed here. Do NOT cite this as a formal proof of
-- k-pool concavity for k > 3.
--
-- The formal checked results are splitFunction3PoolCont_concave_coord1
-- and splitFunction3PoolCont_concave_coord2 (3-pool, both coordinates).
