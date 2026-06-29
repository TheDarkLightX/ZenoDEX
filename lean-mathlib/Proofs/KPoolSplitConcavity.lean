/-
# K-Pool CPMM Split Function: Coordinate-Wise Negative Second Forward Difference

This file proves checked coordinate-slice forms of K-pool CPMM split concavity.
It generalizes the 2-pool result from `CpmmSplitConcavity.lean` to 3 pools,
then factors the K-pool proof obligation through a reusable two-changing-pool
kernel.

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
- This also proves a coordinate-slice kernel for arbitrary K-pool slices:
  once non-moving pools are fixed, only the active coordinate pool and the
  remainder pool change.
- A concrete 4-pool coordinate theorem instantiates that kernel.
- A concrete 5-pool coordinate theorem exercises the same kernel with three
  fixed non-moving pools.
- A List-sum coordinate-slice bridge covers arbitrary finite lists of fixed
  non-moving pools.
- Fixed-pool input/output sums and coordinate slices are invariant under
  permutation of the fixed non-moving pool list.
- Selected-list bridges cover full lists that are already decomposed with the
  active and remainder pools in either order.
- A proof-carrying unordered/List presentation certificate packages a full
  presentation, an order-tagged selected-pair decomposition, and a canonical
  fixed-pool representative. Consuming that certificate transfers the
  coordinate-slice concavity proof to the canonical fixed list.
- Full-list ordered-index constructors build that proof-carrying certificate
  from concrete active/remainder indices in either selected-pair order and
  compose it with the certificate-consumption concavity theorem.
- Identity-stable full-list presentation bridges add explicit pool identities,
  require distinct active/remainder identities, erase identities into the
  existing ordered-index constructors, and preserve permutation after erasure.
- An active-before-remainder arbitrary-index decomposition bridge reconstructs
  a full List from `take`/`drop` slices when the active index is strictly before
  the remainder index.
- A remainder-before-active arbitrary-index decomposition bridge reconstructs
  the same full List shape through the order-tagged selected-list witness when
  the remainder index is strictly before the active index.
- Index-witness bridges identify the concrete active and remainder positions
  inside those explicit selected-list decompositions.
- A bounded removal bridge proves that erasing the selected active pool and
  then the selected remainder pool from either explicit selected-list order
  leaves exactly the fixed non-moving pools.
- Arbitrary-index removal bridges prove that erasing the selected active pool
  and then the selected remainder pool from an undecomposed full List leaves
  exactly the fixed non-moving slices for both selected-pair orders.
- The remaining full K theorem still needs unordered collection
  canonicalization and Finset/Multiset quotient infrastructure.
- This does NOT prove joint concavity (Hessian negative definite) or the full
  arbitrary-index all-K theorem.
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

/-- A one-dimensional coordinate slice of an arbitrary K-pool split.

    In a K-pool split, fix every non-moving non-remainder pool. The fixed pools
    contribute `fixedOutput`, while their input allocations contribute
    `fixedInputSum` to the remainder constraint. Moving coordinate `a` changes
    exactly two terms: the active pool and the remainder pool. -/
noncomputable def splitFunctionCoordSliceCont
    (Kj Mj cj Kr Mr cr D fixedInputSum fixedOutput a : ℝ) : ℝ :=
  fixedOutput +
  cpmmOutputCont Kj Mj (cj * a) +
  cpmmOutputCont Kr Mr (cr * (D - fixedInputSum - a))

/-- **K-Pool Coordinate Slice Concavity**: every K-pool coordinate slice with
    fixed non-moving pools has strictly negative second forward difference.

    This is the checked separability kernel for K-pool coordinate moves. A full
    Finset/List theorem can instantiate this kernel after proving that the
    non-moving pools reduce to `fixedInputSum` and `fixedOutput`. -/
theorem splitFunctionCoordSliceCont_concave
    (Kj Mj cj Kr Mr cr D fixedInputSum fixedOutput a h : ℝ)
    (hKj : Kj > 0) (hMj : Mj > 0) (hcj : cj > 0)
    (hKr : Kr > 0) (hMr : Mr > 0) (hcr : cr > 0)
    (hh : h > 0)
    (h_denomj : Mj + cj * a > 0)
    (h_denomr_base : Mr + cr * (D - fixedInputSum - a - 2*h) > 0)
    : secondDiff (splitFunctionCoordSliceCont Kj Mj cj Kr Mr cr D fixedInputSum fixedOutput) a h < 0 := by
  have h_poolj : secondDiff (cpmmOutputCont Kj Mj) (cj * a) (cj * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hKj
    · exact hMj
    · exact mul_pos hcj hh
    · exact h_denomj

  have h_poolr :
      secondDiff (cpmmOutputCont Kr Mr) (cr * (D - fixedInputSum - a - 2*h)) (cr * h) < 0 := by
    apply cpmmOutputCont_secondDiff_neg
    · exact hKr
    · exact hMr
    · exact mul_pos hcr hh
    · exact h_denomr_base

  have h_eq :
      secondDiff (cpmmOutputCont Kj Mj) (cj * a) (cj * h) +
        secondDiff (cpmmOutputCont Kr Mr) (cr * (D - fixedInputSum - a - 2*h)) (cr * h) =
      secondDiff (splitFunctionCoordSliceCont Kj Mj cj Kr Mr cr D fixedInputSum fixedOutput) a h := by
    unfold secondDiff splitFunctionCoordSliceCont cpmmOutputCont
    ring

  rw [← h_eq]
  exact add_neg h_poolj h_poolr

/-- A fixed non-moving pool term for List-sum coordinate-slice proofs.

    `a` is the fixed input allocated to this pool. Its output contributes a
    constant term to the slice, and its input contributes to the remainder
    constraint. -/
structure FixedPoolTermCont where
  K : ℝ
  M : ℝ
  c : ℝ
  a : ℝ

namespace FixedPoolTermCont

/-- Input contribution of a fixed pool. -/
noncomputable def input (p : FixedPoolTermCont) : ℝ :=
  p.a

/-- Output contribution of a fixed pool. -/
noncomputable def output (p : FixedPoolTermCont) : ℝ :=
  cpmmOutputCont p.K p.M (p.c * p.a)

end FixedPoolTermCont

/-- Sum of fixed non-moving pool inputs. -/
noncomputable def fixedPoolInputSumCont (fixed : List FixedPoolTermCont) : ℝ :=
  (fixed.map FixedPoolTermCont.input).sum

/-- Sum of fixed non-moving pool outputs. -/
noncomputable def fixedPoolOutputSumCont (fixed : List FixedPoolTermCont) : ℝ :=
  (fixed.map FixedPoolTermCont.output).sum

@[simp] theorem fixedPoolInputSumCont_nil :
    fixedPoolInputSumCont [] = 0 := by
  simp [fixedPoolInputSumCont]

@[simp] theorem fixedPoolInputSumCont_cons
    (p : FixedPoolTermCont) (ps : List FixedPoolTermCont) :
    fixedPoolInputSumCont (p :: ps) = p.a + fixedPoolInputSumCont ps := by
  simp [fixedPoolInputSumCont, FixedPoolTermCont.input]

@[simp] theorem fixedPoolOutputSumCont_nil :
    fixedPoolOutputSumCont [] = 0 := by
  simp [fixedPoolOutputSumCont]

@[simp] theorem fixedPoolOutputSumCont_cons
    (p : FixedPoolTermCont) (ps : List FixedPoolTermCont) :
    fixedPoolOutputSumCont (p :: ps) =
      cpmmOutputCont p.K p.M (p.c * p.a) + fixedPoolOutputSumCont ps := by
  simp [fixedPoolOutputSumCont, FixedPoolTermCont.output]

@[simp] theorem fixedPoolInputSumCont_append
    (xs ys : List FixedPoolTermCont) :
    fixedPoolInputSumCont (xs ++ ys) =
      fixedPoolInputSumCont xs + fixedPoolInputSumCont ys := by
  simp [fixedPoolInputSumCont, List.map_append, List.sum_append]

@[simp] theorem fixedPoolOutputSumCont_append
    (xs ys : List FixedPoolTermCont) :
    fixedPoolOutputSumCont (xs ++ ys) =
      fixedPoolOutputSumCont xs + fixedPoolOutputSumCont ys := by
  simp [fixedPoolOutputSumCont, List.map_append, List.sum_append]

/-- Fixed-pool input compression is invariant under permutation of the fixed
    non-moving pool list. This is a List-side quotient bridge: it does not
    select active/remainder pools from a full unordered collection. -/
theorem fixedPoolInputSumCont_perm
    {xs ys : List FixedPoolTermCont} (hPerm : List.Perm xs ys) :
    fixedPoolInputSumCont xs = fixedPoolInputSumCont ys := by
  have hMapPerm :
      List.Perm (xs.map FixedPoolTermCont.input) (ys.map FixedPoolTermCont.input) :=
    List.Perm.map _ hPerm
  exact hMapPerm.sum_eq

/-- Fixed-pool output compression is invariant under permutation of the fixed
    non-moving pool list. -/
theorem fixedPoolOutputSumCont_perm
    {xs ys : List FixedPoolTermCont} (hPerm : List.Perm xs ys) :
    fixedPoolOutputSumCont xs = fixedPoolOutputSumCont ys := by
  have hMapPerm :
      List.Perm (xs.map FixedPoolTermCont.output) (ys.map FixedPoolTermCont.output) :=
    List.Perm.map _ hPerm
  exact hMapPerm.sum_eq

/-- A List-sum coordinate slice of a K-pool split.

    The active and remainder pools are singled out. Every other fixed pool is
    represented in `fixed`, and its input/output contribution is summed by
    `fixedPoolInputSumCont` and `fixedPoolOutputSumCont`. -/
noncomputable def splitFunctionListCoordSliceCont
    (fixed : List FixedPoolTermCont) (Kj Mj cj Kr Mr cr D a : ℝ) : ℝ :=
  splitFunctionCoordSliceCont Kj Mj cj Kr Mr cr D
    (fixedPoolInputSumCont fixed)
    (fixedPoolOutputSumCont fixed)
    a

/-- **List-Sum K-Pool Coordinate Slice Concavity**: after selecting an active
    pool and a remainder pool, an arbitrary finite List of fixed non-moving
    pools can be compressed into summed fixed input and output terms, and the
    checked coordinate-slice kernel applies.

    This is a checked List-sum bridge for the fixed-pool part of the all-K
    proof obligation. It still assumes the active and remainder pools have
    already been selected. -/
theorem splitFunctionListCoordSliceCont_concave
    (fixed : List FixedPoolTermCont)
    (Kj Mj cj Kr Mr cr D a h : ℝ)
    (hKj : Kj > 0) (hMj : Mj > 0) (hcj : cj > 0)
    (hKr : Kr > 0) (hMr : Mr > 0) (hcr : cr > 0)
    (hh : h > 0)
    (h_denomj : Mj + cj * a > 0)
    (h_denomr_base : Mr + cr * (D - fixedPoolInputSumCont fixed - a - 2*h) > 0)
    : secondDiff (splitFunctionListCoordSliceCont fixed Kj Mj cj Kr Mr cr D) a h < 0 := by
  simpa [splitFunctionListCoordSliceCont] using
    (splitFunctionCoordSliceCont_concave
      Kj Mj cj Kr Mr cr D
      (fixedPoolInputSumCont fixed) (fixedPoolOutputSumCont fixed)
      a h
      hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base)

/-- The List-sum coordinate slice depends on the fixed non-moving pools only
    through permutation-invariant input/output sums. -/
theorem splitFunctionListCoordSliceCont_eq_of_perm_fixed
    {fixed fixed' : List FixedPoolTermCont}
    (hPerm : List.Perm fixed fixed')
    (Kj Mj cj Kr Mr cr D : ℝ) :
    splitFunctionListCoordSliceCont fixed Kj Mj cj Kr Mr cr D =
      splitFunctionListCoordSliceCont fixed' Kj Mj cj Kr Mr cr D := by
  funext a
  unfold splitFunctionListCoordSliceCont splitFunctionCoordSliceCont
  rw [fixedPoolInputSumCont_perm hPerm, fixedPoolOutputSumCont_perm hPerm]

/-- A full selected-pool decomposition witness.

    The active and remainder pools are present in the full list, but the
    coordinate slice treats them as moving terms and compresses only the fixed
    pools `left ++ between ++ right`. -/
def selectedFullPoolListCont
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) : List FixedPoolTermCont :=
  left ++ active :: between ++ remainder :: right

/-- Active-before-remainder arbitrary-index decomposition bridge.

    Given an undecomposed full pool list and two concrete indices with
    `i < j`, the usual `take`/`drop` slices form a selected-list witness that
    reconstructs the original list exactly. The order-tagged reversed theorem
    below handles the opposite selected-pair order; arbitrary-index removal and
    Finset quotient bridges remain separate proof obligations. -/
theorem selectedFullPoolListCont_eq_take_drop_of_lt
    (pools : List FixedPoolTermCont) {i j : Nat}
    (hij : i < j) (hj : j < pools.length) :
    selectedFullPoolListCont
      (pools.take i)
      (pools[i]'(lt_trans hij hj))
      ((pools.drop (i + 1)).take (j - i - 1))
      (pools[j]'hj)
      (pools.drop (j + 1)) = pools := by
  unfold selectedFullPoolListCont
  have hi : i < pools.length := lt_trans hij hj
  have hdrop_i :
      pools[i]'hi :: pools.drop (i + 1) = pools.drop i := by
    exact List.cons_getElem_drop_succ (l := pools) (n := i) (h := hi)
  have hdrop_j :
      pools[j]'hj :: pools.drop (j + 1) = pools.drop j := by
    exact List.cons_getElem_drop_succ (l := pools) (n := j) (h := hj)
  have hsum : i + 1 + (j - i - 1) = j := by omega
  calc
    pools.take i ++
        pools[i]'hi :: (pools.drop (i + 1)).take (j - i - 1) ++
          pools[j]'hj :: pools.drop (j + 1)
        = pools.take i ++
            (pools[i]'hi ::
              ((pools.drop (i + 1)).take (j - i - 1) ++
                pools[j]'hj :: pools.drop (j + 1))) := by
          simp [List.append_assoc]
    _ = pools.take i ++
          (pools[i]'hi ::
            ((pools.drop (i + 1)).take (j - i - 1) ++ pools.drop j)) := by
          rw [hdrop_j]
    _ = pools.take i ++
          (pools[i]'hi ::
            ((pools.drop (i + 1)).take (j - i - 1) ++
              pools.drop (i + 1 + (j - i - 1)))) := by
          rw [hsum]
    _ = pools.take i ++ (pools[i]'hi :: pools.drop (i + 1)) := by
          rw [List.drop_take_append_drop]
    _ = pools.take i ++ pools.drop i := by
          rw [hdrop_i]
    _ = pools := by
          exact List.take_append_drop i pools

/-- The two possible orders for a selected active/remainder pair in a full List. -/
inductive SelectedPoolOrderCont where
  | activeBeforeRemainder
  | remainderBeforeActive
deriving DecidableEq, Repr

/-- A full selected-pool decomposition witness for either selected-pair order.

    In both cases, the fixed non-moving pools are `left ++ between ++ right`.
    This records the list-shape case split needed before applying the coordinate
    slice kernel. -/
def selectedFullPoolListOrderedCont
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) : List FixedPoolTermCont :=
  match order with
  | .activeBeforeRemainder => left ++ active :: between ++ remainder :: right
  | .remainderBeforeActive => left ++ remainder :: between ++ active :: right

@[simp] theorem selectedFullPoolListOrderedCont_activeBeforeRemainder
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    selectedFullPoolListOrderedCont .activeBeforeRemainder left active between remainder right =
      selectedFullPoolListCont left active between remainder right := by
  rfl

@[simp] theorem selectedFullPoolListOrderedCont_remainderBeforeActive
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    selectedFullPoolListOrderedCont .remainderBeforeActive left active between remainder right =
      left ++ remainder :: between ++ active :: right := by
  rfl

/-- Remainder-before-active arbitrary-index decomposition bridge.

    Given an undecomposed full pool list and two concrete indices with
    `j < i`, the same `take`/`drop` slices form the reversed order-tagged
    selected-list witness and reconstruct the original list exactly. This closes
    the List reconstruction half of the two-order arbitrary-index selection
    gap; arbitrary-index removal and Finset quotient bridges remain separate
    proof obligations. -/
theorem selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt
    (pools : List FixedPoolTermCont) {j i : Nat}
    (hji : j < i) (hi : i < pools.length) :
    selectedFullPoolListOrderedCont .remainderBeforeActive
      (pools.take j)
      (pools[i]'hi)
      ((pools.drop (j + 1)).take (i - j - 1))
      (pools[j]'(lt_trans hji hi))
      (pools.drop (i + 1)) = pools := by
  change
    selectedFullPoolListCont
      (pools.take j)
      (pools[j]'(lt_trans hji hi))
      ((pools.drop (j + 1)).take (i - j - 1))
      (pools[i]'hi)
      (pools.drop (i + 1)) = pools
  exact
    (selectedFullPoolListCont_eq_take_drop_of_lt
      (pools := pools) (i := j) (j := i) hji hi)

/-- Concrete active-pool index inside an order-tagged selected-list witness. -/
def selectedActiveIndexOrderedCont
    (order : SelectedPoolOrderCont)
    (left between : List FixedPoolTermCont) : Nat :=
  match order with
  | .activeBeforeRemainder => left.length
  | .remainderBeforeActive => left.length + between.length + 1

/-- Concrete remainder-pool index inside an order-tagged selected-list witness. -/
def selectedRemainderIndexOrderedCont
    (order : SelectedPoolOrderCont)
    (left between : List FixedPoolTermCont) : Nat :=
  match order with
  | .activeBeforeRemainder => left.length + between.length + 1
  | .remainderBeforeActive => left.length

/-- The concrete active index is in bounds for either selected-pair order
    witness. -/
theorem selectedActiveIndexOrderedCont_lt
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    selectedActiveIndexOrderedCont order left between <
      (selectedFullPoolListOrderedCont order left active between remainder right).length := by
  cases order <;>
    simp [selectedFullPoolListOrderedCont, selectedActiveIndexOrderedCont,
      Nat.add_assoc]

/-- The concrete remainder index is in bounds for either selected-pair order
    witness. -/
theorem selectedRemainderIndexOrderedCont_lt
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    selectedRemainderIndexOrderedCont order left between <
      (selectedFullPoolListOrderedCont order left active between remainder right).length := by
  cases order <;>
    simp [selectedFullPoolListOrderedCont, selectedRemainderIndexOrderedCont,
      Nat.add_assoc]

/-- The concrete active index retrieves the active pool from either selected-pair
    order witness. This is an index-witness bridge for explicit decompositions,
    not a theorem deriving those decompositions from arbitrary indices. -/
theorem selectedFullPoolListOrderedCont_get_active
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    (selectedFullPoolListOrderedCont order left active between remainder right)[
      selectedActiveIndexOrderedCont order left between]'
        (selectedActiveIndexOrderedCont_lt order left active between remainder right) = active := by
  cases order <;>
    simp [selectedFullPoolListOrderedCont, selectedActiveIndexOrderedCont,
      Nat.add_assoc]

/-- The concrete remainder index retrieves the remainder pool from either
    selected-pair order witness. This records the other half of the bounded
    index bridge needed before arbitrary List/Finset lookup can be attacked. -/
theorem selectedFullPoolListOrderedCont_get_remainder
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    (selectedFullPoolListOrderedCont order left active between remainder right)[
      selectedRemainderIndexOrderedCont order left between]'
        (selectedRemainderIndexOrderedCont_lt order left active between remainder right) = remainder := by
  cases order <;>
    simp [selectedFullPoolListOrderedCont, selectedRemainderIndexOrderedCont,
      Nat.add_assoc]

/-- The active and remainder positions in an explicit order-tagged witness are
    distinct. -/
theorem selectedActiveIndexOrderedCont_ne_remainderIndex
    (order : SelectedPoolOrderCont)
    (left between : List FixedPoolTermCont) :
    selectedActiveIndexOrderedCont order left between ≠
      selectedRemainderIndexOrderedCont order left between := by
  cases order <;>
    simp [selectedActiveIndexOrderedCont, selectedRemainderIndexOrderedCont,
      Nat.add_assoc]

/-- The fixed pools remaining after the active and remainder pools are removed
    from an explicit selected-list witness. -/
def selectedFixedPoolListOrderedCont
    (left between right : List FixedPoolTermCont) : List FixedPoolTermCont :=
  left ++ between ++ right

/-- Remainder index after erasing the active pool first.

    If the active pool originally appears before the remainder pool, the
    remainder index shifts left by one. If the remainder pool appears first,
    its index is unchanged. -/
def selectedRemainderIndexAfterActiveEraseOrderedCont
    (order : SelectedPoolOrderCont)
    (left between : List FixedPoolTermCont) : Nat :=
  match order with
  | .activeBeforeRemainder => left.length + between.length
  | .remainderBeforeActive => left.length

private theorem eraseIdx_append_length_cons_fixed
    (left tail : List FixedPoolTermCont) (pool : FixedPoolTermCont) :
    (left ++ pool :: tail).eraseIdx left.length = left ++ tail := by
  induction left with
  | nil => simp
  | cons _ left ih => simp [ih]

/-- Removing the selected active pool and then the selected remainder pool from
    an explicit order-tagged full-list witness leaves exactly the fixed pools.

    This is a bounded removal bridge for supplied decomposition witnesses. It
    still does not derive the decomposition from arbitrary indices over an
    undecomposed List or Finset. -/
theorem selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) :
    ((selectedFullPoolListOrderedCont order left active between remainder right).eraseIdx
        (selectedActiveIndexOrderedCont order left between)).eraseIdx
        (selectedRemainderIndexAfterActiveEraseOrderedCont order left between) =
      selectedFixedPoolListOrderedCont left between right := by
  cases order
  · have h_drop_active :
        (left ++ active :: between ++ remainder :: right).eraseIdx left.length =
          left ++ between ++ remainder :: right := by
      simpa [List.append_assoc] using
        (eraseIdx_append_length_cons_fixed left (between ++ remainder :: right) active)
    have h_drop_remainder :
        (left ++ between ++ remainder :: right).eraseIdx (left.length + between.length) =
          left ++ between ++ right := by
      simpa [List.length_append, List.append_assoc, Nat.add_assoc] using
        (eraseIdx_append_length_cons_fixed (left ++ between) right remainder)
    change
      ((left ++ active :: between ++ remainder :: right).eraseIdx left.length).eraseIdx
          (left.length + between.length) =
        left ++ between ++ right
    rw [h_drop_active, h_drop_remainder]
  · have h_drop_active :
        (left ++ remainder :: between ++ active :: right).eraseIdx
            (left.length + (between.length + 1)) =
          left ++ remainder :: between ++ right := by
      simpa [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (eraseIdx_append_length_cons_fixed (left ++ remainder :: between) right active)
    have h_drop_remainder :
        (left ++ remainder :: between ++ right).eraseIdx left.length =
          left ++ between ++ right := by
      simpa [List.append_assoc] using
        (eraseIdx_append_length_cons_fixed left (between ++ right) remainder)
    change
      ((left ++ remainder :: between ++ active :: right).eraseIdx
          (left.length + (between.length + 1))).eraseIdx left.length =
        left ++ between ++ right
    rw [h_drop_active, h_drop_remainder]

/-- The middle `take` slice between two concrete indices has the expected
    length. -/
private theorem selectedMiddleSliceLength_eq_sub_of_lt
    (pools : List FixedPoolTermCont) {i j : Nat}
    (hij : i < j) (hj : j < pools.length) :
    ((pools.drop (i + 1)).take (j - i - 1)).length = j - i - 1 := by
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  omega

/-- Active-before-remainder arbitrary-index removal bridge.

    After selecting concrete indices `i < j`, erasing the active pool at `i`
    and then the shifted remainder index `j - 1` leaves exactly the fixed-pool
    slices. This closes the active-before List-side arbitrary-index removal
    obligation; Finset quotient infrastructure remains separate. -/
theorem selectedFullPoolListCont_erase_active_then_remainder_eq_take_drop_of_lt
    (pools : List FixedPoolTermCont) {i j : Nat}
    (hij : i < j) (hj : j < pools.length) :
    ((pools.eraseIdx i).eraseIdx (j - 1)) =
      pools.take i ++ (pools.drop (i + 1)).take (j - i - 1) ++
        pools.drop (j + 1) := by
  have hi : i < pools.length := lt_trans hij hj
  have h_reconstruct :
      selectedFullPoolListOrderedCont .activeBeforeRemainder
        (pools.take i)
        (pools[i]'hi)
        ((pools.drop (i + 1)).take (j - i - 1))
        (pools[j]'hj)
        (pools.drop (j + 1)) = pools := by
    simpa using
      (selectedFullPoolListCont_eq_take_drop_of_lt
        (pools := pools) (i := i) (j := j) hij hj)
  have h_left_len : (pools.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have h_between_len :
      ((pools.drop (i + 1)).take (j - i - 1)).length = j - i - 1 :=
    selectedMiddleSliceLength_eq_sub_of_lt (pools := pools) hij hj
  have h_index : i + (j - i - 1) = j - 1 := by omega
  have h_remove :=
    selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed
      .activeBeforeRemainder
      (pools.take i)
      (pools[i]'hi)
      ((pools.drop (i + 1)).take (j - i - 1))
      (pools[j]'hj)
      (pools.drop (j + 1))
  rw [h_reconstruct] at h_remove
  simpa [selectedActiveIndexOrderedCont,
    selectedRemainderIndexAfterActiveEraseOrderedCont,
    selectedFixedPoolListOrderedCont, h_left_len, h_between_len, h_index,
    Nat.add_assoc] using h_remove

/-- Remainder-before-active arbitrary-index removal bridge.

    After selecting concrete indices `j < i`, erasing the active pool at `i`
    and then the unchanged remainder index `j` leaves exactly the fixed-pool
    slices. This closes the reversed List-side arbitrary-index removal
    obligation; Finset quotient infrastructure remains separate. -/
theorem selectedFullPoolListOrderedCont_remainderBeforeActive_erase_active_then_remainder_eq_take_drop_of_lt
    (pools : List FixedPoolTermCont) {j i : Nat}
    (hji : j < i) (hi : i < pools.length) :
    ((pools.eraseIdx i).eraseIdx j) =
      pools.take j ++ (pools.drop (j + 1)).take (i - j - 1) ++
        pools.drop (i + 1) := by
  have hj : j < pools.length := lt_trans hji hi
  have h_reconstruct :
      selectedFullPoolListOrderedCont .remainderBeforeActive
        (pools.take j)
        (pools[i]'hi)
        ((pools.drop (j + 1)).take (i - j - 1))
        (pools[j]'hj)
        (pools.drop (i + 1)) = pools :=
    selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt
      (pools := pools) hji hi
  have h_left_len : (pools.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have h_between_len :
      ((pools.drop (j + 1)).take (i - j - 1)).length = i - j - 1 :=
    selectedMiddleSliceLength_eq_sub_of_lt (pools := pools) hji hi
  have h_active_index : j + (i - j - 1) + 1 = i := by omega
  have h_remove :=
    selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed
      .remainderBeforeActive
      (pools.take j)
      (pools[i]'hi)
      ((pools.drop (j + 1)).take (i - j - 1))
      (pools[j]'hj)
      (pools.drop (i + 1))
  rw [h_reconstruct] at h_remove
  simpa [selectedActiveIndexOrderedCont,
    selectedRemainderIndexAfterActiveEraseOrderedCont,
    selectedFixedPoolListOrderedCont, h_left_len, h_between_len,
    h_active_index, Nat.add_assoc] using h_remove

/-- Coordinate slice for an explicitly selected active/remainder pair.

    This is the checked bridge from a full-list decomposition witness to the
    existing List-sum fixed-pool kernel. It assumes the decomposition has already
    selected the active and remainder pools. -/
noncomputable def splitFunctionSelectedListCoordSliceCont
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D a : ℝ) : ℝ :=
  fixedPoolOutputSumCont left +
  fixedPoolOutputSumCont between +
  fixedPoolOutputSumCont right +
  cpmmOutputCont active.K active.M (active.c * a) +
  cpmmOutputCont remainder.K remainder.M
    (remainder.c *
      (D - (fixedPoolInputSumCont left +
        fixedPoolInputSumCont between +
        fixedPoolInputSumCont right) - a))

/-- The selected-list slice reduces to the existing fixed-pool List-sum slice.

    The fixed pools are exactly `left ++ between ++ right`; the active and
    remainder pools are supplied as the two changing terms. -/
theorem splitFunctionSelectedListCoordSliceCont_eq_listCoordSliceCont
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D : ℝ) :
    splitFunctionSelectedListCoordSliceCont left active between remainder right D =
      splitFunctionListCoordSliceCont (left ++ between ++ right)
        active.K active.M active.c remainder.K remainder.M remainder.c D := by
  funext a
  unfold splitFunctionSelectedListCoordSliceCont
    splitFunctionListCoordSliceCont splitFunctionCoordSliceCont
  simp only [fixedPoolInputSumCont_append, fixedPoolOutputSumCont_append]

/-- **Selected-List K-Pool Coordinate Slice Concavity**: for a full pool list
    represented by `left ++ active :: between ++ remainder :: right`, the
    selected coordinate slice has strictly negative second forward difference.

    This proves the selection/removal bridge for explicit decomposition
    witnesses. It does not prove arbitrary index lookup over an undecomposed
    List or Finset. -/
theorem splitFunctionSelectedListCoordSliceCont_concave
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D a h : ℝ)
    (hKj : active.K > 0) (hMj : active.M > 0) (hcj : active.c > 0)
    (hKr : remainder.K > 0) (hMr : remainder.M > 0) (hcr : remainder.c > 0)
    (hh : h > 0)
    (h_denomj : active.M + active.c * a > 0)
    (h_denomr_base :
      remainder.M +
        remainder.c * (D - fixedPoolInputSumCont (left ++ between ++ right) - a - 2*h) > 0)
    : secondDiff
      (splitFunctionSelectedListCoordSliceCont left active between remainder right D)
      a h < 0 := by
  rw [splitFunctionSelectedListCoordSliceCont_eq_listCoordSliceCont]
  exact splitFunctionListCoordSliceCont_concave
    (left ++ between ++ right)
    active.K active.M active.c remainder.K remainder.M remainder.c D a h
    hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- Coordinate slice for an explicitly selected active/remainder pair with its
    full-list order recorded.

    The order parameter records whether the active pool appears before the
    remainder pool or after it in the full List. The moving terms and the fixed
    pool compression are the same in either case. -/
noncomputable def splitFunctionSelectedListOrderedCoordSliceCont
    (_order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D a : ℝ) : ℝ :=
  splitFunctionSelectedListCoordSliceCont left active between remainder right D a

/-- The order-tagged selected-list slice reduces to the same fixed-pool
    List-sum slice for both active/remainder orders. -/
theorem splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D : ℝ) :
    splitFunctionSelectedListOrderedCoordSliceCont order left active between remainder right D =
      splitFunctionListCoordSliceCont (left ++ between ++ right)
        active.K active.M active.c remainder.K remainder.M remainder.c D := by
  funext a
  unfold splitFunctionSelectedListOrderedCoordSliceCont
  rw [splitFunctionSelectedListCoordSliceCont_eq_listCoordSliceCont]

/-- The selected-list coordinate slice can be transferred to any canonical fixed
    pool list that is a permutation of `left ++ between ++ right`.

    This is a permutation quotient bridge for the fixed-pool compression. It
    still assumes that the active and remainder pools have already been selected
    by a List-side witness. -/
theorem splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont_of_perm_fixed
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right fixed : List FixedPoolTermCont) (D : ℝ)
    (hPerm : List.Perm (left ++ between ++ right) fixed) :
    splitFunctionSelectedListOrderedCoordSliceCont order left active between remainder right D =
      splitFunctionListCoordSliceCont fixed
        active.K active.M active.c remainder.K remainder.M remainder.c D := by
  rw [splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont]
  exact
    splitFunctionListCoordSliceCont_eq_of_perm_fixed hPerm
      active.K active.M active.c remainder.K remainder.M remainder.c D

/-- **Order-Tagged Selected-List K-Pool Coordinate Slice Concavity**: for a full
    pool list with the active and remainder pools selected in either order, the
    selected coordinate slice has strictly negative second forward difference.

    This closes the order-case part of the List decomposition witness. It still
    assumes a decomposition witness is supplied, so arbitrary index lookup over
    an undecomposed List or Finset remains open. -/
theorem splitFunctionSelectedListOrderedCoordSliceCont_concave
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right : List FixedPoolTermCont) (D a h : ℝ)
    (hKj : active.K > 0) (hMj : active.M > 0) (hcj : active.c > 0)
    (hKr : remainder.K > 0) (hMr : remainder.M > 0) (hcr : remainder.c > 0)
    (hh : h > 0)
    (h_denomj : active.M + active.c * a > 0)
    (h_denomr_base :
      remainder.M +
        remainder.c * (D - fixedPoolInputSumCont (left ++ between ++ right) - a - 2*h) > 0)
    : secondDiff
      (splitFunctionSelectedListOrderedCoordSliceCont order left active between remainder right D)
      a h < 0 := by
  rw [splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont]
  exact splitFunctionListCoordSliceCont_concave
    (left ++ between ++ right)
    active.K active.M active.c remainder.K remainder.M remainder.c D a h
    hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- Selected-list concavity transferred through a canonical fixed-pool list.

    If a quotient/canonicalization layer supplies any fixed list permutation
    equivalent to the explicit `left ++ between ++ right` fixed pools, the
    coordinate-slice concavity proof can consume the canonical list directly.
    Selecting active/remainder pools from a full unordered collection remains a
    separate obligation. -/
theorem splitFunctionSelectedListOrderedCoordSliceCont_concave_of_perm_fixed
    (order : SelectedPoolOrderCont)
    (left : List FixedPoolTermCont) (active : FixedPoolTermCont)
    (between : List FixedPoolTermCont) (remainder : FixedPoolTermCont)
    (right fixed : List FixedPoolTermCont) (D a h : ℝ)
    (hPerm : List.Perm (left ++ between ++ right) fixed)
    (hKj : active.K > 0) (hMj : active.M > 0) (hcj : active.c > 0)
    (hKr : remainder.K > 0) (hMr : remainder.M > 0) (hcr : remainder.c > 0)
    (hh : h > 0)
    (h_denomj : active.M + active.c * a > 0)
    (h_denomr_base :
      remainder.M +
        remainder.c * (D - fixedPoolInputSumCont fixed - a - 2*h) > 0) :
    secondDiff
      (splitFunctionSelectedListOrderedCoordSliceCont order left active between remainder right D)
      a h < 0 := by
  rw [splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont_of_perm_fixed
    order left active between remainder right fixed D hPerm]
  exact splitFunctionListCoordSliceCont_concave
    fixed
    active.K active.M active.c remainder.K remainder.M remainder.c D a h
    hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- Proof-carrying selection certificate for an unordered/List-presented full
    pool collection.

    The certificate packages the full presentation, a selected active/remainder
    decomposition, and a canonical fixed-pool representative. It validates a
    supplied witness; constructing this certificate from an arbitrary
    Finset/Multiset presentation is a separate obligation. -/
structure UnorderedSelectionCertificateCont where
  order : SelectedPoolOrderCont
  left : List FixedPoolTermCont
  active : FixedPoolTermCont
  between : List FixedPoolTermCont
  remainder : FixedPoolTermCont
  right : List FixedPoolTermCont
  fixed : List FixedPoolTermCont
  full : List FixedPoolTermCont
  full_eq :
    selectedFullPoolListOrderedCont order left active between remainder right = full
  fixed_perm :
    List.Perm (selectedFixedPoolListOrderedCont left between right) fixed

/-- The certificate reconstructs its advertised full pool presentation. -/
theorem unorderedSelectionCertificate_full_eq
    (cert : UnorderedSelectionCertificateCont) :
    selectedFullPoolListOrderedCont cert.order cert.left cert.active cert.between
      cert.remainder cert.right = cert.full :=
  cert.full_eq

/-- The certificate's canonical fixed list is a permutation of the explicit
    fixed-pool slices. -/
theorem unorderedSelectionCertificate_fixed_perm
    (cert : UnorderedSelectionCertificateCont) :
    List.Perm (cert.left ++ cert.between ++ cert.right) cert.fixed := by
  simpa [selectedFixedPoolListOrderedCont] using cert.fixed_perm

/-- Coordinate slice consumed through a proof-carrying unordered selection
    certificate. -/
noncomputable def splitFunctionUnorderedSelectionCertCoordSliceCont
    (cert : UnorderedSelectionCertificateCont) (D a : ℝ) : ℝ :=
  splitFunctionSelectedListOrderedCoordSliceCont cert.order cert.left cert.active
    cert.between cert.remainder cert.right D a

/-- A proof-carrying unordered selection certificate transfers the selected-list
    slice to its canonical fixed-pool representative. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_eq_listCoordSliceCont
    (cert : UnorderedSelectionCertificateCont) (D : ℝ) :
    splitFunctionUnorderedSelectionCertCoordSliceCont cert D =
      splitFunctionListCoordSliceCont cert.fixed
        cert.active.K cert.active.M cert.active.c
        cert.remainder.K cert.remainder.M cert.remainder.c D := by
  unfold splitFunctionUnorderedSelectionCertCoordSliceCont
  exact
    splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont_of_perm_fixed
      cert.order cert.left cert.active cert.between cert.remainder cert.right
      cert.fixed D
      (unorderedSelectionCertificate_fixed_perm cert)

/-- Concavity consumed through a proof-carrying unordered selection
    certificate.

    This is a certificate-consumption theorem. It does not construct the
    certificate from an arbitrary unordered collection. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_concave
    (cert : UnorderedSelectionCertificateCont) (D a h : ℝ)
    (hKj : cert.active.K > 0) (hMj : cert.active.M > 0)
    (hcj : cert.active.c > 0)
    (hKr : cert.remainder.K > 0) (hMr : cert.remainder.M > 0)
    (hcr : cert.remainder.c > 0)
    (hh : h > 0)
    (h_denomj : cert.active.M + cert.active.c * a > 0)
    (h_denomr_base :
      cert.remainder.M +
        cert.remainder.c * (D - fixedPoolInputSumCont cert.fixed - a - 2*h) > 0) :
    secondDiff (splitFunctionUnorderedSelectionCertCoordSliceCont cert D) a h < 0 := by
  unfold splitFunctionUnorderedSelectionCertCoordSliceCont
  exact
    splitFunctionSelectedListOrderedCoordSliceCont_concave_of_perm_fixed
      cert.order cert.left cert.active cert.between cert.remainder cert.right
      cert.fixed D a h
      (unorderedSelectionCertificate_fixed_perm cert)
      hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- Build a proof-carrying selection certificate from a full List and ordered
    active-before-remainder indices.

    This is a List-index constructor. It keeps out-of-bounds selections
    unrepresentable via the index proofs and leaves Finset/Multiset
    canonicalization as a separate quotient obligation. -/
def unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont
    (pools : List FixedPoolTermCont) {i j : Nat}
    (hij : i < j) (hj : j < pools.length) :
    UnorderedSelectionCertificateCont where
  order := .activeBeforeRemainder
  left := pools.take i
  active := pools[i]'(lt_trans hij hj)
  between := (pools.drop (i + 1)).take (j - i - 1)
  remainder := pools[j]'hj
  right := pools.drop (j + 1)
  fixed :=
    pools.take i ++ (pools.drop (i + 1)).take (j - i - 1) ++
      pools.drop (j + 1)
  full := pools
  full_eq := by
    simpa using
      (selectedFullPoolListCont_eq_take_drop_of_lt
        (pools := pools) (i := i) (j := j) hij hj)
  fixed_perm := by
    simp [selectedFixedPoolListOrderedCont]

/-- Build a proof-carrying selection certificate from a full List and ordered
    remainder-before-active indices. -/
def unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont
    (pools : List FixedPoolTermCont) {j i : Nat}
    (hji : j < i) (hi : i < pools.length) :
    UnorderedSelectionCertificateCont where
  order := .remainderBeforeActive
  left := pools.take j
  active := pools[i]'hi
  between := (pools.drop (j + 1)).take (i - j - 1)
  remainder := pools[j]'(lt_trans hji hi)
  right := pools.drop (i + 1)
  fixed :=
    pools.take j ++ (pools.drop (j + 1)).take (i - j - 1) ++
      pools.drop (i + 1)
  full := pools
  full_eq :=
    selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt
      (pools := pools) hji hi
  fixed_perm := by
    simp [selectedFixedPoolListOrderedCont]

/-- The active-before-remainder List-index constructor composes with the
    certificate-consumption concavity theorem. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_activeBeforeRemainderIndex
    (pools : List FixedPoolTermCont) {i j : Nat}
    (hij : i < j) (hj : j < pools.length) (D a h : ℝ)
    (hKj : (pools[i]'(lt_trans hij hj)).K > 0)
    (hMj : (pools[i]'(lt_trans hij hj)).M > 0)
    (hcj : (pools[i]'(lt_trans hij hj)).c > 0)
    (hKr : (pools[j]'hj).K > 0)
    (hMr : (pools[j]'hj).M > 0)
    (hcr : (pools[j]'hj).c > 0)
    (hh : h > 0)
    (h_denomj :
      (pools[i]'(lt_trans hij hj)).M +
        (pools[i]'(lt_trans hij hj)).c * a > 0)
    (h_denomr_base :
      (pools[j]'hj).M +
        (pools[j]'hj).c *
          (D -
            fixedPoolInputSumCont
              (pools.take i ++ (pools.drop (i + 1)).take (j - i - 1) ++
                pools.drop (j + 1)) - a - 2*h) > 0) :
    secondDiff
      (splitFunctionUnorderedSelectionCertCoordSliceCont
        (unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont
          (pools := pools) hij hj) D)
      a h < 0 := by
  simpa [unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont] using
    (splitFunctionUnorderedSelectionCertCoordSliceCont_concave
      (cert := unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont
        (pools := pools) hij hj)
      D a h hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base)

/-- The remainder-before-active List-index constructor composes with the
    certificate-consumption concavity theorem. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_remainderBeforeActiveIndex
    (pools : List FixedPoolTermCont) {j i : Nat}
    (hji : j < i) (hi : i < pools.length) (D a h : ℝ)
    (hKj : (pools[i]'hi).K > 0)
    (hMj : (pools[i]'hi).M > 0)
    (hcj : (pools[i]'hi).c > 0)
    (hKr : (pools[j]'(lt_trans hji hi)).K > 0)
    (hMr : (pools[j]'(lt_trans hji hi)).M > 0)
    (hcr : (pools[j]'(lt_trans hji hi)).c > 0)
    (hh : h > 0)
    (h_denomj : (pools[i]'hi).M + (pools[i]'hi).c * a > 0)
    (h_denomr_base :
      (pools[j]'(lt_trans hji hi)).M +
        (pools[j]'(lt_trans hji hi)).c *
          (D -
            fixedPoolInputSumCont
              (pools.take j ++ (pools.drop (j + 1)).take (i - j - 1) ++
                pools.drop (i + 1)) - a - 2*h) > 0) :
    secondDiff
      (splitFunctionUnorderedSelectionCertCoordSliceCont
        (unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont
          (pools := pools) hji hi) D)
      a h < 0 := by
  simpa [unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont] using
    (splitFunctionUnorderedSelectionCertCoordSliceCont_concave
      (cert := unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont
        (pools := pools) hji hi)
      D a h hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base)

/-- A fixed-pool term with a stable identity.

    The `id` field separates duplicate-valued pools before erasing to the
    mathematical `FixedPoolTermCont` payload consumed by the concavity kernel. -/
structure IdentifiedFixedPoolTermCont where
  id : Nat
  term : FixedPoolTermCont

/-- Erase stable identities from an identified full-list presentation. -/
def identifiedPoolTermsCont
    (pools : List IdentifiedFixedPoolTermCont) : List FixedPoolTermCont :=
  pools.map IdentifiedFixedPoolTermCont.term

@[simp] theorem identifiedPoolTermsCont_length
    (pools : List IdentifiedFixedPoolTermCont) :
    (identifiedPoolTermsCont pools).length = pools.length := by
  simp [identifiedPoolTermsCont]

@[simp] theorem identifiedPoolTermsCont_get
    (pools : List IdentifiedFixedPoolTermCont) {i : Nat}
    (hi : i < pools.length) :
    (identifiedPoolTermsCont pools)[i]'(by simpa [identifiedPoolTermsCont] using hi) =
      (pools[i]'hi).term := by
  simp [identifiedPoolTermsCont]

/-- Erasing stable identities preserves list permutation. This is the quotient
    bridge needed before an unordered canonical representative can feed the
    existing fixed-pool permutation theorems. -/
theorem identifiedPoolTermsCont_perm
    {xs ys : List IdentifiedFixedPoolTermCont} (hPerm : List.Perm xs ys) :
    List.Perm (identifiedPoolTermsCont xs) (identifiedPoolTermsCont ys) := by
  exact List.Perm.map _ hPerm

/-- Active-before-remainder selection over an identified full-list
    presentation.

    The identity inequality makes same-identity active/remainder selection
    unrepresentable even when two selected pools have equal payload terms. -/
structure IdentifiedActiveBeforeRemainderSelectionCont where
  pools : List IdentifiedFixedPoolTermCont
  activeIndex : Nat
  remainderIndex : Nat
  ordered : activeIndex < remainderIndex
  remainder_lt : remainderIndex < pools.length
  ids_distinct :
    (pools[activeIndex]'(lt_trans ordered remainder_lt)).id ≠
      (pools[remainderIndex]'remainder_lt).id

/-- Remainder-before-active selection over an identified full-list
    presentation. -/
structure IdentifiedRemainderBeforeActiveSelectionCont where
  pools : List IdentifiedFixedPoolTermCont
  remainderIndex : Nat
  activeIndex : Nat
  ordered : remainderIndex < activeIndex
  active_lt : activeIndex < pools.length
  ids_distinct :
    (pools[activeIndex]'active_lt).id ≠
      (pools[remainderIndex]'(lt_trans ordered active_lt)).id

/-- The active-before-remainder identified witness exposes its distinct
    selected identities. -/
theorem identifiedActiveBeforeRemainderSelection_ids_distinct
    (sel : IdentifiedActiveBeforeRemainderSelectionCont) :
    (sel.pools[sel.activeIndex]'(lt_trans sel.ordered sel.remainder_lt)).id ≠
      (sel.pools[sel.remainderIndex]'sel.remainder_lt).id :=
  sel.ids_distinct

/-- The remainder-before-active identified witness exposes its distinct
    selected identities. -/
theorem identifiedRemainderBeforeActiveSelection_ids_distinct
    (sel : IdentifiedRemainderBeforeActiveSelectionCont) :
    (sel.pools[sel.activeIndex]'sel.active_lt).id ≠
      (sel.pools[sel.remainderIndex]'(lt_trans sel.ordered sel.active_lt)).id :=
  sel.ids_distinct

/-- Build a proof-carrying selection certificate from an identified
    active-before-remainder full-list witness by erasing stable identities only
    after the witness has ruled out same-identity selection. -/
def unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont
    (sel : IdentifiedActiveBeforeRemainderSelectionCont) :
    UnorderedSelectionCertificateCont :=
  unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont
    (pools := identifiedPoolTermsCont sel.pools)
    sel.ordered
    (by simpa [identifiedPoolTermsCont] using sel.remainder_lt)

/-- Build a proof-carrying selection certificate from an identified
    remainder-before-active full-list witness. -/
def unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont
    (sel : IdentifiedRemainderBeforeActiveSelectionCont) :
    UnorderedSelectionCertificateCont :=
  unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont
    (pools := identifiedPoolTermsCont sel.pools)
    sel.ordered
    (by simpa [identifiedPoolTermsCont] using sel.active_lt)

/-- The active-before identified constructor composes with the
    certificate-consumption concavity theorem. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedActiveBeforeRemainder
    (sel : IdentifiedActiveBeforeRemainderSelectionCont) (D a h : ℝ)
    (hKj :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).active.K > 0)
    (hMj :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).active.M > 0)
    (hcj :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).active.c > 0)
    (hKr :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).remainder.K > 0)
    (hMr :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).remainder.M > 0)
    (hcr :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).remainder.c > 0)
    (hh : h > 0)
    (h_denomj :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).active.M +
        (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).active.c * a > 0)
    (h_denomr_base :
      (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).remainder.M +
        (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).remainder.c *
          (D -
            fixedPoolInputSumCont
              (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel).fixed -
            a - 2*h) > 0) :
    secondDiff
      (splitFunctionUnorderedSelectionCertCoordSliceCont
        (unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel) D)
      a h < 0 :=
  splitFunctionUnorderedSelectionCertCoordSliceCont_concave
    (cert := unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont sel)
    D a h hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- The remainder-before identified constructor composes with the
    certificate-consumption concavity theorem. -/
theorem splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedRemainderBeforeActive
    (sel : IdentifiedRemainderBeforeActiveSelectionCont) (D a h : ℝ)
    (hKj :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).active.K > 0)
    (hMj :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).active.M > 0)
    (hcj :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).active.c > 0)
    (hKr :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).remainder.K > 0)
    (hMr :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).remainder.M > 0)
    (hcr :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).remainder.c > 0)
    (hh : h > 0)
    (h_denomj :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).active.M +
        (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).active.c * a > 0)
    (h_denomr_base :
      (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).remainder.M +
        (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).remainder.c *
          (D -
            fixedPoolInputSumCont
              (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel).fixed -
            a - 2*h) > 0) :
    secondDiff
      (splitFunctionUnorderedSelectionCertCoordSliceCont
        (unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel) D)
      a h < 0 :=
  splitFunctionUnorderedSelectionCertCoordSliceCont_concave
    (cert := unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont sel)
    D a h hKj hMj hcj hKr hMr hcr hh h_denomj h_denomr_base

/-- A concrete 4-pool split function used as a K > 3 checkpoint for the
    coordinate-slice theorem. -/
noncomputable def splitFunction4PoolCont
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 D a1 a2 a3 : ℝ) : ℝ :=
  cpmmOutputCont K0 M0 (c0 * a1) +
  cpmmOutputCont K1 M1 (c1 * a2) +
  cpmmOutputCont K2 M2 (c2 * a3) +
  cpmmOutputCont K3 M3 (c3 * (D - a1 - a2 - a3))

/-- **4-Pool Coordinate 2 Concavity**: moving the second explicit coordinate in
    a 4-pool split has strictly negative second forward difference.

    This theorem instantiates `splitFunctionCoordSliceCont_concave` with pool 1
    as the active pool, pool 3 as the remainder pool, and pools 0 and 2 fixed. -/
theorem splitFunction4PoolCont_concave_coord2
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 D a1 a2 a3 h : ℝ)
    (_hK0 : K0 > 0) (_hM0 : M0 > 0) (_hc0 : c0 > 0)
    (hK1 : K1 > 0) (hM1 : M1 > 0) (hc1 : c1 > 0)
    (_hK2 : K2 > 0) (_hM2 : M2 > 0) (_hc2 : c2 > 0)
    (hK3 : K3 > 0) (hM3 : M3 > 0) (hc3 : c3 > 0)
    (hh : h > 0)
    (h_denom1 : M1 + c1 * a2 > 0)
    (h_denom3_base : M3 + c3 * (D - a1 - a3 - a2 - 2*h) > 0)
    : secondDiff
      (fun b => splitFunction4PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 D a1 b a3)
      a2 h < 0 := by
  have h_kernel :
      secondDiff
        (splitFunctionCoordSliceCont
          K1 M1 c1 K3 M3 c3 D (a1 + a3)
          (cpmmOutputCont K0 M0 (c0 * a1) + cpmmOutputCont K2 M2 (c2 * a3)))
        a2 h < 0 := by
    apply splitFunctionCoordSliceCont_concave
    · exact hK1
    · exact hM1
    · exact hc1
    · exact hK3
    · exact hM3
    · exact hc3
    · exact hh
    · exact h_denom1
    · convert h_denom3_base using 1
      ring

  have h_eq :
      secondDiff
        (splitFunctionCoordSliceCont
          K1 M1 c1 K3 M3 c3 D (a1 + a3)
          (cpmmOutputCont K0 M0 (c0 * a1) + cpmmOutputCont K2 M2 (c2 * a3)))
        a2 h =
      secondDiff
        (fun b => splitFunction4PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 D a1 b a3)
        a2 h := by
    unfold secondDiff splitFunctionCoordSliceCont splitFunction4PoolCont cpmmOutputCont
    ring

  rw [← h_eq]
  exact h_kernel

/-- A concrete 5-pool split function used as the next K > 3 checkpoint for the
    coordinate-slice theorem. -/
noncomputable def splitFunction5PoolCont
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 K4 M4 c4 D a1 a2 a3 a4 : ℝ) : ℝ :=
  cpmmOutputCont K0 M0 (c0 * a1) +
  cpmmOutputCont K1 M1 (c1 * a2) +
  cpmmOutputCont K2 M2 (c2 * a3) +
  cpmmOutputCont K3 M3 (c3 * a4) +
  cpmmOutputCont K4 M4 (c4 * (D - a1 - a2 - a3 - a4))

/-- **5-Pool Coordinate 3 Concavity**: moving the third explicit coordinate in
    a 5-pool split has strictly negative second forward difference.

    This theorem instantiates `splitFunctionCoordSliceCont_concave` with pool 2
    as the active pool, pool 4 as the remainder pool, and pools 0, 1, and 3
    fixed. It is a concrete formalization-ladder checkpoint, not the full
    all-K Finset/List theorem. -/
theorem splitFunction5PoolCont_concave_coord3
    (K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 K4 M4 c4 D a1 a2 a3 a4 h : ℝ)
    (_hK0 : K0 > 0) (_hM0 : M0 > 0) (_hc0 : c0 > 0)
    (_hK1 : K1 > 0) (_hM1 : M1 > 0) (_hc1 : c1 > 0)
    (hK2 : K2 > 0) (hM2 : M2 > 0) (hc2 : c2 > 0)
    (_hK3 : K3 > 0) (_hM3 : M3 > 0) (_hc3 : c3 > 0)
    (hK4 : K4 > 0) (hM4 : M4 > 0) (hc4 : c4 > 0)
    (hh : h > 0)
    (h_denom2 : M2 + c2 * a3 > 0)
    (h_denom4_base : M4 + c4 * (D - a1 - a2 - a4 - a3 - 2*h) > 0)
    : secondDiff
      (fun b => splitFunction5PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 K4 M4 c4 D a1 a2 b a4)
      a3 h < 0 := by
  have h_kernel :
      secondDiff
        (splitFunctionCoordSliceCont
          K2 M2 c2 K4 M4 c4 D (a1 + a2 + a4)
          (cpmmOutputCont K0 M0 (c0 * a1) +
            cpmmOutputCont K1 M1 (c1 * a2) +
            cpmmOutputCont K3 M3 (c3 * a4)))
        a3 h < 0 := by
    apply splitFunctionCoordSliceCont_concave
    · exact hK2
    · exact hM2
    · exact hc2
    · exact hK4
    · exact hM4
    · exact hc4
    · exact hh
    · exact h_denom2
    · convert h_denom4_base using 1
      ring

  have h_eq :
      secondDiff
        (splitFunctionCoordSliceCont
          K2 M2 c2 K4 M4 c4 D (a1 + a2 + a4)
          (cpmmOutputCont K0 M0 (c0 * a1) +
            cpmmOutputCont K1 M1 (c1 * a2) +
            cpmmOutputCont K3 M3 (c3 * a4)))
        a3 h =
      secondDiff
        (fun b => splitFunction5PoolCont K0 M0 c0 K1 M1 c1 K2 M2 c2 K3 M3 c3 K4 M4 c4 D a1 a2 b a4)
        a3 h := by
    unfold secondDiff splitFunctionCoordSliceCont splitFunction5PoolCont cpmmOutputCont
    ring

  rw [← h_eq]
  exact h_kernel

-- **Informal Note: K-Pool Generalization Principle** (NOT a checked theorem).
--
-- The k-pool split function F(a1, ..., a_{k-1}) = sum_i f_i(c_i * a_i) has
-- coordinate-wise negative second forward difference because:
--
-- 1. Only 2 pools change per coordinate step (pool j increasing, pool k-1 decreasing)
-- 2. Each changing pool's contribution is negative by `cpmmOutputCont_secondDiff_neg`
-- 3. The sum of two negative numbers is negative
--
-- This principle extends the 2-pool proof strategy to any k >= 2. The checked
-- `splitFunctionCoordSliceCont_concave` theorem proves the two-changing-pool
-- coordinate kernel, `splitFunctionListCoordSliceCont_concave` proves a
-- List-sum bridge for arbitrary fixed non-moving pools,
-- `fixedPoolInputSumCont_perm`, `fixedPoolOutputSumCont_perm`,
-- `splitFunctionListCoordSliceCont_eq_of_perm_fixed`, and
-- `splitFunctionSelectedListOrderedCoordSliceCont_concave_of_perm_fixed`
-- prove that the fixed-pool compression is invariant under fixed-pool
-- permutations. `UnorderedSelectionCertificateCont`,
-- `unorderedSelectionCertificate_full_eq`,
-- `unorderedSelectionCertificate_fixed_perm`,
-- `splitFunctionUnorderedSelectionCertCoordSliceCont_eq_listCoordSliceCont`,
-- and `splitFunctionUnorderedSelectionCertCoordSliceCont_concave` package that
-- transfer as a proof-carrying unordered/List presentation certificate, and
-- `unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont`,
-- `unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont`,
-- `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_activeBeforeRemainderIndex`,
-- and `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_remainderBeforeActiveIndex`
-- construct and consume that certificate from full-list ordered-index
-- witnesses for both selected-pair orders. `IdentifiedFixedPoolTermCont`,
-- `identifiedPoolTermsCont_perm`,
-- `IdentifiedActiveBeforeRemainderSelectionCont`,
-- `IdentifiedRemainderBeforeActiveSelectionCont`,
-- `unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont`,
-- `unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont`,
-- `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedActiveBeforeRemainder`,
-- and `splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedRemainderBeforeActive`
-- add an identity-stable full-list presentation bridge for duplicate-valued
-- pools. `splitFunctionSelectedListCoordSliceCont_concave` plus
-- `splitFunctionSelectedListOrderedCoordSliceCont_concave` prove explicit
-- selected-list decomposition witness bridges, including both active/remainder
-- orders. `selectedFullPoolListCont_eq_take_drop_of_lt` proves the
-- active-before-remainder arbitrary-index List reconstruction bridge, and
-- `selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt`
-- proves the remainder-before-active order-tagged reconstruction bridge.
-- `selectedActiveIndexOrderedCont_lt`,
-- `selectedRemainderIndexOrderedCont_lt`,
-- `selectedFullPoolListOrderedCont_get_active`,
-- `selectedFullPoolListOrderedCont_get_remainder`, and
-- `selectedActiveIndexOrderedCont_ne_remainderIndex` prove concrete
-- index-witness facts for those explicit decompositions.
-- `selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed`
-- proves a bounded removal/projection bridge for those same supplied
-- decompositions. `selectedFullPoolListCont_erase_active_then_remainder_eq_take_drop_of_lt`
-- and
-- `selectedFullPoolListOrderedCont_remainderBeforeActive_erase_active_then_remainder_eq_take_drop_of_lt`
-- prove the corresponding active-before and remainder-before arbitrary-index
-- List removal bridges. The concrete
-- `splitFunction4PoolCont_concave_coord2` plus
-- `splitFunction5PoolCont_concave_coord3` check concrete K > 3 instances.
-- The remaining full K theorem still needs unordered collection
-- canonicalization and Finset/Multiset quotient infrastructure.
--
-- **Non-claim**: This is an INFORMAL NOTE, not a checked theorem. The formal
-- checked theorems above cover k = 3 (coordinates 1 and 2), the abstract
-- coordinate-slice kernel, a List-sum fixed-pool bridge, one concrete k = 4
-- coordinate, one concrete k = 5 coordinate, explicit selected-list
-- decomposition witness bridges for both active/remainder orders, and concrete
-- index-witness plus active/remainder removal facts for those explicit
-- decompositions, and active-before-remainder plus remainder-before-active
-- arbitrary-index List reconstruction, removal, certificate-constructor, and
-- identity-stable presentation bridges. The full all-k top-level theorem still
-- requires deterministic unordered canonicalization and Finset/Multiset
-- quotient infrastructure. Do NOT cite this as a formal all-k proof.
--
-- The formal checked results are splitFunction3PoolCont_concave_coord1
-- and splitFunction3PoolCont_concave_coord2 (3-pool, both coordinates),
-- splitFunctionCoordSliceCont_concave, splitFunctionListCoordSliceCont_concave,
-- fixedPoolInputSumCont_perm, fixedPoolOutputSumCont_perm,
-- splitFunctionListCoordSliceCont_eq_of_perm_fixed,
-- splitFunctionSelectedListCoordSliceCont_concave,
-- splitFunctionSelectedListOrderedCoordSliceCont_concave,
-- splitFunctionSelectedListOrderedCoordSliceCont_eq_listCoordSliceCont_of_perm_fixed,
-- splitFunctionSelectedListOrderedCoordSliceCont_concave_of_perm_fixed,
-- UnorderedSelectionCertificateCont,
-- unorderedSelectionCertificate_full_eq,
-- unorderedSelectionCertificate_fixed_perm,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_eq_listCoordSliceCont,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_concave,
-- unorderedSelectionCertificateOfActiveBeforeRemainderIndexCont,
-- unorderedSelectionCertificateOfRemainderBeforeActiveIndexCont,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_activeBeforeRemainderIndex,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_remainderBeforeActiveIndex,
-- IdentifiedFixedPoolTermCont,
-- identifiedPoolTermsCont,
-- identifiedPoolTermsCont_perm,
-- IdentifiedActiveBeforeRemainderSelectionCont,
-- IdentifiedRemainderBeforeActiveSelectionCont,
-- identifiedActiveBeforeRemainderSelection_ids_distinct,
-- identifiedRemainderBeforeActiveSelection_ids_distinct,
-- unorderedSelectionCertificateOfIdentifiedActiveBeforeRemainderCont,
-- unorderedSelectionCertificateOfIdentifiedRemainderBeforeActiveCont,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedActiveBeforeRemainder,
-- splitFunctionUnorderedSelectionCertCoordSliceCont_concave_of_identifiedRemainderBeforeActive,
-- selectedFullPoolListCont_eq_take_drop_of_lt,
-- selectedFullPoolListOrderedCont_remainderBeforeActive_eq_take_drop_of_lt,
-- selectedActiveIndexOrderedCont_lt,
-- selectedRemainderIndexOrderedCont_lt,
-- selectedFullPoolListOrderedCont_get_active,
-- selectedFullPoolListOrderedCont_get_remainder,
-- selectedActiveIndexOrderedCont_ne_remainderIndex,
-- selectedFullPoolListOrderedCont_erase_active_then_remainder_eq_fixed,
-- selectedFullPoolListCont_erase_active_then_remainder_eq_take_drop_of_lt,
-- selectedFullPoolListOrderedCont_remainderBeforeActive_erase_active_then_remainder_eq_take_drop_of_lt,
-- splitFunction4PoolCont_concave_coord2, and splitFunction5PoolCont_concave_coord3.
