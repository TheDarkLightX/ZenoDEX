/-
# Window Bound for Ternary Search DP

This file proves results about the relationship between the continuous and
discrete optima of a concave Lipschitz function, which underpins the adaptive
window formula `W = ceil(C/L_min)` used in the ternary search DP.

## What can be proven from concavity + Lipschitz alone

1. **Floor proximity**: f(⌊b*⌋) ≥ f(b*) - L (the floor of the continuous
   optimum is L-optimal). This is the key lemma.

2. **Superlevel set structure**: For a concave function, the ε-superlevel set
   {b : f(b) ≥ f(b*) - ε} is a convex set (interval).

## What requires CPMM structure (not proven here)

The full window bound W = ceil(1/L) + 1 requires the specific CPMM split
function structure, not just general concavity + Lipschitz. The issue is that
a general concave function can be flat near the maximum (constant derivative
of 0), making the integer maximizer arbitrarily far from the continuous
maximizer. The CPMM function has strictly decreasing derivative (second
derivative is strictly negative), which prevents this degeneracy.

The empirical result (100% exactness with W = ceil(1/L) at C = 1.0) is
verified numerically in `window_bound_proof.py` but not formally proven here.
-/

import Mathlib.Tactic

open Real

/-- Lemma 1: For a Lipschitz function f with global max at b*,
    the floor of b* satisfies f(⌊b*⌋) ≥ f(b*) - L.

    Proof: |⌊b*⌋ - b*| ≤ 1 (floor is within 1 of its argument).
    By Lipschitz: |f(⌊b*⌋) - f(b*)| ≤ L * |⌊b*⌋ - b*| ≤ L.
    Since f(b*) is the max: f(⌊b*⌋) ≤ f(b*), so f(b*) - f(⌊b*⌋) ≤ L. -/
theorem concave_floor_L_optimal
    (f : ℝ → ℝ) (L : ℝ) (b_star : ℝ)
    (hL : L ≥ 0)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ L * |x - y|)
    (h_max : ∀ (b : ℝ), f b ≤ f b_star)
    : f ↑⌊b_star⌋ ≥ f b_star - L
  := by
  -- Key facts:
  -- 1. ↑⌊b_star⌋ ≤ b_star (floor_le)
  -- 2. b_star < ↑⌊b_star⌋ + 1 (lt_floor_add_one)
  -- 3. So 0 ≤ b_star - ↑⌊b_star⌋ < 1, hence |↑⌊b_star⌋ - b_star| ≤ 1
  -- 4. By Lipschitz: |f(↑⌊b*⌋) - f(b*)| ≤ L * |↑⌊b*⌋ - b*| ≤ L * 1 = L
  -- 5. By max: f(↑⌊b*⌋) ≤ f(b*), so f(b*) - f(↑⌊b*⌋) = |f(↑⌊b*⌋) - f(b*)| ≤ L
  -- 6. Therefore f(↑⌊b*⌋) ≥ f(b*) - L
  have h_floor_le : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
  have h_lt_succ : b_star < ↑⌊b_star⌋ + 1 := by
    have := Int.lt_floor_add_one b_star
    exact_mod_cast this
  -- |↑⌊b*⌋ - b*| = b* - ↑⌊b*⌋ (since ↑⌊b*⌋ ≤ b*)
  have h_abs_eq : |(↑⌊b_star⌋ : ℝ) - b_star| = b_star - ↑⌊b_star⌋ := by
    have h_neg : ↑⌊b_star⌋ - b_star ≤ 0 := by linarith
    rw [abs_of_nonpos h_neg]
    ring
  -- |↑⌊b*⌋ - b*| ≤ 1
  have h_dist_le_1 : |(↑⌊b_star⌋ : ℝ) - b_star| ≤ 1 := by
    rw [h_abs_eq]; linarith
  -- Lipschitz gives: |f(↑⌊b*⌋) - f(b*)| ≤ L * (b* - ↑⌊b*⌋) ≤ L * 1 = L
  have h_lip := h_lipschitz ↑⌊b_star⌋ b_star
  rw [h_abs_eq] at h_lip
  -- f(↑⌊b*⌋) ≤ f(b*) by max property
  have h_max_floor : f ↑⌊b_star⌋ ≤ f b_star := h_max ↑⌊b_star⌋
  -- |f(↑⌊b*⌋) - f(b*)| = f(b*) - f(↑⌊b*⌋) since f(↑⌊b*⌋) ≤ f(b*)
  have h_abs_f : |f ↑⌊b_star⌋ - f b_star| = f b_star - f ↑⌊b_star⌋ := by
    have h_neg : f ↑⌊b_star⌋ - f b_star ≤ 0 := by linarith
    rw [abs_of_nonpos h_neg]
    ring
  rw [h_abs_f] at h_lip
  -- Now h_lip: f b_star - f ↑⌊b_star⌋ ≤ L * (b_star - ↑⌊b_star⌋)
  -- And b_star - ↑⌊b_star⌋ ≤ 1, L ≥ 0, so L * (b_star - ↑⌊b_star⌋) ≤ L
  have h_prod_le : L * (b_star - ↑⌊b_star⌋) ≤ L := by
    nlinarith [hL, h_dist_le_1, h_abs_eq]
  -- Therefore f b_star - f ↑⌊b_star⌋ ≤ L
  linarith

/-- Lemma 2: For a concave function, the ε-superlevel set is convex.
    If f(a) ≥ f(b*) - ε and f(c) ≥ f(b*) - ε, then for any t ∈ [0,1],
    f(t*a + (1-t)*c) ≥ f(b*) - ε.

    This means the set of near-optimal points forms an interval, which is
    essential for the ternary search to work (unimodality). -/
theorem concave_superlevel_convex
    (f : ℝ → ℝ) (b_star : ℝ) (ε : ℝ)
    (h_concave : ∀ (x y : ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      f (t * x + (1 - t) * y) ≥ t * f x + (1 - t) * f y)
    (a c : ℝ) (t : ℝ)
    (h_t : 0 ≤ t ∧ t ≤ 1)
    (h_a : f a ≥ f b_star - ε)
    (h_c : f c ≥ f b_star - ε)
    : f (t * a + (1 - t) * c) ≥ f b_star - ε
  := by
  have h_conc := h_concave a c t h_t.1 h_t.2
  nlinarith [h_conc, h_a, h_c, h_t.1, h_t.2]

/-- Theorem: For a Lipschitz function f with max at b*,
    the floor ⌊b*⌋ is L-optimal: f(⌊b*⌋) ≥ f(b*) - L.

    For the CPMM split function with L < 1, this means the floor of the
    continuous optimum is within 1 of the true maximum (integer noise level).

    Combined with the numerical verification in window_bound_proof.py,
    this provides strong evidence that the adaptive window W = ceil(1/L)
    is sufficient for exact DP. -/
theorem floor_optimal_within_L
    (f : ℝ → ℝ) (L : ℝ) (b_star : ℝ)
    (hL : L ≥ 0)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ L * |x - y|)
    (h_max : ∀ (b : ℝ), f b ≤ f b_star)
    : f ↑⌊b_star⌋ ≥ f b_star - L
  := concave_floor_L_optimal f L b_star hL h_lipschitz h_max

/-- Corollary: For L ≤ 1, the floor of the continuous optimum is 1-optimal.
    f(⌊b*⌋) ≥ f(b*) - 1, within the integer rounding error.
    For the CPMM split function, L = y*(1-fee)/x is typically < 1. -/
theorem floor_optimal_within_1
    (f : ℝ → ℝ) (b_star : ℝ)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ 1 * |x - y|)
    (h_max : ∀ (b : ℝ), f b ≤ f b_star)
    : f ↑⌊b_star⌋ ≥ f b_star - 1
  := by
  apply concave_floor_L_optimal f 1 b_star (by linarith) h_lipschitz h_max

/-- **Ternary Search Window Sufficiency (Lipschitz + Concavity)**:
    For a concave Lipschitz function f with continuous optimum at b*,
    the floor ⌊b*⌋ is L-optimal: f(⌊b*⌋) ≥ f(b*) - L.

    This means the integer argmax n* satisfies f(n*) ≥ f(⌊b*⌋) ≥ f(b*) - L,
    so the integer optimum is within L of the continuous optimum in value.

    The tight window bound W = ⌈1/L⌉ (distance from ⌊b*⌋ to n*) requires
    CPMM-specific curvature analysis (strictly negative second derivative),
    which is proven in CpmmSplitConcavity.lean. The empirical verification
    is in window_bound_proof.py.

    **What is proven here** (from Lipschitz + concavity alone):
    1. f(⌊b*⌋) ≥ f(b*) - L  (floor is L-optimal)
    2. The ε-superlevel set is convex (interval)
    3. For L ≤ 1, f(⌊b*⌋) ≥ f(b*) - 1 (within integer rounding error)

    **What requires CPMM structure** (not proven from Lipschitz alone):
    - The tight distance bound |n* - ⌊b*⌋| ≤ ⌈1/L⌉
    - This needs the strictly negative second derivative from CpmmSplitConcavity.lean

    **Non-claim**: Lipschitz alone cannot bound |n* - b*| because a general
    Lipschitz function can be flat near the maximum (zero derivative), making
    the integer maximizer arbitrarily far from the continuous maximizer.
    The CPMM function's strictly negative second derivative prevents this. -/
theorem floor_L_optimal_implies_int_max_nearby
    (f : ℝ → ℝ) (L : ℝ) (b_star : ℝ) (n_star : ℤ)
    (hL : L > 0)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ L * |x - y|)
    (h_max_real : ∀ (b : ℝ), f b ≤ f b_star)
    (h_max_int : ∀ (n : ℤ), f ↑n ≤ f ↑n_star)
    : f ↑n_star ≥ f b_star - L ∧ f ↑n_star ≤ f b_star := by
  have h_floor_opt := concave_floor_L_optimal f L b_star (by linarith) h_lipschitz h_max_real
  have h_nstar_ge_floor : f ↑n_star ≥ f ↑⌊b_star⌋ := h_max_int ⌊b_star⌋
  have h_nstar_le : f ↑n_star ≤ f b_star := h_max_real ↑n_star
  exact ⟨by linarith, h_nstar_le⟩

/-- **Trivial Distance Bound**: For any integer n* and real b*,
    |n* - b*| ≤ |n* - ⌊b*⌋| + 1 (triangle inequality with floor).

    The tight bound |n* - b*| ≤ ⌈1/L⌉ requires CPMM-specific curvature. -/
theorem integer_argmax_trivial_bound
    (b_star : ℝ) (n_star : ℤ)
    : ↑n_star - b_star ≤ ↑(n_star - ⌊b_star⌋) + 1 ∧
      b_star - ↑n_star ≤ ↑(⌊b_star⌋ - n_star) + 1 := by
  have h_floor_le : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
  have h_lt_succ : b_star < ↑⌊b_star⌋ + 1 := by
    exact_mod_cast Int.lt_floor_add_one b_star
  have h_int_sub1 : ↑(n_star - ⌊b_star⌋) = (↑n_star : ℝ) - ↑⌊b_star⌋ := by
    exact_mod_cast rfl
  have h_int_sub2 : ↑(⌊b_star⌋ - n_star) = (↑⌊b_star⌋ : ℝ) - ↑n_star := by
    exact_mod_cast rfl
  rw [h_int_sub1, h_int_sub2]
  constructor
  · linarith
  · linarith
