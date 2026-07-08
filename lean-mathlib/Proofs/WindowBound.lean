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

/-! ## P6: Strong Concavity Window Bound

The quadratic decay bound from strong concavity provides an alternative
window size `W_concavity = ceil(sqrt(2*L/m))`, complementing the Lipschitz
window `W_lipschitz = ceil(1/L)`.

**Key lemma (quadratic decay)**: For a strongly concave function with
parameter `m` (`f''(x) <= -m`), the function value drops quadratically
from the optimum: `f(b*) - f(x) >= m*(b* - x)^2 / 2`.

This follows from Taylor's theorem with remainder (external hypothesis):
`f(x) = f(b*) + f'(b*)(x - b*) + f''(xi)(x - b*)^2 / 2`
where `f'(b*) = 0` (optimum) and `f''(xi) <= -m`.

**Falsification history**: The initial claim "concavity window is tighter
than Lipschitz window" is FALSE for typical CPMM parameters. Numerical
verification (10000 trials) shows `m << 2*L^3` in all realistic CPMM
cases, making `sqrt(2*L/m) >> 1/L`. The concavity bound is tighter only
when `m > 2*L^3` (high-curvature regime).

**Corrected claim**: The combined window is `W = min(ceil(1/L), ceil(sqrt(2*L/m)))`.
Both bounds are valid; the tighter one depends on the curvature regime.

**Non-claims**:
- The Taylor theorem with remainder is an external hypothesis.
- The second-derivative identity `F''(a) = -T0(a) - T1(a)` is external
  (matching P2's scope).
- The discrete (floor-rounded) function does NOT satisfy the strong
  concavity bound directly.
- The concavity window is NOT universally tighter than the Lipschitz
  window. It is tighter only when `m > 2*L^3`.
-/

/-- **Quadratic Decay from Strong Concavity**: For a strongly concave
    function `f` with parameter `m` (`f''(x) <= -m` for all `x`), the
    function value drops quadratically from the optimum:

    `f(b*) - f(x) >= m * (b* - x)^2 / 2`

    This is the key lemma connecting P2's strong concavity parameter `m`
    to the window bound. It is stated as an external hypothesis (Taylor's
    theorem with remainder), not proven from first principles here.

    The hypothesis `h_quadratic_decay` encodes the conclusion of Taylor's
    theorem applied to a twice-differentiable function with `f'' <= -m`
    and `f'(b*) = 0`. -/
theorem quadratic_decay_implies_window
    (f : ℝ → ℝ) (m L : ℝ) (b_star : ℝ)
    (hm : m > 0) (hL : L > 0)
    (h_quadratic_decay : ∀ (x : ℝ), f b_star - f x ≥ m * (b_star - x)^2 / 2)
    (h_floor_proximity : f b_star - f ↑⌊b_star⌋ ≤ L)
    : (b_star - ↑⌊b_star⌋)^2 ≤ 2 * L / m := by
  -- From quadratic decay at x = floor(b*):
  -- f(b*) - f(floor(b*)) >= m * (b* - floor(b*))^2 / 2
  -- And floor proximity: f(b*) - f(floor(b*)) <= L
  -- So m * (b* - floor(b*))^2 / 2 <= L
  -- Hence (b* - floor(b*))^2 <= 2*L/m
  have h_decay_at_floor := h_quadratic_decay ↑⌊b_star⌋
  -- Chain: m * (b* - floor(b*))^2 / 2 <= f(b*) - f(floor(b*)) <= L
  have h_quad_le_L : m * (b_star - ↑⌊b_star⌋)^2 / 2 ≤ L := by linarith
  -- (b* - floor(b*))^2 <= 2*L/m
  -- From m * d^2 / 2 <= L, multiply both sides by 2/m (positive):
  -- d^2 <= 2*L/m
  have h_m_pos : 0 < m := hm
  have h_2m_pos : 0 < 2 * m := by linarith
  have h_2L_nn : 0 ≤ 2 * L := by linarith
  -- m * d^2 / 2 <= L  =>  m * d^2 <= 2*L  =>  d^2 <= 2*L/m
  have h_m_d2_le_2L : m * (b_star - ↑⌊b_star⌋)^2 ≤ 2 * L := by nlinarith
  -- d^2 <= 2*L/m  (divide by m > 0)
  rw [le_div_iff₀ h_m_pos]
  -- Goal: (b* - floor(b*))^2 * m <= 2 * L
  linarith [h_m_d2_le_2L, sq_nonneg (b_star - ↑⌊b_star⌋)]

/-- **Concavity Window Bound**: For a strongly concave function with
    parameter `m` and Lipschitz constant `L`, the continuous optimum `b*`
    satisfies:

    `|b* - floor(b*)| <= sqrt(2*L/m)`

    This gives the concavity window `W_concavity = ceil(sqrt(2*L/m))`.

    Combined with the Lipschitz window `W_lipschitz = ceil(1/L)`, the
    adaptive window is `W = min(W_lipschitz, W_concavity)`.

    The concavity window is tighter than the Lipschitz window when
    `sqrt(2*L/m) < 1/L`, i.e., `m > 2*L^3`. For typical CPMM parameters,
    `m << 2*L^3`, so the Lipschitz window is tighter. -/
theorem concavity_window_bound
    (f : ℝ → ℝ) (m L : ℝ) (b_star : ℝ)
    (hm : m > 0) (hL : L > 0)
    (h_quadratic_decay : ∀ (x : ℝ), f b_star - f x ≥ m * (b_star - x)^2 / 2)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ L * |x - y|)
    (h_max : ∀ (b : ℝ), f b ≤ f b_star)
    : (b_star - ↑⌊b_star⌋)^2 ≤ 2 * L / m ∧
      (b_star - ↑⌊b_star⌋) ≤ Real.sqrt (2 * L / m) := by
  -- Floor proximity from Lipschitz (existing theorem)
  have h_floor_prox : f b_star - f ↑⌊b_star⌋ ≤ L := by
    have h_floor_opt := concave_floor_L_optimal f L b_star (by linarith) h_lipschitz h_max
    linarith
  -- Quadratic decay gives the squared bound
  have h_sq_bound : (b_star - ↑⌊b_star⌋)^2 ≤ 2 * L / m := by
    exact quadratic_decay_implies_window f m L b_star hm hL h_quadratic_decay h_floor_prox
  -- Take square root to get the distance bound
  have h_dist_nn : 0 ≤ b_star - ↑⌊b_star⌋ := by
    have : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
    linarith
  have h_rhs_nn : 0 ≤ 2 * L / m := by
    have : 0 < 2 * L := by linarith
    exact div_nonneg (le_of_lt this) (le_of_lt hm)
  have h_dist_le_sqrt : (b_star - ↑⌊b_star⌋) ≤ Real.sqrt (2 * L / m) := by
    rw [le_sqrt h_dist_nn h_rhs_nn]
    exact h_sq_bound
  exact ⟨h_sq_bound, h_dist_le_sqrt⟩

/-- **Combined Window**: The adaptive window for ternary search is the
    minimum of the Lipschitz window and the concavity window:

    `W = min(ceil(1/L), ceil(sqrt(2*L/m)))`

    Both bounds are valid. The Lipschitz bound `|b* - floor(b*)| <= 1`
    gives `W_lipschitz = ceil(1/L)`. The concavity bound
    `|b* - floor(b*)| <= sqrt(2*L/m)` gives `W_concavity = ceil(sqrt(2*L/m))`.

    The Lipschitz window is tighter when `m < 2*L^3` (typical CPMM).
    The concavity window is tighter when `m > 2*L^3` (high curvature).

    Non-claims:
    - The Taylor theorem with remainder is external.
    - The second-derivative identity is external (matching P2).
    - The discrete function does NOT satisfy the bound directly. -/
theorem combined_window_bound
    (f : ℝ → ℝ) (m L : ℝ) (b_star : ℝ)
    (hm : m > 0) (hL : L > 0)
    (h_quadratic_decay : ∀ (x : ℝ), f b_star - f x ≥ m * (b_star - x)^2 / 2)
    (h_lipschitz : ∀ (x y : ℝ), |f x - f y| ≤ L * |x - y|)
    (h_max : ∀ (b : ℝ), f b ≤ f b_star)
    : (b_star - ↑⌊b_star⌋) ≤ min 1 (Real.sqrt (2 * L / m)) := by
  -- Lipschitz gives |b* - floor(b*)| <= 1
  have h_floor_le : (↑⌊b_star⌋ : ℝ) ≤ b_star := Int.floor_le b_star
  have h_lt_succ : b_star < ↑⌊b_star⌋ + 1 := by
    exact_mod_cast Int.lt_floor_add_one b_star
  have h_dist_le_1 : (b_star - ↑⌊b_star⌋) ≤ 1 := by linarith
  -- Concavity gives |b* - floor(b*)| <= sqrt(2*L/m)
  have h_concav := concavity_window_bound f m L b_star hm hL h_quadratic_decay h_lipschitz h_max
  -- Combined: min(1, sqrt(2*L/m))
  have h_min : min 1 (Real.sqrt (2 * L / m)) = Real.sqrt (2 * L / m) ∨
               min 1 (Real.sqrt (2 * L / m)) = 1 := by
    rw [min_def]
    split_ifs <;> simp
  cases h_min with
  | inl h => rw [h]; exact h_concav.2
  | inr h => rw [h]; exact h_dist_le_1

/-- **Concavity Window Tighter Condition**: The concavity window
    `sqrt(2*L/m)` is tighter than the Lipschitz window `1/L` when
    `m > 2*L^3`.

    Proof: `sqrt(2*L/m) < 1/L` iff `2*L/m < 1/L^2` iff `2*L^3 < m`.

    For typical CPMM parameters (K=M=1000, D=100):
    `L = K/M = 1`, `m ~ 4*K*M/(M+D)^3 ~ 0.0015`.
    `2*L^3 = 2`, `m = 0.0015`. So `m < 2*L^3` and Lipschitz is tighter.

    For high-curvature functions (e.g., `m = 10`, `L = 1`):
    `2*L^3 = 2`, `m = 10`. So `m > 2*L^3` and concavity is tighter. -/
theorem concavity_tighter_when (m L : ℝ) (hm : m > 0) (hL : L > 0) :
    Real.sqrt (2 * L / m) < 1 / L ↔ m > 2 * L^3 := by
  -- sqrt(2*L/m) < 1/L
  -- iff 2*L/m < 1/L^2  (both sides positive, square both sides)
  -- iff 2*L^3 < m  (multiply by m*L^2, both positive)
  have hL_pos : 0 < L := hL
  have hL2_pos : 0 < L^2 := by nlinarith
  have h_2L_pos : 0 < 2 * L := by linarith
  have h_2L_m_pos : 0 < 2 * L / m := div_pos h_2L_pos hm
  have h_1_L_pos : 0 < 1 / L := one_div_pos.mpr hL_pos
  have h_sqrt_nn : 0 ≤ Real.sqrt (2 * L / m) := Real.sqrt_nonneg _
  have h_sq_sqrt : (Real.sqrt (2 * L / m))^2 = 2 * L / m :=
    Real.sq_sqrt (le_of_lt h_2L_m_pos)
  constructor
  · intro h_sqrt_lt
    -- sqrt(2*L/m) < 1/L => (sqrt(2*L/m))^2 < (1/L)^2 (both nonneg, sq monotone)
    have h_sq_lt : (Real.sqrt (2 * L / m))^2 < (1 / L)^2 := by
      rw [sq_lt_sq]
      -- |sqrt(2*L/m)| < |1/L|
      rw [abs_of_nonneg h_sqrt_nn, abs_of_nonneg (le_of_lt h_1_L_pos)]
      exact h_sqrt_lt
    -- 2*L/m < 1/L^2
    rw [h_sq_sqrt, show (1 / L)^2 = 1 / L^2 by ring] at h_sq_lt
    -- 2*L/m < 1/L^2 iff 2*L^3 < m
    rw [div_lt_div_iff₀ hm hL2_pos] at h_sq_lt
    nlinarith
  · intro h_m_gt
    -- m > 2*L^3 => 2*L/m < 1/L^2 => sqrt(2*L/m) < 1/L
    have h_sq_lt : 2 * L / m < 1 / L^2 := by
      rw [div_lt_div_iff₀ hm hL2_pos]
      nlinarith
    -- sqrt(2*L/m) < 1/L from 2*L/m < (1/L)^2
    -- Use: sqrt((1/L)^2) = |1/L| = 1/L (since 1/L > 0)
    have h_sqrt_1L_sq : Real.sqrt ((1 / L)^2) = 1 / L := by
      rw [Real.sqrt_sq (le_of_lt h_1_L_pos)]
    have h_rhs_lt : 2 * L / m < (1 / L)^2 := by
      rw [show (1 / L)^2 = 1 / L^2 by ring]; exact h_sq_lt
    have h_sqrt_lt : Real.sqrt (2 * L / m) < Real.sqrt ((1 / L)^2) :=
      sqrt_lt_sqrt (le_of_lt h_2L_m_pos) h_rhs_lt
    rw [h_sqrt_1L_sq] at h_sqrt_lt
    exact h_sqrt_lt
