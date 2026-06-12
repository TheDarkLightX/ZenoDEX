import Proofs.GaloisSplitCertificate
import Proofs.CPMMOutputMonotonicity
import Mathlib.Tactic

/-!
# CPMM Output Discrete Concavity and Zero-Fee Split Routing Certificate

Connects the abstract `GaloisSplitCertificate` to a zero-fee CPMM split objective.

The CPMM output function `cpmmOut(x, y, a) = y * a / (x + a)` (floor division)
has **nearly discretely concave** first differences in the trade amount `a`:

  cpmmOut(x, y, a+2) + cpmmOut(x, y, a) ≤ 2 * cpmmOut(x, y, a+1) + 1

The bound +1 is tight (achieved when floor rounding shifts the value), as
demonstrated by the `witness_second_diff_tight` example.

## Algebraic core

The continuous function h(a) = y*a/(x+a) has second difference:
  h(a+2) + h(a) - 2*h(a+1) = -2*y*x / [(x+a)*(x+a+1)*(x+a+2)] ≤ 0

Floor division can perturb each value by at most 1, but a clean contradiction
argument shows the integer second difference is at most +1 (not +2):
the assumption q₂+q₀ ≥ 2*q₁+2 forces q₁ ≥ y, contradicting the output-bounded-
by-reserve property when x > 0.

## Split routing connection

For specific pool configurations where the zero-fee split objective IS
discretely concave (verified computationally for each instance), the
`GaloisSplitCertificate` gives O(1) optimality verification. The
`cpmm_zero_fee_split_certificate_sound` theorem bridges the abstract
certificate to the concrete zero-fee split-routing problem.

## Part I: CPMM Concavity Analysis

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `sq_neighbors` | Core | n*(n+2) ≤ (n+1)^2 (algebraic core of concavity) |
| 2 | `cpmmOut_mono` | Bridge | cpmmOut monotone (via swapOut_mono_amount) |
| 3 | `cross_mul_concavity` | Core | Continuous concavity after clearing denominators |
| 4 | `cpmmOut_second_diff_le_one` | Main | Integer second difference ≤ 1 (unconditional) |
| 5 | `split_concave_of_concave` | Core | Sum of DiscreteConcave functions is DiscreteConcave |
| 5'| `discrete_concave_reverse` | Core | Reversal a ↦ f(D-a) preserves discrete concavity |
| 5"| `split_objective_concave` | Bridge | f(a)+g(D-a) concave when both f,g concave |
| 5‴| `cpmm_zero_fee_split_second_diff_le_two` | Main | Zero-fee CPMM split obj Δ² ≤ 2 |
| 6 | `cpmm_zero_fee_split_certificate_sound` | Bridge | GaloisSplitCertificate for zero-fee split obj |
| 7 | `witness_full_chain` | Witness | End-to-end: concavity + certificate + global optimality |

## Part II: NearlyDiscreteConcave — Graded Concavity Defect

New algebraic structure capturing the concavity defect as a graded invariant:

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 8 | `nearly_zero_iff_concave` | Bridge | Grade 0 ↔ DiscreteConcave |
| 9 | `nearly_sum` | Algebraic | Grade is additive under function sum |
| 10| `nearly_reverse` | Algebraic | Grade is invariant under index reversal |
| 11| `cpmmOut_nearly_concave` | Instantiation | CPMM output is grade 1 |
| 12| `cpmm_zero_fee_split_nearly_concave` | Derived | Zero-fee split obj grade 2 |
| 13| `nearly_right_delta_drift` | Novel | First-difference drift ≤ n*k per step |
| 14| `nearly_right_quadratic_bound` | Novel | Cumulative drift ≤ n*(n-1)*k/2 |
| 15| `cpmmOut_defect_tight` | Tightness | Grade 1 is tight (grade 0 fails) |
| 16| `cpmmOut_exact_concave_large` | Witness | High y/x pools achieve grade 0 |

## Part III: The Graded Certificate — Approximate Optimality Without Concavity

Part I's certificate (`cpmm_zero_fee_split_certificate_sound`) requires exact
`DiscreteConcave`, which the split objective does not satisfy in general
(see `witness_split_not_concave`); Part II proves it always has grade ≤ 2.
Part III closes the gap: the 2-comparison certificate applied to a grade-k
function certifies **approximate** global optimality with the explicit, tight
error `k·d·(d−1)/2` at distance `d`. The exact certificate is the `k = 0`
special case, so Parts I and II are unified under one theorem.

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 17| `nearly_left_quadratic_bound` | Core | Left-side cumulative drift via reversal symmetry |
| 18| `nearly_certificate_global_approx` | Main | Grade-k + 2 checks ⟹ 2·f(j) ≤ 2·f(a*) + k·d·(d−1) |
| 19| `nearly_certificate_global_max` | Corollary | k = 0 recovers the exact certificate |
| 20| `quadratic_grade_two` | Tightness | f(i)=i(i−1) has grade exactly 2 |
| 21| `approx_certificate_tight` | Tightness | f(i)=i(i−1) attains the bound with equality ∀ j |
| 22| `cpmm_zero_fee_split_certificate_approx` | Main | Universal CPMM split certificate (ALL pools, no concavity hypothesis) |
| 23| `witness_split_not_concave` | Witness | A pool pair where exact concavity FAILS |
| 24| `witness_approx_certificate_beyond_concavity` | Witness | The graded certificate still certifies that instance |

## Scope notes

The per-pool integer concavity bound (Theorem 4) does NOT imply the split
objective is `DiscreteConcave` (Part I's certificate needs per-instance
verification, and `witness_split_not_concave` exhibits a configuration where
concavity genuinely fails). Part III resolves this: the graded certificate
`cpmm_zero_fee_split_certificate_approx` applies to EVERY pool configuration
with no concavity hypothesis, at the cost of an explicit error term d·(d−1)
that vanishes for adjacent candidates (d ≤ 1) and is provably unimprovable
(`approx_certificate_tight`).

This file does not model fee-adjusted runtime routing semantics. Any
fee-aware split-routing correctness claim needs a separate theorem surface.
-/

namespace Proofs
namespace CPMMConcavity

open AntiFragmentation (swapOut swapOut_mono_amount)

/-! ## Definition -/

/-- CPMM output: `y * a / (x + a)` using natural number floor division. -/
def cpmmOut (x y a : ℕ) : ℕ := y * a / (x + a)

/-- cpmmOut agrees with swapOut from AntiFragmentation. -/
theorem cpmmOut_eq_swapOut (x y a : ℕ) : cpmmOut x y a = swapOut x y a := by
  simp [cpmmOut, swapOut]

/-! ## Theorem 1: n*(n+2) ≤ (n+1)^2

The algebraic core. For n = x+a this says the denominator product at
positions a and a+2 exceeds the square at a+1, making first differences
of the continuous CPMM output decrease. -/

/-- **ALGEBRAIC CORE**: n*(n+2) ≤ (n+1)^2. AM-GM for consecutive integers. -/
theorem sq_neighbors (n : ℕ) : n * (n + 2) ≤ (n + 1) * (n + 1) := by
  nlinarith [sq_nonneg n]

/-- Non-vacuity: concrete values and tightness (gap = 1). -/
theorem witness_sq_neighbors :
    10 * 12 ≤ 11 * 11 ∧
    100 * 102 ≤ 101 * 101 ∧
    (11 * 11 - 10 * 12 = 1) := by
  native_decide

/-! ## Theorem 2: cpmmOut monotone in trade amount

cpmmOut = swapOut (by definition), so monotonicity follows directly from
`swapOut_mono_amount` in AntiFragmentation.lean via the `cpmmOut_eq_swapOut` bridge. -/

/-- **MONOTONICITY**: cpmmOut is non-decreasing in the trade amount `a`.
    Derived from `swapOut_mono_amount` (AntiFragmentation.lean) via the
    `cpmmOut = swapOut` definitional bridge. -/
theorem cpmmOut_mono (x y : ℕ) {a₁ a₂ : ℕ} (h : a₁ ≤ a₂) :
    cpmmOut x y a₁ ≤ cpmmOut x y a₂ := by
  rw [cpmmOut_eq_swapOut, cpmmOut_eq_swapOut]
  exact swapOut_mono_amount x y a₁ a₂ h

/-- Monotonicity witness. -/
theorem witness_cpmmOut_mono :
    cpmmOut 1000 1000 50 ≤ cpmmOut 1000 1000 100 ∧
    cpmmOut 1000 1000 50 = 47 ∧
    cpmmOut 1000 1000 100 = 90 := by
  native_decide

/-! ## Basic bounds

Two elementary facts used throughout: zero input yields zero output, and the
output never exceeds the output reserve. -/

/-- cpmmOut at a=0 is always 0. -/
theorem cpmmOut_zero (x y : ℕ) : cpmmOut x y 0 = 0 := by
  simp [cpmmOut]

/-- cpmmOut is bounded by the output reserve. -/
theorem cpmmOut_le_reserve (x y a : ℕ) : cpmmOut x y a ≤ y := by
  simp only [cpmmOut]
  apply Nat.div_le_of_le_mul
  calc y * a ≤ y * (x + a) := Nat.mul_le_mul_left y (Nat.le_add_left a x)
    _ = (x + a) * y := by ring

/-! ## Theorem 3: Continuous concavity (cross-multiplication form)

The continuous CPMM output h(a) = y*a/(x+a) satisfies:
  h(a+2) + h(a) ≤ 2*h(a+1)

After clearing all three denominators, this becomes:
  y*(a+2)*(x+a)*(x+a+1) + y*a*(x+a+1)*(x+a+2) ≤ 2*y*(a+1)*(x+a)*(x+a+2)

The difference simplifies to 2*y*x ≥ 0 (always true). -/

/-- **CONTINUOUS CONCAVITY**: the cross-multiplication form of the
    concavity inequality for the continuous CPMM output. -/
theorem cross_mul_concavity (x y a : ℕ) :
    y * (a + 2) * ((x + a) * (x + a + 1)) + y * a * ((x + a + 1) * (x + a + 2))
      ≤ 2 * (y * (a + 1)) * ((x + a) * (x + a + 2)) := by
  nlinarith [sq_nonneg (x + a + 1), sq_neighbors (x + a)]

/-! ## Theorem 4: Integer second difference ≤ 1

The main technical theorem. For cpmmOut with x > 0:

  cpmmOut(x,y,a+2) + cpmmOut(x,y,a) ≤ 2*cpmmOut(x,y,a+1) + 1

The proof is by contradiction: assuming the second difference ≥ 2 leads to
q₁ ≥ y (via a chain of floor/ceil bounds and the sq_neighbors identity),
which contradicts the output-bounded-by-reserve property (q₁ ≤ y) when x > 0.

The bound +1 is tight: e.g., pool (100, 1000) at a=0 gives
  cpmmOut(100,1000,2) + cpmmOut(100,1000,0) = 19 + 0 = 19
  2*cpmmOut(100,1000,1) + 1 = 2*9 + 1 = 19. -/

/-- **INTEGER SECOND DIFFERENCE BOUND**: `Δ²f(a) ≤ 1` for cpmmOut,
    unconditionally (every x, including the degenerate empty-input-reserve
    pool x = 0, where the output saturates at y from a = 1 onward).

    Proof idea for x > 0: By contradiction. Assume q₂ + q₀ ≥ 2*q₁ + 2.
    1. Floor bounds: (q₂+q₀)*(d₀*d₂) ≤ n₂*d₀ + n₀*d₂
    2. Exact algebra: n₂*d₀ + n₀*d₂ + 2y = 2*n₁*d₁
    3. Ceil bound: 2*n₁ < (2*q₁+2)*d₁
    4. sq_neighbors: d₁² = d₀*d₂ + 1
    Combining: 2y + d₁ ≤ 2*q₁ + 2, and d₁ ≥ 2 (from x ≥ 1),
    so y ≤ q₁. But q₁ ≤ y (output bound), giving q₁ = y.
    Then y*d₁ ≤ y*(a+1), forcing d₁ ≤ a+1, i.e., x ≤ 0. Contradiction.

    For x = 0: cpmmOut 0 y (a+1) = y exactly, while both outer terms are
    ≤ y by the reserve bound, so the second difference is ≤ 0 ≤ 1. -/
theorem cpmmOut_second_diff_le_one (x y a : ℕ) :
    (cpmmOut x y (a + 2) : ℤ) + cpmmOut x y a ≤ 2 * cpmmOut x y (a + 1) + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · -- x = 0: the middle term equals y; both ends are ≤ y.
    have h1 : cpmmOut 0 y (a + 1) = y := by
      show y * (a + 1) / (0 + (a + 1)) = y
      rw [Nat.zero_add]
      exact Nat.mul_div_cancel y (Nat.succ_pos a)
    have h2 : cpmmOut 0 y (a + 2) ≤ y := cpmmOut_le_reserve 0 y (a + 2)
    have h0 : cpmmOut 0 y a ≤ y := cpmmOut_le_reserve 0 y a
    rw [h1]
    omega
  simp only [cpmmOut]
  set d₀ := x + a
  set d₁ := x + (a + 1)
  set d₂ := x + (a + 2)
  set n₁ := y * (a + 1)
  set q₀ := y * a / d₀
  set q₁ := n₁ / d₁
  set q₂ := y * (a + 2) / d₂
  suffices h : q₂ + q₀ ≤ 2 * q₁ + 1 by exact_mod_cast h
  by_contra hgt
  push_neg at hgt
  have hge : 2 * q₁ + 2 ≤ q₂ + q₀ := by omega
  -- Floor lower bounds
  have hf0 : q₀ * d₀ ≤ y * a := Nat.div_mul_le_self _ _
  have hf2 : q₂ * d₂ ≤ y * (a + 2) := Nat.div_mul_le_self _ _
  -- Floor upper bound (ceiling property)
  have hd1_pos : 0 < d₁ := by omega
  have hc1 : n₁ < q₁ * d₁ + d₁ := Nat.lt_div_mul_add hd1_pos
  -- Output bounded by reserve
  have hq1_le : q₁ ≤ y := by
    apply Nat.div_le_of_le_mul; show n₁ ≤ d₁ * y
    calc n₁ = y * (a + 1) := rfl
      _ ≤ y * d₁ := Nat.mul_le_mul_left y (by omega : a + 1 ≤ d₁)
      _ = d₁ * y := Nat.mul_comm y d₁
  -- Algebraic identities
  have hsq : d₀ * d₂ + 1 = d₁ * d₁ := by simp only [d₀, d₁, d₂]; ring
  have hcont : y * (a + 2) * d₀ + y * a * d₂ + 2 * y = 2 * n₁ * d₁ := by
    simp only [n₁, d₀, d₁, d₂]; ring
  -- Step 1: floor product bound
  have hstep1 : (q₂ + q₀) * (d₀ * d₂) ≤ y * (a + 2) * d₀ + y * a * d₂ := by
    have h1 : q₂ * d₂ * d₀ ≤ y * (a + 2) * d₀ := Nat.mul_le_mul_right d₀ hf2
    have h2 : q₀ * d₀ * d₂ ≤ y * a * d₂ := Nat.mul_le_mul_right d₂ hf0
    nlinarith
  -- Step 2: from assumption
  have hstep2 : (2 * q₁ + 2) * (d₀ * d₂) ≤ (q₂ + q₀) * (d₀ * d₂) :=
    Nat.mul_le_mul_right (d₀ * d₂) hge
  -- Step 3: combine with continuous concavity
  have hstep3 : (2 * q₁ + 2) * (d₀ * d₂) + 2 * y ≤ 2 * n₁ * d₁ := by linarith
  -- Step 4: d₁² decomposition
  have hstep5 : (2 * q₁ + 2) * d₁ * d₁ = (2 * q₁ + 2) * (d₀ * d₂) + (2 * q₁ + 2) := by
    nlinarith
  -- Step 5: ceiling bound gives 2*n₁*d₁ + d₁ ≤ (2*q₁+2)*d₁²
  have hstep6 : 2 * n₁ * d₁ + d₁ ≤ (2 * q₁ + 2) * (d₀ * d₂) + (2 * q₁ + 2) := by
    have h4a : 2 * n₁ + 1 ≤ (2 * q₁ + 2) * d₁ := by linarith
    nlinarith
  -- Step 6: derive y ≤ q₁
  have hstep7 : 2 * y + d₁ ≤ 2 * q₁ + 2 := by linarith
  have h_yle : y ≤ q₁ := by omega
  -- Step 7: q₁ = y (combined with hq1_le)
  have heq : q₁ = y := by omega
  -- Step 8: floor gives y*d₁ ≤ y*(a+1), so d₁ ≤ a+1, so x ≤ 0
  have habs : q₁ * d₁ ≤ n₁ := Nat.div_mul_le_self n₁ d₁
  rw [heq] at habs
  by_cases hy : y = 0
  · have hq0z : q₀ = 0 := by simp [q₀, hy]
    have hq2z : q₂ = 0 := by simp [q₂, hy]
    omega
  · have : d₁ ≤ a + 1 := Nat.le_of_mul_le_mul_left habs (by omega : 0 < y)
    omega

/-- Tightness witness: second difference = 1 for pool (100, 1000) at a = 0. -/
theorem witness_second_diff_tight :
    -- g(0) = 0, g(1) = 9, g(2) = 19
    cpmmOut 100 1000 0 = 0 ∧
    cpmmOut 100 1000 1 = 9 ∧
    cpmmOut 100 1000 2 = 19 ∧
    -- Second diff = 19 + 0 - 2*9 = 1 (tight!)
    (cpmmOut 100 1000 2 : ℤ) + cpmmOut 100 1000 0 = 2 * cpmmOut 100 1000 1 + 1 := by
  native_decide

/-- For large pools, the second difference is typically 0 (exact concavity). -/
theorem witness_second_diff_zero :
    -- Pool (10000, 10000), a = 5: second diff = 0
    (cpmmOut 10000 10000 7 : ℤ) + cpmmOut 10000 10000 5
      = 2 * cpmmOut 10000 10000 6 := by
  native_decide

/-! ## Theorem 5: Sum of discretely concave functions is concave

The structural backbone of split routing: if each pool's output is discretely
concave (as an ℤ-valued function), then the total split output is too. -/

/-- **SUM CONCAVITY**: the sum of two DiscreteConcave functions is DiscreteConcave. -/
theorem split_concave_of_concave (f g : ℕ → ℤ) (D : ℕ)
    (hf : GaloisSplitCertificate.DiscreteConcave f D)
    (hg : GaloisSplitCertificate.DiscreteConcave g D) :
    GaloisSplitCertificate.DiscreteConcave (fun i => f i + g i) D := by
  intro i hi
  have hfi := hf i hi
  have hgi := hg i hi
  linarith

/-- Non-vacuity: sum of two concave parabolas is concave. -/
theorem witness_sum_concave :
    let f : ℕ → ℤ := fun x => -((x : ℤ) - 3) ^ 2
    let g : ℕ → ℤ := fun x => -((x : ℤ) - 7) ^ 2
    (f 0 + g 0 = -58) ∧
    (f 5 + g 5 = -8) ∧
    (f 6 + g 6 - (f 5 + g 5) ≤ f 5 + g 5 - (f 4 + g 4)) := by
  native_decide

/-! ## Theorem 5': Reversal preserves discrete concavity

The split objective `f(a) + g(D-a)` requires concavity of `g(D - ·)`.
Discrete concavity is invariant under index reversal because the
second-difference condition `Δ²f(i) ≤ 0` is symmetric: substituting
`j = D - i - 2` maps the reversed second difference back to the
original condition at position j. -/

/-- **REVERSAL PRESERVES CONCAVITY**: if f is discretely concave on {0,...,D},
    then `a ↦ f(D - a)` is also discretely concave on {0,...,D}.

    This is the index-reversal symmetry of the second-difference condition:
    Δ²f(D-i) = f(D-i-2) - 2f(D-i-1) + f(D-i) = Δ²f(j) where j = D-i-2. -/
theorem discrete_concave_reverse (f : ℕ → ℤ) (D : ℕ)
    (hf : GaloisSplitCertificate.DiscreteConcave f D) :
    GaloisSplitCertificate.DiscreteConcave (fun a => f (D - a)) D := by
  intro i hi
  show f (D - (i + 2)) - f (D - (i + 1)) ≤ f (D - (i + 1)) - f (D - i)
  set j := D - (i + 2) with hj_def
  have hj2 : j + 2 ≤ D := by omega
  have eq1 : D - i = j + 2 := by omega
  have eq2 : D - (i + 1) = j + 1 := by omega
  rw [eq1, eq2]
  linarith [hf j hj2]

/-- **SPLIT OBJECTIVE CONCAVITY**: for the split objective `f(a) + g(D-a)`,
    discrete concavity of both f and g on {0,...,D} implies discrete
    concavity of the split objective on {0,...,D}.

    Combines `split_concave_of_concave` (sum preserves concavity) with
    `discrete_concave_reverse` (reversal preserves concavity). This bridges
    per-pool concavity to the split routing objective. -/
theorem split_objective_concave (f g : ℕ → ℤ) (D : ℕ)
    (hf : GaloisSplitCertificate.DiscreteConcave f D)
    (hg : GaloisSplitCertificate.DiscreteConcave g D) :
    GaloisSplitCertificate.DiscreteConcave (fun a => f a + g (D - a)) D :=
  split_concave_of_concave f (fun a => g (D - a)) D hf (discrete_concave_reverse g D hg)

/-- Non-vacuity: split objective for f(a) = -a² and g(a) = -a² on {0,...,6}.
    Maximum at a = 3 (symmetric), obj(3) = -18, obj(0) = obj(6) = -36. -/
theorem witness_split_objective_concave :
    let f : ℕ → ℤ := fun a => -((a : ℤ) ^ 2)
    let g : ℕ → ℤ := fun a => -((a : ℤ) ^ 2)
    let obj : ℕ → ℤ := fun a => f a + g (6 - a)
    obj 3 = -18 ∧ obj 0 = -36 ∧ obj 6 = -36 ∧
    obj 3 ≥ obj 0 ∧ obj 3 ≥ obj 6 := by
  native_decide

/-! ## Zero-Fee CPMM Split Objective

The concrete function that the GaloisSplitCertificate is instantiated for:
total output from splitting `D` tokens across two CPMM pools in the zero-fee
algebraic model. -/

/-- The zero-fee CPMM split objective: total output from splitting `D` tokens
    across two pools, routing `a` to pool 0 and `D - a` to pool 1. -/
def cpmmZeroFeeSplitObj (x₀ y₀ x₁ y₁ D : ℕ) (a : ℕ) : ℤ :=
  (cpmmOut x₀ y₀ a : ℤ) + (cpmmOut x₁ y₁ (D - a) : ℤ)

/-! ## Theorem 5": CPMM split objective second-difference bound

The per-pool integer second difference is ≤ 1 (`cpmmOut_second_diff_le_one`).
Composing two pools in opposite directions (the split objective) gives a
second difference ≤ 2 (one from each pool). This partially bridges the
scope limitation: the split objective is "nearly concave" with bounded error. -/

/-- **CPMM SPLIT SECOND-DIFFERENCE BOUND**: The split objective
    `cpmmOut₀(a) + cpmmOut₁(D-a)` has integer second difference ≤ 2.

    Each pool contributes at most +1 to the second difference
    (by `cpmmOut_second_diff_le_one`), giving +2 total.
    When both pools are large, the bound is typically 0 (exact concavity). -/
theorem cpmm_zero_fee_split_second_diff_le_two (x₀ y₀ x₁ y₁ D : ℕ)
    (i : ℕ) (hi : i + 2 ≤ D) :
    cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (i + 2) + cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D i ≤
      2 * cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (i + 1) + 2 := by
  simp only [cpmmZeroFeeSplitObj]
  have h0 := cpmmOut_second_diff_le_one x₀ y₀ i
  have hb : D - (i + 2) + 2 = D - i := by omega
  have hb1 : D - (i + 2) + 1 = D - (i + 1) := by omega
  rw [← hb, ← hb1]
  have h1 := cpmmOut_second_diff_le_one x₁ y₁ (D - (i + 2))
  linarith

/-- Non-vacuity: the split second difference is -38 (strongly concave)
    for symmetric pools (1,100), well below the +2 bound. Shows the bound
    is conservative in practice. -/
theorem witness_split_second_diff :
    cpmmZeroFeeSplitObj 1 100 1 100 4 2 + cpmmZeroFeeSplitObj 1 100 1 100 4 0 ≤
      2 * cpmmZeroFeeSplitObj 1 100 1 100 4 1 + 2 := by
  native_decide

/-! ## Theorem 6: GaloisSplitCertificate for CPMM split routing

Connects `certificate_implies_global_max` to the concrete zero-fee CPMM split
objective `cpmmZeroFeeSplitObj`. When discrete concavity holds for a specific pool configuration
(verified per-instance), the 2-comparison certificate gives O(1) global optimality.
Boundary comparisons are unnecessary — they follow from concavity + neighbor checks. -/

/-- **ZERO-FEE CPMM SPLIT ROUTING CERTIFICATE SOUNDNESS**: when the zero-fee
    split objective `cpmmZeroFeeSplitObj` is discretely concave and the
    2 neighbor comparisons pass at `a_star`, then `a_star` is a global
    maximum over `{0, ..., D}`.

    This theorem is for the zero-fee algebraic model only. It is not a
    fee-aware runtime-routing correctness theorem. -/
theorem cpmm_zero_fee_split_certificate_sound
    (x₀ y₀ x₁ y₁ D a_star : ℕ)
    (ha : a_star ≤ D)
    (hconc : GaloisSplitCertificate.DiscreteConcave (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D)
    (h_prev : 0 < a_star → cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥ cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star - 1))
    (h_next : a_star < D → cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥ cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star + 1)) :
    ∀ j : ℕ, j ≤ D → cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥ cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D j :=
  GaloisSplitCertificate.certificate_implies_global_max
    (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D a_star ha hconc h_prev h_next

/-! ## Theorem 7: End-to-end witness

Complete proof chain: two identical pools (1, 10000), D = 6.
1. Verify discrete concavity by `interval_cases` + `native_decide`
2. Certificate passes at a* = 3 (symmetric pools → split evenly)
3. Global optimality follows from `cpmm_zero_fee_split_certificate_sound` -/

/-- Zero-fee split objective for the witness pools `(1, 10000)` with `D = 6`. -/
private def f_witness : ℕ → ℤ := cpmmZeroFeeSplitObj 1 10000 1 10000 6

/-- The split objective is discretely concave for pools (1,10000), D=6. -/
theorem witness_split_concavity :
    GaloisSplitCertificate.DiscreteConcave f_witness 6 := by
  intro i hi
  have hi' : i ≤ 4 := by omega
  simp only [f_witness, cpmmZeroFeeSplitObj, cpmmOut]
  interval_cases i <;> native_decide

/-- Certificate values at the optimal split a*=3. -/
theorem witness_certificate_values :
    -- Concrete output values
    f_witness 0 = 8571 ∧
    f_witness 3 = 15000 ∧
    f_witness 6 = 8571 ∧
    -- Certificate comparisons at a* = 3
    f_witness 3 ≥ f_witness 2 ∧
    f_witness 3 ≥ f_witness 4 ∧
    f_witness 3 ≥ f_witness 0 ∧
    f_witness 3 ≥ f_witness 6 := by
  simp only [f_witness, cpmmZeroFeeSplitObj, cpmmOut]
  native_decide

/-- **FULL CHAIN WITNESS**: `cpmm_zero_fee_split_certificate_sound` applied to
    concrete zero-fee pools. Two identical pools `(1, 10000)`, `D = 6`.
    Composes through theorem 6:
    1. Verify discrete concavity (witness_split_concavity)
    2. 2 neighbor checks at a* = 3 pass (native_decide)
    3. Global optimality follows — boundary checks f(0), f(6) are derived, not assumed -/
theorem witness_full_chain :
    -- Concavity
    GaloisSplitCertificate.DiscreteConcave f_witness 6 ∧
    -- Certificate at a* = 3 (only 2 neighbor checks needed)
    f_witness 3 ≥ f_witness 2 ∧ f_witness 3 ≥ f_witness 4 ∧
    -- Global optimality (via cpmm_zero_fee_split_certificate_sound)
    (∀ j, j ≤ 6 → f_witness 3 ≥ f_witness j) := by
  constructor
  · exact witness_split_concavity
  constructor
  · simp only [f_witness, cpmmZeroFeeSplitObj, cpmmOut]
    native_decide
  constructor
  · simp only [f_witness, cpmmZeroFeeSplitObj, cpmmOut]
    native_decide
  · -- Compose through theorem 6: only concavity + 2 neighbor checks.
    exact cpmm_zero_fee_split_certificate_sound 1 10000 1 10000 6 3
      (by omega)
      witness_split_concavity
      (by simp only [cpmmZeroFeeSplitObj, cpmmOut]; intro; native_decide)
      (by simp only [cpmmZeroFeeSplitObj, cpmmOut]; intro; native_decide)

/-! ## Non-vacuity witnesses -/

/-- Large pool witness: output values and concavity. -/
theorem witness_large_pool :
    cpmmOut 10000 10000 0 = 0 ∧
    cpmmOut 10000 10000 100 = 99 ∧
    cpmmOut 10000 10000 1000 = 909 ∧
    cpmmOut 10000 10000 10000 = 5000 := by
  native_decide

/-! ## Part II: NearlyDiscreteConcave — Graded Concavity Defect

CPMM output's integer second difference is bounded by 1, not 0. This
"concavity defect" is a first-class algebraic invariant:

| Property | Statement |
|----------|-----------|
| Grading  | `NearlyDiscreteConcave k f D` ↔ `∀ i, Δ²f(i) ≤ k` |
| Zero     | `NearlyDiscreteConcave 0` ↔ `DiscreteConcave` |
| Sum      | `grade(f+g) ≤ grade(f) + grade(g)` |
| Reversal | `grade(f ∘ rev) = grade(f)` |
| Monotone | `k₁ ≤ k₂ → grade-k₁ ⊆ grade-k₂` |

The main novel result is the **delta drift theorem**: under grade-k
concavity with a non-positive initial delta, subsequent deltas grow by
at most k per step. Combined with telescoping, this gives a tight
quadratic bound on how far a nearly-concave function can deviate from
the behavior of an exactly concave one.
-/

/-- Graded discrete concavity with defect k. Second differences bounded by k.
    Generalizes `DiscreteConcave` (k = 0) to capture floor-division errors.
    Forms a graded monoid under function addition:
    - Sum of grade-k₁ and grade-k₂ has grade k₁+k₂
    - Reversal preserves grade
    - k = 0 recovers exact discrete concavity -/
def NearlyDiscreteConcave (k : ℤ) (f : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ i, i + 2 ≤ D → f (i + 2) - f (i + 1) ≤ f (i + 1) - f i + k

/-- **GRADE-0 BRIDGE**: `NearlyDiscreteConcave 0` is exactly `DiscreteConcave`.
    Shows the graded structure is a genuine generalization: every theorem about
    `DiscreteConcave` transfers to the grade-0 case and vice versa. -/
theorem nearly_zero_iff_concave (f : ℕ → ℤ) (D : ℕ) :
    NearlyDiscreteConcave 0 f D ↔ GaloisSplitCertificate.DiscreteConcave f D := by
  simp only [NearlyDiscreteConcave, GaloisSplitCertificate.DiscreteConcave]
  constructor <;> intro h i hi <;> linarith [h i hi]

/-- **GRADE MONOTONICITY**: a tighter defect bound implies a looser one. -/
theorem nearly_mono_grade {k₁ k₂ : ℤ} (hle : k₁ ≤ k₂) {f : ℕ → ℤ} {D : ℕ}
    (h : NearlyDiscreteConcave k₁ f D) : NearlyDiscreteConcave k₂ f D :=
  fun i hi => by linarith [h i hi]

/-- **ADDITIVE COMPOSITION**: concavity defect is additive under function sum.
    Each pool contributes its own defect independently, and the total defect
    is their sum. This is the algebraic core of the split routing analysis.
    Proof: add the second-difference inequalities for f and g. -/
theorem nearly_sum (k₁ k₂ : ℤ) (f g : ℕ → ℤ) (D : ℕ)
    (hf : NearlyDiscreteConcave k₁ f D)
    (hg : NearlyDiscreteConcave k₂ g D) :
    NearlyDiscreteConcave (k₁ + k₂) (fun i => f i + g i) D := by
  intro i hi
  have := hf i hi; have := hg i hi
  show f (i + 2) + g (i + 2) - (f (i + 1) + g (i + 1)) ≤
       f (i + 1) + g (i + 1) - (f i + g i) + (k₁ + k₂)
  linarith

/-- **REVERSAL INVARIANCE**: index reversal preserves the concavity defect.
    Maps position i to j = D-i-2, reducing to the original condition at j.
    Combined with `nearly_sum`, this explains why the split objective
    `f(a) + g(D-a)` has defect = defect(f) + defect(g). -/
theorem nearly_reverse (k : ℤ) (f : ℕ → ℤ) (D : ℕ)
    (h : NearlyDiscreteConcave k f D) :
    NearlyDiscreteConcave k (fun a => f (D - a)) D := by
  intro i hi
  show f (D - (i + 2)) - f (D - (i + 1)) ≤ f (D - (i + 1)) - f (D - i) + k
  have eq1 : D - i = (D - (i + 2)) + 2 := by omega
  have eq2 : D - (i + 1) = (D - (i + 2)) + 1 := by omega
  rw [eq1, eq2]
  linarith [h (D - (i + 2)) (by omega : D - (i + 2) + 2 ≤ D)]

/-- **CPMM GRADE**: cpmmOut has concavity defect exactly 1 (grade 1),
    unconditionally in the pool parameters. Derived from
    `cpmmOut_second_diff_le_one` via the equivalence
    `Δ²f(i) ≤ 1` ↔ `NearlyDiscreteConcave 1`. -/
theorem cpmmOut_nearly_concave (x y D : ℕ) :
    NearlyDiscreteConcave 1 (fun a => (cpmmOut x y a : ℤ)) D := by
  intro i hi
  have := cpmmOut_second_diff_le_one x y i
  linarith

/-- **SPLIT GRADE (COMPOSITIONAL)**: CPMM split objective has grade 2,
    derived algebraically from per-pool grade-1 bounds.

    Proof chain:
    1. `cpmmOut₀` is grade 1 (`cpmmOut_nearly_concave`)
    2. `cpmmOut₁` is grade 1 (`cpmmOut_nearly_concave`)
    3. Reversed `cpmmOut₁` is grade 1 (`nearly_reverse`)
    4. Sum is grade 1+1 = 2 (`nearly_sum`)

    This compositional proof replaces the direct calculation in
    `cpmm_zero_fee_split_second_diff_le_two` with an algebraic derivation,
    showing the split bound of 2 is structurally inevitable (one
    defect unit per pool). -/
theorem cpmm_zero_fee_split_nearly_concave (x₀ y₀ x₁ y₁ D : ℕ) :
    NearlyDiscreteConcave 2 (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D := by
  intro i hi
  simp only [cpmmZeroFeeSplitObj]
  -- Pool 0 contributes defect 1
  have h0 := (cpmmOut_nearly_concave x₀ y₀ D) i hi
  -- Pool 1 (reversed) contributes defect 1
  have h1 := (nearly_reverse 1 (fun a => (cpmmOut x₁ y₁ a : ℤ)) D
    (cpmmOut_nearly_concave x₁ y₁ D)) i hi
  -- Total defect: 1 + 1 = 2
  linarith

/-- **DELTA DRIFT THEOREM**: Under grade-k concavity, if the first difference
    at position a is non-positive, then the first difference n steps later
    is at most n*k.

    This quantifies how fast a nearly-concave function's first differences
    can grow. For k = 0 (exact concavity), deltas stay non-positive forever,
    recovering `GaloisSplitCertificate.right_delta_chain`.

    Proof: induction on n. The concavity condition gives
    Δf(a+n+1) ≤ Δf(a+n) + k, and the IH gives Δf(a+n) ≤ n*k,
    so Δf(a+n+1) ≤ n*k + k = (n+1)*k. -/
theorem nearly_right_delta_drift (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n + 1 ≤ D) :
    f (a + n + 1) - f (a + n) ≤ ↑n * k := by
  induction n with
  | zero => simp; linarith
  | succ m ih =>
    have ihm := ih (by omega)
    have hc := hconc (a + m) (by omega)
    have e1 : a + (m + 1) + 1 = (a + m) + 2 := by omega
    have e2 : a + (m + 1) = (a + m) + 1 := by omega
    rw [e1, e2]
    push_cast
    linarith

/-- **QUADRATIC DRIFT BOUND**: Under grade-k concavity with non-positive
    initial delta, the cumulative drift over n steps satisfies:

      2 * (f(a+n) - f(a)) ≤ n * (n-1) * k

    For k = 0: f(a+n) ≤ f(a) (exact right monotonicity).
    For k = 1: f(a+n) ≤ f(a) + n*(n-1)/2 (quadratic error).

    The bound is tight: equality holds for f(i) = k*i*(i-1)/2.

    Proof: induction + telescoping. The delta drift gives Δf(a+j) ≤ j*k,
    and summing: f(a+n) - f(a) = Σ Δf(a+j) ≤ Σ j*k = k*n*(n-1)/2.
    Multiplying by 2 avoids integer division. -/
theorem nearly_right_quadratic_bound (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D)
    (h_base : f (a + 1) ≤ f a)
    (n : ℕ) (hn : a + n ≤ D) :
    2 * (f (a + n) - f a) ≤ ↑n * (↑n - 1) * k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have ihm := ih (by omega)
    have hdrift := nearly_right_delta_drift k f D a hconc h_base m (by omega)
    have e : a + (m + 1) = a + m + 1 := by omega
    rw [e]
    have hsplit : 2 * (f (a + m + 1) - f a) =
        2 * (f (a + m + 1) - f (a + m)) + 2 * (f (a + m) - f a) := by ring
    rw [hsplit]
    push_cast
    nlinarith

/-- **GRADE-1 TIGHTNESS**: cpmmOut is NOT grade 0 in general.
    Pool (100, 1000) at a = 0 has second difference exactly 1,
    so `NearlyDiscreteConcave 0` fails. This proves grade 1 is tight:
    no smaller defect bound holds universally for CPMM. -/
theorem cpmmOut_defect_tight :
    ¬ NearlyDiscreteConcave 0 (fun a => (cpmmOut 100 1000 a : ℤ)) 2 := by
  intro h
  have := h 0 (by omega)
  simp only [cpmmOut] at this
  norm_num at this

/-- **EXACT CONCAVITY FOR HIGH-RATIO POOLS**: Pool (100, 10000) achieves
    grade 0 (exact discrete concavity) on {0,...,5}.
    When the output reserve y is much larger than the input reserve x,
    the continuous concavity `2yx/[(x+a)(x+a+1)(x+a+2)]` dominates
    floor rounding, eliminating the defect entirely.
    Combined with `cpmmOut_defect_tight`, this shows that grade 0 depends
    on pool configuration: small y/x → defect 1, large y/x → defect 0. -/
theorem cpmmOut_exact_concave_large :
    NearlyDiscreteConcave 0 (fun a => (cpmmOut 100 10000 a : ℤ)) 5 := by
  intro i hi
  have : i ≤ 3 := by omega
  simp only [cpmmOut]
  interval_cases i <;> native_decide

/-- Non-vacuity: the delta drift bound is achieved.
    For f(a) = a² (NearlyDiscreteConcave 2, second diff = 2),
    with a = 3 and f(4) = 16 > f(3) = 9, the delta at step n = 1 is
    f(5) - f(4) = 9, and drift bound = 1 * 2 = 2. Actual drift = 9 - 7 = 2. -/
theorem witness_delta_drift :
    let f : ℕ → ℤ := fun a => (a : ℤ) ^ 2
    -- f is NearlyDiscreteConcave 2 (constant second diff = 2)
    (f 2 - f 1 ≤ f 1 - f 0 + 2) ∧
    (f 3 - f 2 ≤ f 2 - f 1 + 2) ∧
    -- With f(1) ≤ f(0) being false (1 > 0), use f(a) = -a² instead
    -- For f(a) = -(a-5)², starting at a=5 where f(6) ≤ f(5):
    -- delta drift at n=1: f(7)-f(6) = -4-(-1) = -3, bound = 1*(-2) = -2. Tight!
    let g : ℕ → ℤ := fun a => -((a : ℤ) - 5) ^ 2
    (g 6 ≤ g 5) ∧ (g 7 - g 6 = -3) := by
  native_decide

/-- Non-vacuity: quadratic bound for concave function.
    For g(a) = -(a-5)² with g(6) ≤ g(5), the quadratic bound gives:
    2*(g(8) - g(5)) ≤ 3*2*(-2) = -12. Actual: 2*(-9 - 0) = -18 ≤ -12. ✓ -/
theorem witness_quadratic_bound :
    let g : ℕ → ℤ := fun a => -((a : ℤ) - 5) ^ 2
    2 * (g 8 - g 5) ≤ 3 * (3 - 1) * (-2) ∧
    2 * (g 8 - g 5) = -18 ∧
    (3 : ℤ) * (3 - 1) * (-2) = -12 := by
  native_decide

/-! ## Part III: The Graded Certificate

The 2-comparison certificate, generalized from exact concavity (grade 0) to
arbitrary grade k. The certified point is globally optimal up to the explicit
error `k·d·(d−1)/2` at distance d — an error that is zero for adjacent
candidates, tight in general (`approx_certificate_tight`), and recovers the
exact certificate at k = 0.

The left-side bound is obtained from the right-side bound by the reversal
symmetry (`nearly_reverse`) rather than by a second induction: the reversed
function `b ↦ f(D−b)` has the same grade, the left neighbor check at `a`
becomes the right neighbor check at `D−a`, and positions `a−n` become
`(D−a)+n`. -/

/-- **LEFT QUADRATIC DRIFT BOUND** (by reversal symmetry): under grade-k
    concavity with a non-negative step into `a` from the left
    (`f (a-1) ≤ f a`), the cumulative drift looking leftward satisfies

      2 * (f (a-n) - f a) ≤ n * (n-1) * k.

    Proof: apply `nearly_right_quadratic_bound` to the reversed function
    `b ↦ f (D - b)` at position `D - a`; no new induction is needed. -/
theorem nearly_left_quadratic_bound (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (hconc : NearlyDiscreteConcave k f D) (haD : a ≤ D)
    (h_base : f (a - 1) ≤ f a)
    (n : ℕ) (hn : n ≤ a) :
    2 * (f (a - n) - f a) ≤ ↑n * (↑n - 1) * k := by
  have hg : NearlyDiscreteConcave k (fun b => f (D - b)) D := nearly_reverse k f D hconc
  have hgb : (fun b => f (D - b)) (D - a + 1) ≤ (fun b => f (D - b)) (D - a) := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · -- a = 0: both sides reduce to f 0
      have e1 : D - (D - 0 + 1) = 0 := by omega
      have e2 : D - (D - 0) = 0 := by omega
      simp only [e1, e2, le_refl]
    · have e1 : D - (D - a + 1) = a - 1 := by omega
      have e2 : D - (D - a) = a := by omega
      simpa only [e1, e2] using h_base
  have h := nearly_right_quadratic_bound k (fun b => f (D - b)) D (D - a) hg hgb n (by omega)
  have e3 : D - (D - a + n) = a - n := by omega
  have e4 : D - (D - a) = a := by omega
  simpa only [e3, e4] using h

/-- **THE GRADED CERTIFICATE** (main theorem of Part III): under grade-k
    concavity, the same 2 neighbor comparisons used by the exact certificate
    certify global optimality up to an explicit quadratic-in-distance error:

      ∀ j ≤ D,  2·f(j) ≤ 2·f(a) + k·d·(d−1)   where d = |j − a|.

    Consequences:
    * k = 0 (exact concavity): global maximality — the GaloisSplitCertificate
      theorem is the grade-0 instance (`nearly_certificate_global_max`).
    * d ≤ 1: the error vanishes — neighbors are exactly dominated at any grade.
    * The error is attained for every j by f(i) = k/2·i·(i−1)
      (`approx_certificate_tight` for k = 2), so the bound is unimprovable.

    No concavity of f is assumed beyond the grade bound; in particular this
    applies to the CPMM split objective (always grade ≤ 2) on configurations
    where exact discrete concavity FAILS. -/
theorem nearly_certificate_global_approx (k : ℤ) (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hconc : NearlyDiscreteConcave k f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1)) :
    ∀ j, j ≤ D →
      2 * f j ≤ 2 * f a + k * |(j : ℤ) - (a : ℤ)| * (|(j : ℤ) - (a : ℤ)| - 1) := by
  intro j hj
  rcases lt_trichotomy j a with hja | rfl | haj
  · -- j < a: left side at distance n = a - j (so a > 0 and h_prev applies)
    have hapos : 0 < a := by omega
    have habs : |(j : ℤ) - (a : ℤ)| = ((a - j : ℕ) : ℤ) := by
      rw [abs_sub_comm]
      have hcast : (a : ℤ) - (j : ℤ) = ((a - j : ℕ) : ℤ) := by
        omega
      rw [hcast]
      exact abs_of_nonneg (Int.natCast_nonneg _)
    have h := nearly_left_quadratic_bound k f D a hconc ha (h_prev hapos) (a - j) (by omega)
    have e : a - (a - j) = j := by omega
    rw [e] at h
    rw [habs]
    linarith
  · -- j = a: distance 0, error term vanishes
    simp
  · -- a < j: right side at distance n = j - a (so a < D and h_next applies)
    have haD : a < D := by omega
    have habs : |(j : ℤ) - (a : ℤ)| = ((j - a : ℕ) : ℤ) := by
      have hcast : (j : ℤ) - (a : ℤ) = ((j - a : ℕ) : ℤ) := by
        omega
      rw [hcast]
      exact abs_of_nonneg (Int.natCast_nonneg _)
    have h := nearly_right_quadratic_bound k f D a hconc (h_next haD) (j - a) (by omega)
    have e : a + (j - a) = j := by omega
    rw [e] at h
    rw [habs]
    linarith

/-- **GRADE-0 RECOVERY**: at k = 0 the graded certificate yields exact global
    maximality — the conclusion of
    `GaloisSplitCertificate.certificate_implies_global_max` — so the exact
    certificate is the grade-0 special case of the graded one (via
    `nearly_zero_iff_concave`, the hypotheses match as well). -/
theorem nearly_certificate_global_max (f : ℕ → ℤ) (D a : ℕ)
    (ha : a ≤ D)
    (hconc : NearlyDiscreteConcave 0 f D)
    (h_prev : 0 < a → f a ≥ f (a - 1))
    (h_next : a < D → f a ≥ f (a + 1)) :
    ∀ j, j ≤ D → f a ≥ f j := by
  intro j hj
  have h := nearly_certificate_global_approx 0 f D a ha hconc h_prev h_next j hj
  simp only [zero_mul, add_zero] at h
  linarith

/-- The quadratic f(i) = i·(i−1) has grade exactly 2 on every domain:
    its second difference is constantly 2. -/
theorem quadratic_grade_two (D : ℕ) :
    NearlyDiscreteConcave 2 (fun i => (i : ℤ) * ((i : ℤ) - 1)) D := by
  intro i hi
  push_cast
  ring_nf
  omega

/-- **TIGHTNESS OF THE GRADED CERTIFICATE**: for f(i) = i·(i−1) (grade 2),
    the certificate passes at a★ = 0 (f(0) = f(1) = 0) and the error bound
    holds with EQUALITY at every j:

      2·f(j) = 2·f(0) + 2·|j − 0|·(|j − 0| − 1).

    Hence the error term k·d·(d−1) in `nearly_certificate_global_approx`
    cannot be lowered at any single distance. -/
theorem approx_certificate_tight (j : ℕ) :
    2 * ((j : ℤ) * ((j : ℤ) - 1)) =
      2 * ((0 : ℤ) * ((0 : ℤ) - 1))
        + 2 * |(j : ℤ) - ((0 : ℕ) : ℤ)| * (|(j : ℤ) - ((0 : ℕ) : ℤ)| - 1) := by
  have habs : |(j : ℤ) - ((0 : ℕ) : ℤ)| = (j : ℤ) := by
    simp [abs_of_nonneg (Int.natCast_nonneg j)]
  rw [habs]
  ring

/-- **UNIVERSAL APPROXIMATE CERTIFICATE FOR ZERO-FEE CPMM SPLIT ROUTING**:
    for EVERY pool configuration `(x₀, y₀, x₁, y₁)` and budget `D` — with no
    concavity hypothesis and no per-instance verification — if the
    2-comparison certificate passes at `a★`, then `a★` is globally optimal up
    to `d·(d−1)` at distance d:

      ∀ j ≤ D,  obj(j) ≤ obj(a★) + |j − a★|·(|j − a★| − 1).

    This resolves the Part I scope limitation: `cpmm_zero_fee_split_certificate_sound`
    needs `DiscreteConcave`, which can FAIL (`witness_split_not_concave`);
    this theorem needs only the grade-2 bound, which ALWAYS holds
    (`cpmm_zero_fee_split_nearly_concave`). The error vanishes for adjacent
    candidates and is quadratic in the distance — in particular the certified
    point's neighbors never beat it, and any point beating it by more than
    d·(d−1) cannot exist. -/
theorem cpmm_zero_fee_split_certificate_approx
    (x₀ y₀ x₁ y₁ D a_star : ℕ) (ha : a_star ≤ D)
    (h_prev : 0 < a_star →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star - 1))
    (h_next : a_star < D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star ≥
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D (a_star + 1)) :
    ∀ j, j ≤ D →
      cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D j ≤
        cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D a_star
          + |(j : ℤ) - (a_star : ℤ)| * (|(j : ℤ) - (a_star : ℤ)| - 1) := by
  intro j hj
  have h := nearly_certificate_global_approx 2 (cpmmZeroFeeSplitObj x₀ y₀ x₁ y₁ D) D a_star
    ha (cpmm_zero_fee_split_nearly_concave x₀ y₀ x₁ y₁ D) h_prev h_next j hj
  linarith

/-- **EXACT CONCAVITY CAN FAIL**: for pools (1,100) and (100,1000) with D = 7,
    the zero-fee split objective is NOT discretely concave — the second
    difference at i = 5 is +1 (values: obj(5) = 102, obj(6) = 94, obj(7) = 87,
    so Δ(6) = −7 > Δ(5) = −8). Part I's exact certificate is therefore
    inapplicable to this configuration. -/
theorem witness_split_not_concave :
    ¬ GaloisSplitCertificate.DiscreteConcave (cpmmZeroFeeSplitObj 1 100 100 1000 7) 7 := by
  intro h
  have h5 := h 5 (by omega)
  simp only [cpmmZeroFeeSplitObj, cpmmOut] at h5
  norm_num at h5

/-- **THE GRADED CERTIFICATE GOES BEYOND CONCAVITY**: on the very
    configuration where exact concavity fails (`witness_split_not_concave`),
    the graded certificate still certifies a★ = 2 (obj = 113, the global
    maximum) within d·(d−1) — with only the same 2 neighbor comparisons. -/
theorem witness_approx_certificate_beyond_concavity :
    ∀ j, j ≤ 7 →
      cpmmZeroFeeSplitObj 1 100 100 1000 7 j ≤
        cpmmZeroFeeSplitObj 1 100 100 1000 7 2
          + |(j : ℤ) - (2 : ℤ)| * (|(j : ℤ) - (2 : ℤ)| - 1) := by
  have h := cpmm_zero_fee_split_certificate_approx 1 100 100 1000 7 2 (by omega)
    (by intro _; simp only [cpmmZeroFeeSplitObj, cpmmOut]; norm_num)
    (by intro _; simp only [cpmmZeroFeeSplitObj, cpmmOut]; norm_num)
  intro j hj
  simpa using h j hj

end CPMMConcavity
end Proofs
