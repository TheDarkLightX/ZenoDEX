import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic
import Proofs.ZenoDEXExactOutBruteforceCompleteness

/-!
# Exact-Out Two-Pool Search Completeness

**ShapeForge promotion**: `exact_out_two_pool_completeness` (TESTED_ONLY → PROVED)

**THEOREM**: For two-pool exact-out routing with demand Q and per-pool capacity
bounds max₀, max₁, the integer interval `[Q - max₁, min(Q, max₀)]` captures
ALL feasible two-pool allocations. Combined with `ExactOutBruteforceCompleteness`,
this proves that brute-force search over the interval finds the unique canonical
optimum — no feasible allocation is missed.

## Key results (4 substantive + 4 helpers + 5 witnesses)

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `feasible_iff_in_interval` | Substantive | Biconditional: feasible ↔ in interval (from helpers 1a, 1b) |
| 2 | `two_pool_capacity_guard` | Substantive | Infeasibility ↔ lo > hi (biconditional, by-contra + witness) |
| 3 | `two_pool_canonical_exists` | Substantive | ∃! canonical optimum over feasible allocations (composition) |
| 4 | `two_pool_end_to_end` | Substantive | Capacity sufficiency → unique canonical winner (end-to-end) |
| 1a | `feasible_in_interval` | Helper | Completeness direction of (1) |
| 1b | `interval_is_feasible` | Helper | Soundness direction of (1) |
| 1c | `interval_nonempty_of_feasible` | Helper | Interval nonempty from witness |
| 1d | `two_pool_search_complete` | Helper | Membership + minimality over searchSet |

## Evidence chain
- `ZenoDEXExactOutCanonicalMinimizer.lean`: canonical key ordering, unique minimum
- `ZenoDEXExactOutBruteforceCompleteness.lean`: interval search → unique canonical
- `src/core/split_routing_dispatch.py:568-616`: Python implementation with same bounds
- This file: bridge from concrete bounds to abstract completeness (0 sorry)
-/

namespace TauSwap
namespace ZenoDEX
namespace ExactOutTwoPoolCompleteness

open ExactOutCanonicalMinimizer
open ExactOutBruteforceCompleteness

/-! ## Part 1: Feasible Interval Definition

For two-pool exact-out with demand Q and per-pool output capacities max₀, max₁:
- Pool 0 handles q₀ ∈ [0, max₀]
- Pool 1 handles q₁ = Q - q₀ ∈ [0, max₁]
- Feasibility: q₀ ≤ max₀ ∧ Q - q₀ ≤ max₁ ∧ q₀ ≤ Q

The search interval is [lo, hi] where lo = Q - max₁ (ℕ-truncated) and hi = min(Q, max₀).
In Python: `lo = max(0, Q - max1)`, `hi = min(Q, max0)`. -/

/-- Lower bound of the two-pool feasible interval.
    In ℕ, `Q - max₁` is already `max(0, Q - max₁)` by truncating subtraction. -/
def lo (Q max₁ : ℕ) : ℕ := Q - max₁

/-- Upper bound of the two-pool feasible interval. -/
def hi (Q max₀ : ℕ) : ℕ := min Q max₀

/-- A two-pool allocation q₀ is FEASIBLE when both pools are within capacity
    and the total output equals demand Q. -/
def Feasible (Q max₀ max₁ q₀ : ℕ) : Prop :=
  q₀ ≤ max₀ ∧ Q - q₀ ≤ max₁ ∧ q₀ ≤ Q

/-! ## Part 2: Completeness — All Feasible Allocations Are in the Interval -/

/-- COMPLETENESS: every feasible allocation q₀ lies in the search interval [lo, hi].
    This is the key theorem — it guarantees brute-force search misses nothing.

    Proof: `q₀ ≤ max₀` and `q₀ ≤ Q` give `q₀ ≤ hi`. For the lower bound,
    `Q - q₀ ≤ max₁` gives `Q - max₁ ≤ q₀` (in ℕ truncated subtraction). -/
theorem feasible_in_interval (Q max₀ max₁ q₀ : ℕ)
    (hfeas : Feasible Q max₀ max₁ q₀) :
    q₀ ∈ Finset.Icc (lo Q max₁) (hi Q max₀) := by
  simp [Feasible, lo, hi] at hfeas ⊢
  omega

/-- SOUNDNESS: every point in the search interval gives a feasible allocation.
    This is the converse — the interval doesn't include any infeasible points. -/
theorem interval_is_feasible (Q max₀ max₁ q₀ : ℕ)
    (hmem : q₀ ∈ Finset.Icc (lo Q max₁) (hi Q max₀)) :
    Feasible Q max₀ max₁ q₀ := by
  simp [Feasible, lo, hi] at hmem ⊢
  omega

/-- BICONDITIONAL: feasibility is EXACTLY membership in the search interval.
    The brute-force search is both complete (misses nothing) and sound (includes
    nothing infeasible). -/
theorem feasible_iff_in_interval (Q max₀ max₁ q₀ : ℕ) :
    Feasible Q max₀ max₁ q₀ ↔ q₀ ∈ Finset.Icc (lo Q max₁) (hi Q max₀) :=
  ⟨feasible_in_interval Q max₀ max₁ q₀, interval_is_feasible Q max₀ max₁ q₀⟩

/-! ## Part 3: Nonemptiness and Guard Correctness -/

/-- INTERVAL NONEMPTY: the search interval is nonempty whenever any feasible
    allocation exists. Equivalently: lo ≤ hi when feasible.

    Proof: from a witness q₀ that is feasible, it's in [lo, hi], so lo ≤ hi. -/
theorem interval_nonempty_of_feasible (Q max₀ max₁ q₀ : ℕ)
    (hfeas : Feasible Q max₀ max₁ q₀) :
    lo Q max₁ ≤ hi Q max₀ := by
  have hmem := feasible_in_interval Q max₀ max₁ q₀ hfeas
  simp at hmem
  omega

/-- CAPACITY GUARD: the allocation is infeasible for ALL q₀ precisely when
    the interval is empty (lo > hi). This matches the Python guard
    `if lo > hi: raise ValueError("no feasible split")`. -/
theorem two_pool_capacity_guard (Q max₀ max₁ : ℕ) :
    (∀ q₀ : ℕ, ¬Feasible Q max₀ max₁ q₀) ↔ hi Q max₀ < lo Q max₁ := by
  constructor
  · intro hall
    by_contra hle
    push_neg at hle
    -- The interval is nonempty, so lo is in it
    have : lo Q max₁ ∈ Finset.Icc (lo Q max₁) (hi Q max₀) := by
      simp; omega
    exact hall (lo Q max₁) (interval_is_feasible Q max₀ max₁ (lo Q max₁) this)
  · intro hlt q₀ hfeas
    have := interval_nonempty_of_feasible Q max₀ max₁ q₀ hfeas
    omega

/-! ## Part 4: Canonical Optimum via Composition

The key composition: `feasible_iff_in_interval` guarantees [lo, hi] captures
all feasible allocations. `ExactOutBruteforceCompleteness.witness_is_unique_canonical`
guarantees the interval search finds a unique canonical minimum.
Together: brute-force over [lo, hi] finds THE optimal allocation. -/

/-- CANONICAL OPTIMUM EXISTS: for any route key function over feasible
    two-pool allocations, there exists a UNIQUE canonical minimum.

    Proof: interval is nonempty (from feasibility witness) + Finset.Icc is
    finite + ExactOutBruteforceCompleteness.witness_is_unique_canonical. -/
theorem two_pool_canonical_exists {PoolId : Type} [LinearOrder PoolId]
    (routeKey : ℕ → Key PoolId) (Q max₀ max₁ : ℕ)
    (hfeas : ∃ q₀, Feasible Q max₀ max₁ q₀) :
    ∃! k, k ∈ searchSet routeKey (lo Q max₁) (hi Q max₀) ∧
      ∀ y ∈ searchSet routeKey (lo Q max₁) (hi Q max₀), k ≤ y := by
  obtain ⟨q₀, hq₀⟩ := hfeas
  have hLoHi := interval_nonempty_of_feasible Q max₀ max₁ q₀ hq₀
  have hS := searchSet_nonempty (routeKey := routeKey) hLoHi
  exact exists_unique_canonical (searchSet routeKey (lo Q max₁) (hi Q max₀)) hS

/-- SEARCH COMPLETENESS: if qStar minimizes routeKey over [lo, hi], then
    routeKey qStar is the canonical minimum over the search set (key-image of
    the interval). Combined with `feasible_iff_in_interval`, this means
    minimizing over the interval IS minimizing over all feasible allocations.

    Note: this theorem proves membership + minimality, not uniqueness. For
    the ∃! (existence + uniqueness) statement, see `two_pool_canonical_exists`. -/
theorem two_pool_search_complete {PoolId : Type} [LinearOrder PoolId]
    (routeKey : ℕ → Key PoolId) (Q max₀ max₁ qStar : ℕ)
    (hfeas : Feasible Q max₀ max₁ qStar)
    (hMin : ∀ q₀ ∈ Finset.Icc (lo Q max₁) (hi Q max₀),
      routeKey qStar ≤ routeKey q₀) :
    routeKey qStar ∈ searchSet routeKey (lo Q max₁) (hi Q max₀) ∧
      ∀ y ∈ searchSet routeKey (lo Q max₁) (hi Q max₀), routeKey qStar ≤ y := by
  have hRange := feasible_in_interval Q max₀ max₁ qStar hfeas
  exact witness_is_canonical hRange hMin

/-! ## Part 5: End-to-End Composition (Proof-Gated Acceptance)

Connects the capacity guard directly to the existence of a unique canonical
optimum. If pool capacities suffice (max₀ + max₁ ≥ Q), then brute-force
search over the feasible interval WILL find a unique canonical winner.

This is the "proof-gated acceptance" pattern: the capacity guard is a
sufficient condition for the router to produce a verifiable output. -/

/-- END-TO-END: if total capacity ≥ demand, a unique canonical optimum exists.
    Combines: capacity sufficiency → feasible witness → interval nonemptiness
    → canonical uniqueness. This is the formal justification for the Python
    pattern: `if cap_guard.passes(): run_search()` — the search always succeeds
    when the guard passes. -/
theorem two_pool_end_to_end {PoolId : Type} [LinearOrder PoolId]
    (routeKey : ℕ → Key PoolId) (Q max₀ max₁ : ℕ)
    (hCap : max₀ + max₁ ≥ Q) :
    ∃! k, k ∈ searchSet routeKey (lo Q max₁) (hi Q max₀) ∧
      ∀ y ∈ searchSet routeKey (lo Q max₁) (hi Q max₀), k ≤ y := by
  -- The capacity guard implies `lo` is a feasible allocation
  have hLoFeas : Feasible Q max₀ max₁ (lo Q max₁) := by
    simp [Feasible, lo]; omega
  exact two_pool_canonical_exists routeKey Q max₀ max₁ ⟨_, hLoFeas⟩

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: two pools with capacity 1000, demand 500. Interval = [0, 500]. -/
theorem witness_basic :
    lo 500 1000 = 0 ∧ hi 500 1000 = 500 ∧
    -- Every point in [0, 500] is feasible
    Feasible 500 1000 1000 0 ∧
    Feasible 500 1000 1000 250 ∧
    Feasible 500 1000 1000 500 := by
  simp [lo, hi, Feasible]

/-- Witness: asymmetric capacities. Pool 0 cap 100, pool 1 cap 300, demand 350.
    Interval = [50, 100] (pool 1 can absorb at most 300, so pool 0 gets ≥ 50). -/
theorem witness_asymmetric :
    lo 350 300 = 50 ∧ hi 350 100 = 100 ∧
    Feasible 350 100 300 50 ∧
    Feasible 350 100 300 100 ∧
    ¬Feasible 350 100 300 49 := by
  simp [lo, hi, Feasible]

/-- Witness: infeasible case. Pool caps 100 + 200 = 300, demand 400.
    lo = 200 > 100 = hi, so no feasible split exists. -/
theorem witness_infeasible :
    hi 400 100 < lo 400 200 ∧
    ¬Feasible 400 100 200 0 ∧
    ¬Feasible 400 100 200 100 ∧
    ¬Feasible 400 100 200 200 := by
  simp [lo, hi, Feasible]

/-- Witness: boundary case. Exact capacity match: 100 + 200 = 300, demand 300.
    Interval = [100, 100], only one feasible allocation. -/
theorem witness_exact_capacity :
    lo 300 200 = 100 ∧ hi 300 100 = 100 ∧
    Feasible 300 100 200 100 ∧
    ¬Feasible 300 100 200 99 ∧
    ¬Feasible 300 100 200 101 := by
  simp [lo, hi, Feasible]

/-- Witness: all output from one pool. Pool 0 cap 1000, pool 1 cap 0, demand 500.
    Interval = [500, 500]. Pool 0 must handle everything. -/
theorem witness_single_pool :
    lo 500 0 = 500 ∧ hi 500 1000 = 500 ∧
    Feasible 500 1000 0 500 ∧
    ¬Feasible 500 1000 0 499 := by
  simp [lo, hi, Feasible]

end ExactOutTwoPoolCompleteness
end ZenoDEX
end TauSwap
