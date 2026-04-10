import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation

/-!
# Exact-Out Many-Pool Capacity Guard

**world-model promotion**: `exact_out_capacity` (TESTED_ONLY → PROVED)

**THEOREM**: For exact-out routing with demand Q and n pools with per-pool
output capacities cap[i], a feasible allocation exists iff ∑ cap[i] ≥ Q.
The Python guard `if sum(top_caps[:max_legs]) < Q: raise ValueError`
is both sound (rejects only truly infeasible demands) and complete
(accepts all feasible demands).

The constructive direction builds an explicit greedy allocation
(fill pools in order up to capacity or remaining demand).

## Key results (4 substantive + 2 helpers + 7 witnesses)

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `greedyAlloc_le_cap` | Substantive | Greedy alloc respects all capacities (Fin induction) |
| 2 | `greedyAlloc_sum` | Substantive | Greedy alloc sums to Q when ∑ cap ≥ Q (Fin induction) |
| 3 | `infeasible_of_cap_lt` | Substantive | ∑ cap < Q → no feasible allocation (pigeonhole) |
| 4 | `capacity_guard_iff` | Substantive | Biconditional: infeasible ↔ ∑ cap < Q |
| 4a | `alloc_sum_le_cap_sum` | Helper | Pointwise ≤ lifts to sum ≤ (Finset.sum_le_sum) |
| 4b | `greedyAlloc_feasible` | Helper | Packages (1) + (2) into Feasible |

## Evidence chain
- `ZenoDEXExactOutTwoPoolCompleteness.lean`: Two-pool capacity guard (n=2 special case)
- `src/core/split_routing_dispatch.py:568-616`: Python implementation with same bounds
- This file: n-pool generalization with constructive greedy allocation (0 sorry)
-/

namespace TauSwap
namespace ZenoDEX
namespace ManyPoolCapacityGuard

open Finset

/-! ## Part 1: Definitions -/

/-- A many-pool allocation is feasible when each pool is within capacity
    and the total allocation equals the demand Q. -/
@[reducible] def Feasible (n : ℕ) (cap : Fin n → ℕ) (Q : ℕ) (alloc : Fin n → ℕ) : Prop :=
  (∀ i, alloc i ≤ cap i) ∧ (∑ i, alloc i) = Q

/-- Greedy allocation: fill each pool in index order up to its capacity
    or remaining demand, whichever is smaller.
    Matches the Python pattern: `for pool in sorted_pools: take = min(remaining, cap[pool])` -/
def greedyAlloc : (n : ℕ) → (Fin n → ℕ) → ℕ → (Fin n → ℕ)
  | 0, _, _ => Fin.elim0
  | _ + 1, cap, Q =>
    Fin.cons (min Q (cap 0)) (greedyAlloc _ (cap ∘ Fin.succ) (Q - min Q (cap 0)))

/-! ## Part 2: Infeasibility (Easy Direction) -/

/-- Any feasible allocation's total is bounded by total capacity.
    Proof: pointwise ≤ lifts to sum ≤ via `Finset.sum_le_sum`. -/
theorem alloc_sum_le_cap_sum {n : ℕ} {cap alloc : Fin n → ℕ}
    (hle : ∀ i, alloc i ≤ cap i) :
    (∑ i, alloc i) ≤ ∑ i, cap i :=
  Finset.sum_le_sum (fun i _ => hle i)

/-- INFEASIBILITY: no allocation exists when total capacity < demand.
    Proof: `alloc_sum ≤ cap_sum < Q` contradicts `alloc_sum = Q`. -/
theorem infeasible_of_cap_lt {n : ℕ} {cap : Fin n → ℕ} {Q : ℕ}
    (hlt : (∑ i, cap i) < Q) :
    ∀ alloc, ¬Feasible n cap Q alloc := by
  intro alloc ⟨hle, hsum⟩
  have := alloc_sum_le_cap_sum hle
  omega

/-! ## Part 3: Greedy Allocation Properties -/

/-- Each entry of the greedy allocation respects the corresponding pool capacity.
    Proof: by induction on n, using `Fin.cons_zero`/`Fin.cons_succ` to evaluate. -/
theorem greedyAlloc_le_cap : ∀ (n : ℕ) (cap : Fin n → ℕ) (Q : ℕ) (i : Fin n),
    greedyAlloc n cap Q i ≤ cap i := by
  intro n
  induction n with
  | zero => intro _ _ i; exact Fin.elim0 i
  | succ n ih =>
    intro cap Q i
    simp only [greedyAlloc]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]; omega
    · intro j; simp only [Fin.cons_succ]; exact ih _ _ j

/-- The greedy allocation sums to exactly Q whenever total capacity ≥ Q.
    Proof: by induction on n. Decompose the sum via `Fin.sum_cons`,
    show the tail capacity suffices for the reduced demand, then apply IH. -/
theorem greedyAlloc_sum : ∀ (n : ℕ) (cap : Fin n → ℕ) (Q : ℕ),
    (∑ i, cap i) ≥ Q → (∑ i, greedyAlloc n cap Q i) = Q := by
  intro n
  induction n with
  | zero =>
    intro _ Q hge
    simp [Finset.univ_eq_empty] at hge ⊢
    omega
  | succ n ih =>
    intro cap Q hge
    simp only [greedyAlloc]
    rw [Fin.sum_cons]
    -- Decompose the cap sum: cap 0 + ∑ tail
    have hdecomp : (∑ i : Fin (n + 1), cap i) = cap 0 + ∑ i : Fin n, cap (Fin.succ i) :=
      Fin.sum_univ_succ cap
    -- Tail capacity suffices for the reduced demand
    have hTailGe : (∑ i : Fin n, (cap ∘ Fin.succ) i) ≥ Q - min Q (cap 0) := by
      simp only [Function.comp]
      omega
    -- Apply IH to the tail
    have hTailSum := ih (cap ∘ Fin.succ) (Q - min Q (cap 0)) hTailGe
    omega

/-! ## Part 4: Feasibility and Biconditional Guard -/

/-- FEASIBILITY: greedy allocation is feasible when total capacity ≥ demand.
    Combines capacity bounds and sum correctness. -/
theorem greedyAlloc_feasible {n : ℕ} {cap : Fin n → ℕ} {Q : ℕ}
    (hge : (∑ i, cap i) ≥ Q) :
    Feasible n cap Q (greedyAlloc n cap Q) :=
  ⟨greedyAlloc_le_cap n cap Q, greedyAlloc_sum n cap Q hge⟩

/-- CAPACITY GUARD (biconditional): no feasible allocation exists if and only if
    total capacity is strictly less than demand.

    This matches the Python guard
    `if sum(top_caps[:max_legs]) < Q: raise ValueError("no feasible split")`.

    The guard is both SOUND (doesn't reject feasible demands) and
    COMPLETE (rejects all truly infeasible demands). -/
theorem capacity_guard_iff (n : ℕ) (cap : Fin n → ℕ) (Q : ℕ) :
    (∀ alloc, ¬Feasible n cap Q alloc) ↔ (∑ i, cap i) < Q := by
  constructor
  · intro hall
    by_contra hge
    push_neg at hge
    exact hall _ (greedyAlloc_feasible hge)
  · exact fun h => infeasible_of_cap_lt h

/-! ## Part 5: Specialization to Two Pools -/

/-- Two-pool capacity guard as a corollary of the n-pool theorem. -/
theorem two_pool_guard (c₀ c₁ Q : ℕ) :
    (∀ alloc : Fin 2 → ℕ, ¬Feasible 2 ![c₀, c₁] Q alloc) ↔ c₀ + c₁ < Q := by
  rw [capacity_guard_iff]
  simp [Fin.sum_univ_two]

/-! ## Part 6: Non-Vacuity Witnesses -/

/-- Witness: 3 pools, caps [100, 200, 300], demand 400. Feasible (600 ≥ 400). -/
theorem witness_feasible :
    Feasible 3 ![100, 200, 300] 400 ![100, 200, 100] := by
  native_decide

/-- Witness: 3 pools, caps [100, 200, 300], demand 700. Infeasible (600 < 700). -/
theorem witness_infeasible :
    ∀ alloc, ¬Feasible 3 ![100, 200, 300] 700 alloc := by
  apply infeasible_of_cap_lt
  native_decide

/-- Witness: boundary case. 3 pools, total capacity = demand exactly.
    One feasible allocation demonstrated: fill every pool to capacity. -/
theorem witness_boundary :
    Feasible 3 ![100, 200, 300] 600 ![100, 200, 300] := by
  native_decide

/-- Witness: 1 pool with cap = Q. Trivially feasible. -/
theorem witness_single_pool :
    Feasible 1 ![500] 500 ![500] := by
  native_decide

/-- Witness: 0 pools, demand 0. Trivially feasible (empty allocation). -/
theorem witness_zero_pools :
    Feasible 0 Fin.elim0 0 Fin.elim0 := by
  constructor
  · intro i; exact Fin.elim0 i
  · simp [Finset.univ_eq_empty]

/-- Witness: greedy allocation matches expected result for asymmetric pools. -/
theorem witness_greedy_matches :
    greedyAlloc 3 ![100, 200, 300] 250 0 = 100 ∧
    greedyAlloc 3 ![100, 200, 300] 250 1 = 150 ∧
    greedyAlloc 3 ![100, 200, 300] 250 2 = 0 := by
  native_decide

end ManyPoolCapacityGuard
end ZenoDEX
end TauSwap
