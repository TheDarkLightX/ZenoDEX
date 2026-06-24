# k-Pool Staircase Split Routing — Algorithm Design

## Problem

Given `k` parallel CPMM pools for the same asset pair, a total exact-in amount
`D`, and a leg cap `L`, choose integer allocations `a_1, ..., a_k` with
`Σ a_i = D` and at most `L` positive legs, maximizing:

```text
Σ f_i(a_i)
```

where each `f_i` is the v8 integer CPMM exact-in output (monotone nondecreasing
staircase in `a_i`). Tie-break: canonical leftmost (lexicographically smallest
sorted `(pool_id, amount)` leg tuple among equal-output optima).

## Current State

- Two-pool case: `staircase_exact` is exact, `O(B_0 * Q)` quotes, Lean-proven.
  Benchmark: 4,112 total quotes vs 80,010 for the default heuristic, 6/6 oracle
  parity.
- k-pool case (`split_routing_many_exact_in.py`):
  - Small domain (`D <= 512`): exact DP, `O(k * D^2)` time and space.
  - Larger domain: greedy step refinement, NOT exact.

## Key Insight: Dominated Staircase Representative

For CPMM exact-in, each `f_i` is a monotone integer staircase: between
consecutive jump points of `f_i`, the output is constant. Call pool `i`
*interior* at allocation `a_i` if `a_i` is strictly inside a plateau of `f_i`
(not at the plateau's left edge).

**Theorem (informal, mechanized in Lean):** For every feasible exact-budget
allocation, there exists a *staircase allocation* (non-interior pools at
jump-point left edges, one interior pool absorbing the residual) that spends
exactly D and weakly dominates it in total output. The optimizer searches the
finite staircase space and selects the canonical best, which is at least as
good as any feasible allocation.

**Proof sketch:** Given any feasible allocation, left-cover each non-interior
pool by a jump-point candidate with the same output (LeftCovers hypothesis).
The freed input is routed to the interior pool, whose output is monotone
nondecreasing, so total output weakly increases. Conservation holds because the
freed input equals the spent difference. This is mechanized as
`exists_dominated_staircase_representative` in `KPoolStaircase.lean`.

**Note on tie-break and plateaus:** The theorem proves *existence* of a
dominated staircase representative, not that every optimum has at most one
interior pool. Plateaus can create multiple tied optima with several
interior-looking allocations. The theorem guarantees that at least one of the
tied optima is a staircase allocation, which is sufficient for the optimizer to
find the optimal output value and the canonical-best route.

Formally, this is the k-pool generalization of the two-pool
`candidate_dominates_split` theorem in `SplitRoutingStaircase.lean`. The
two-pool proof fixes pool1 as the single "interior" pool (it receives
`D - a`, which need not be a jump point) and shows pool0's left-covering
candidate dominates. The k-pool version fixes one pool as the interior pool and
left-covers all others.

## Algorithm

```text
For each choice of interior pool j in {1..k} (and the "no interior" case):
  Enumerate the jump-point left edges B_i of every other pool i != j.
  For each combination of jump edges (c_i for i != j) with Σ c_i <= D:
    a_j = D - Σ c_i   (the residual goes to the interior pool)
    if a_j is feasible (>= min_valid_j, or 0 if pool j is unused):
      evaluate Σ f_i(c_i) + f_j(a_j)
  Track the canonical best.
Also evaluate the "no interior" case: all positive pools at jump edges,
  Σ c_i = D exactly (a special case of the above with a_j = 0).
```

## Complexity

Let `B_i` = number of jump points of pool `i` reachable by `D`, `Q` = one quote
cost, `k` = pool count, `L` = leg cap.

- Jump enumeration: `O(Σ B_i * Q)`.
- Combination enumeration (naive): `O(Π B_i)` per interior choice — too costly
  for large `k` or large `B_i`.
- **Pruned enumeration:** Use a DP over pools with state = total spent so far,
  keeping only Pareto-best (output, leg-tuple) per (legs_used, spent). This is
  `O(k * D * B_max)` where `B_max` is the largest breakpoint set, because each
  pool contributes at most `B_i` candidate amounts and we fold them into a
  spent-indexed table.

The DP is the same shape as the existing small-domain DP, but with per-pool
candidate sets restricted to jump points (size `B_i`) instead of all amounts in
`[1, D]` (size `D`). When pools are skewed, `B_i << D`, so this is much cheaper
than `O(k * D^2)`.

Worst case `B_i = D` (flat fee, tiny reserves) degrades to the existing DP
cost; we fall back to the existing exact DP in that regime.

## Determinism and Tie-Breaks

- Jump points are enumerated in increasing input order per pool.
- Pool processing order is canonical (sorted by `pool_id`).
- The DP keeps the lexicographically smallest leg tuple among equal-output
  states, matching the existing `best_small_domain_many_pool_exact_in` tie-break
  exactly.
- The interior-pool loop is ordered by `pool_id`; the canonical best is the
  minimum under the route key (output, then fewer legs, then lex legs).

## Safety and Fail-Closed

- All amounts validated as positive ints at the boundary.
- Duplicate pool_ids rejected before building any maps (fail-closed, matching
  the existing small-domain DP contract).
- Jump enumeration fail-closed on quote/formula drift: if the quote function
  rejects a requested output level (ValueError) or the reached output falls
  below the requested level (closed-form estimate drift), the enumeration
  raises ValueError. The adaptive entry point catches this and falls back to
  the existing small-domain DP. If no fallback is available, re-raises. This
  matches the two-pool staircase behavior: an "exact" solver must not silently
  lose optimality by returning a partial candidate set.
- No floats; all arithmetic is integer (including the breakpoint density
  estimator, which returns an integer count).
- No unbounded loops: jump enumeration is bounded by `D` (each jump advances
  output by at least 1, output is bounded by `y_i`), and the DP is bounded by
  `k * D * B_max`.
- Hard resource bounds with exact fallback: the staircase DP enforces
  `max_table_states`, `max_combine_pairs`, and `max_residual_quotes`. If any
  bound is exceeded, `ResourceLimitExceeded` is raised. The adaptive entry
  point catches this and falls back to the existing exact small-domain DP,
  preserving exactness. If no fallback is available, the exception propagates
  (fail-closed, no partial result). The bounds are set at structural ceilings:
  - `max_table_states = 2 * (max_legs+1) * (D+1)` (structural ceiling:
    `(max_legs+1) * (D+1)` distinct (legs_used, spent) keys)
  - `max_combine_pairs = 2 * D^2 * max_legs^2` (structural ceiling:
    `D^2 * max_legs^2` prefix x suffix candidate pairs)
  - `max_residual_quotes = 2 * D` (structural ceiling: `D` combined spent values)
- Online Pareto pruning during DP fold: during each fold, a candidate at
  (legs, spent) is skipped if an existing state at the same spent has <= legs
  and >= output (dominance). This is sound because any future extension of the
  dominated state would use more legs and produce less output than the same
  extension of the dominating state. This keeps the table smaller without
  losing exactness.

## Formal Verification

1. **Lean theorems (mechanized):** The file `KPoolStaircase.lean` proves:
   - `candidate_dominates_single_pool`: pool-by-pool dominance building block.
   - `candidate_dominates_two_pool_composition`: two-pool composition.
   - `candidate_dominates_three_pool_composition`: three-pool inductive step.
   - `candidate_dominates_k_pool_composition`: full arbitrary-k inductive
     composition by list induction, proving both dominance (weakly increases
     total output) and conservation (candidateSpent + improved_interior =
     originalSpent + original_interior).
   - `candidate_dominates_k_pool_with_budget`: budget-premise corollary that
     takes `originalSpent + a_interior = D` and returns `candidateSpent + r' = D`.
   - `exists_dominated_staircase_representative`: for every feasible exact-budget
     allocation, there exists a staircase allocation (non-interior pools at jump
     points, one interior pool absorbing the residual) that spends exactly D and
     weakly dominates it in total output. This is the stronger existence theorem.
   - `staircase_search_contains_optimum`: for any feasible allocation, there
     exists a staircase allocation that weakly dominates it. This establishes
     that the staircase search space always contains a representative at least
     as good as any feasible allocation.
   - Imported in `Proofs.lean` for aggregate build inclusion.
   - Scope: assumes `LeftCovers` hypotheses. The CPMM jump formula, canonical
     tie-break globality, and DP enumeration correctness are runtime-tested.
2. **Runtime parity tests:** Brute-force oracle parity on a hostile corpus
   (skewed reserves, high fees, dust edges, zero-output gaps, tie-heavy
   plateaus) for `k in {2, 3, 4}` and `D` up to a bounded limit. 40 tests
   including adaptive fallback, duplicate pool_id rejection, drift fail-closed
   behavior, and ResourceLimitExceeded fallback.
3. **Quote-count benchmark:** Compare against the existing greedy and
   small-domain DP.
4. **State-count and work-count profiling:** `tools/profile_state_counts.py`
   measures prefix/suffix state counts, Pareto-optimal state counts, combined
   state counts, transition attempts, combine pairs, and residual quotes across
   sparse, moderate, dense, and adversarial pool configurations. This data
   establishes the actual resource envelope and verifies that the hard bounds
   are well above actual usage.

## Negative Knowledge

Approaches considered and rejected, with reasons:

1. **State truncation by dropping states below a cap:** Unsound. Dropping
   non-Pareto-dominated states can lose the optimal solution. The only sound
   cap is one that triggers exact fallback or fail-closed rejection (which is
   what we implement via `ResourceLimitExceeded`).

2. **Post-fold Pareto filtering only (no online pruning):** Sound but
   suboptimal. The prefix/suffix tables grow large before the Pareto filter
   runs, wasting memory and transition work. Online Pareto pruning during the
   fold keeps tables smaller throughout, reducing both memory and time.

3. **Single forward DP instead of prefix/suffix decomposition:** A single
   forward DP over all pools does not cover the residual interior case (it
   cannot try each pool as the interior without re-running). The prefix/suffix
   decomposition buys reuse across interior choices at the cost of 2 passes
   instead of k+1. In memory and combine time, prefix/suffix can be worse than
   a single forward DP for small k, but the single DP alone does not cover the
   one-interior-pool search space.

4. **Adaptive fallback heuristic can choose the slower solver:** The Phase 1
   density estimate is a heuristic. It can underestimate breakpoint density,
   causing the staircase DP to run when the small-domain DP would be faster.
   It cannot cause an incorrect result: both solvers are exact, and
   `ResourceLimitExceeded` triggers fallback before any partial result is
   returned. The heuristic is conservative (sum of estimates, not max), so a
   single dense pool among many sparse ones does not trigger unnecessary
   fallback.

5. **Pareto filter soundness scope:** The Pareto filter is sound only for
   same-spent states and only while future feasibility depends on spent, legs
   remaining, and fixed remaining pools. If hidden constraints enter the state
   later (e.g., pool-specific minimum amounts that vary by context), the
   dominance relation must be revisited. The current implementation has no
   such hidden constraints: min_valid is fixed per pool and checked at the
   residual probe, not during the DP fold.

6. **The dominance theorem proves existence, not uniqueness:** The theorem
   shows that for every feasible allocation, there exists a staircase
   allocation that weakly dominates it. It does not prove that every optimum
   has at most one interior pool. Plateaus can create multiple tied optima
   with several interior-looking allocations. The theorem guarantees that at
   least one of the tied optima is a staircase allocation, which is sufficient
   for the optimizer to find the optimal output.

## Scope

This is an experimental prototype in a worktree. It does not change the live
route selector. Promotion to default requires the same evidence gates as the
two-pool staircase: runtime parity, performance, formal receipt, replay review.
