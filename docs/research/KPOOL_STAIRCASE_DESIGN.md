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

## Key Insight: At Most One Interior Pool

For CPMM exact-in, each `f_i` is a monotone integer staircase: between
consecutive jump points of `f_i`, the output is constant. Call pool `i`
*interior* at allocation `a_i` if `a_i` is strictly inside a plateau of `f_i`
(not at the plateau's left edge).

**Theorem (informal):** In any optimal allocation, at most one pool is
interior. All other positive pools sit at a jump-point left edge of their own
staircase.

**Proof sketch:** Suppose pools `i` and `j` are both interior. Then
`f_i(a_i - δ) = f_i(a_i)` and `f_j(a_j - δ) = f_j(a_j)` for small `δ > 0`
(both sit in plateaus). Move `δ` from the pool with the smaller next-jump
marginal to the pool with the larger next-jump marginal. Total output weakly
increases; on a tie, the canonical leftmost tie-break strictly improves. So a
two-interior allocation cannot be the canonical optimum.

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
- Quote failures (ValueError) treated as infeasible, matching the existing
  `quote_for_pool_id` wrapper.
- No floats; all arithmetic is integer.
- No unbounded loops: jump enumeration is bounded by `D` (each jump advances
  output by at least 1, output is bounded by `y_i`), and the DP is bounded by
  `k * D * B_max`.

## Formal Verification Plan

1. **Lean theorem:** Generalize `candidate_dominates_split` to k pools. State:
   if every non-interior pool's allocation is left-covered by a jump candidate
   with the same output, and the interior pool's output is monotone, then the
   candidate combination dominates. This is the existing theorem applied
   pool-by-pool.
2. **Runtime parity tests:** Brute-force oracle parity on a hostile corpus
   (skewed reserves, high fees, dust edges, zero-output gaps, tie-heavy
   plateaus) for `k in {2, 3, 4}` and `D` up to a bounded limit.
3. **Quote-count benchmark:** Compare against the existing greedy and
   small-domain DP.

## Scope

This is an experimental prototype in a worktree. It does not change the live
route selector. Promotion to default requires the same evidence gates as the
two-pool staircase: runtime parity, performance, formal receipt, replay review.
