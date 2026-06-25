# AB Ordering DP Reformulation Note

Date: 2026-06-25

## Scope

This note records the current status of three proposed batch-clearing algorithm
reformulations:

1. Held-Karp-style DP for `optimal_ab_bounded`.
2. Bipartite matching for CoW pair netting.
3. Ternary or staircase search for two-pool exact-in split routing.

## Finding 1: Plain Held-Karp State Is Unsound

A one-state-per-subset DP is not exact for the current integer CPMM kernel.
The future state after a prefix is not determined by the subset of swaps that
has appeared in the prefix.

Counterexample:

```text
pool: reserve0 = 2, reserve1 = 8, fee_bps = 0
swap a: amount_in = 3, min_amount_out = 0
swap b: amount_in = 4, min_amount_out = 0

a then b leaves reserves (9, 3)
b then a leaves reserves (9, 2)
```

Both prefixes contain the same swap subset `{a, b}`, but the terminal reserve
state differs because integer CPMM rounding is order-sensitive. With nonzero
fees, order-sensitivity also appears in the continuous model because gross input
stays in reserves while net input drives the quote.

Consequence: an exact DP replacement for `_order_swaps_optimal_ab_bounded` must
carry terminal state, such as reserves and relevant sender balances, or prove a
narrower contract where subset state is sufficient. The safe shape is a
Pareto-state subset DP with explicit resource bounds, followed by brute-force
parity on small domains.

## Finding 2: CoW Matching Is Already Polynomial

The CoW exact uncoupled path already implements the clean bipartite-matching
reformulation:

- `_cow_exact_match_uncoupled`
- `_cow_max_weight_assignment`
- `cow_pair_netting_exact_uncoupled_v2`

The implementation uses deterministic Kuhn-Munkres assignment and keeps the
legacy CoW profile stable behind a versioned exact profile. The TR26-100 paper
(`Bipartite Matching is in NC`, 2026-06-14) is useful background for future
parallelization or formal complexity notes. The practical implementation should
continue to use the simpler assignment solver unless the runtime needs parallel
NC-style matching.

## Finding 3: Two-Pool Exact-In Split Has A Stronger Exact Path

The two-pool split route already has `staircase_v1`, an exact jump-enumeration
solver with brute-force parity tests and Lean-linked proof notes. For integer
CPMM outputs, the objective is a pair of monotone staircases, so a generic
ternary-search claim is weaker than the current staircase candidate-completeness
contract.

## Next Exact A Path

The highest-value remaining target is still AB ordering. A sound exact path
requires a Pareto-state DP:

```text
state := (placed_mask, reserves, sender_balances, A, B, order_ids)
transition := append one remaining intent and simulate the existing kernel
prune := keep only identical or proven-dominated terminal states
gate := exact brute-force parity for n <= 8 or n <= 10, then benchmark frontiers
```

That path can improve large-batch exact search if the Pareto frontier stays
small on real corpora. If the frontier grows toward factorial size, promotion
should focus on a bounded exact verifier plus stronger heuristics with clearly
scoped exactness claims.
