# Cross-Pool Batch Clearing Research Note

## Status

The original CPSS-BC claim is falsified.

Claim tested:

```text
Output(greedy sequential current-reserve splitting) >= Output(two-phase decomposition)
```

This does not hold universally. The per-intent current-reserve split can be
locally optimal while leaving a worse reserve trajectory for later intents.
The useful result from the research run is the replacement oracle:

```text
Exact subset DP over processed-intent subsets and compressed reserve state.
```

That oracle is implemented as an advisory/research surface. It is not wired into
settlement and does not authorize state transitions.

## Falsifying Examples

Fixed-order counterexample:

```text
pools   = [(1, 2, 0), (2, 2, 0)]
intents = [1, 1, 2]

two-phase decomposition output = 2
greedy CPSS output             = 1
```

AB-order counterexample:

```text
pools   = [(1, 2, 0), (1, 6, 0)]
intents = [1, 2, 4]

two-phase decomposition output = 6
greedy CPSS output             = 5
```

These examples are small enough to replay by hand and are included in
`docs/research/cpss_bc_witness.py`.

## Corrected Algorithm

For two pools, define a DP state for each processed subset:

```text
dp[subset][(a0, y0r)] = best total output seen so far
```

Where:

- `subset` is the set of intents already processed;
- `a0` is total input routed to pool 0;
- `y0r` is pool 0's remaining output reserve.

Given `subset`, `a0`, `y0r`, and the retained `total_out`, the remaining pool 1
state is determined by conservation:

```text
x1r = x1 + processed_input(subset) - a0
y1r = y1 - total_out + (y0 - y0r)
```

The transition tries every unprocessed intent and every split of that intent's
exact-in amount across the two pools. This explores all orderings through the
subset lattice, without enumerating `n!` permutations directly.

## Compression Obligation

The compressed key omits `y1r`. If two paths collide on `(subset, a0, y0r)`,
the path with larger banked `total_out` has lower `y1r` by the same amount.
Future pool-1 output advantage for the discarded path is bounded by its extra
`y1r`, so retaining the larger `total_out` path is safe when:

```text
banked_output_delta >= y_reserve_delta
```

For this conservation-derived collision, the two deltas are equal. The focused
test suite includes a full-state oracle that keeps `(a0, y0r, y1r)` to pressure
this pruning rule.

## Complexity

Let:

- `n` be distinct intents;
- `D` be the split domain, roughly total input or maximum intent amount;
- `|S|` be the per-subset compressed state count;
- `k` be pool count.

Two-pool exact subset DP:

```text
O(2^n * n * |S| * D)
```

This removes the factorial ordering factor from brute force:

```text
brute force: O(n! * D^n)
subset DP:   O(2^n * n * |S| * D)
```

k-pool exact subset DP:

```text
O(2^n * n * |S_k| * D^(k-1))
```

The solver remains exponential in intent count and pseudo-polynomial in the
split domain. It is suitable as a bounded exact oracle, quality comparator, and
small-batch advisory engine.

## Implemented Surfaces

- Core oracle: `src/core/cross_pool_subset_dp.py`
- Advisory wrapper: `src/agents/cross_pool_subset_dp_advisor.py`
- CLI: `tools/cross_pool_subset_dp_advisor.py`
- Benchmark: `tools/benchmark_cross_pool_subset_dp.py`
- Core tests: `tests/core/test_cross_pool_subset_dp.py`
- Advisor tests: `tests/agents/test_cross_pool_subset_dp_advisor.py`
- Replay witness: `docs/research/cpss_bc_witness.py`

The advisory packet sets:

```text
production_security_claim = false
settlement_authority = false
solver_authorizes_settlement = false
```

If the exact search exceeds configured limits, the advisor returns
`status=exact_unavailable` and leaves exact output fields empty.

## Replay Evidence

Run:

```bash
python3 docs/research/cpss_bc_witness.py
pytest -q tests/core/test_cross_pool_subset_dp.py tests/agents/test_cross_pool_subset_dp_advisor.py
```

Current witness coverage:

```text
Known fixed-order counterexample: decomposition > greedy CPSS
Known AB-order counterexample:    decomposition > greedy CPSS
Subset DP vs brute force:         3-intent and 4-intent seeded corpora
Subset DP vs full-state oracle:   compressed-key collision pressure
k-pool DP vs brute force:         3, 4, and 5 pools on bounded corpora
Multi-set DP vs subset DP:        duplicate-heavy corpora
```

The witness is deterministic and hermetic. It is evidence for the bounded
modeled CPMM exact-in problem, not a production settlement claim.

## Promotion Boundary

Before any settlement integration, this needs a separate promotion path:

1. A versioned consensus contract for the exact modeled problem.
2. Differential replay against the current production batch-clearing path.
3. Full negative tests for reject-is-no-op and limit exhaustion.
4. Performance caps appropriate for live admission.
5. A proof or proof-carrying checker for the compressed-state pruning rule.

Until that exists, the subset-DP solver remains advisory.
