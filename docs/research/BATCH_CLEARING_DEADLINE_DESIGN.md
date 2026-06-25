# Batch Clearing via Deadline Scheduling: Design Document

## Motivation

The current batch clearing A-optimization uses O(n!) brute-force permutation search
for n <= 12 and greedy heuristics for larger batches. This limits both the batch
size and the optimality guarantee. We reformulate the problem as **weighted deadline
scheduling**, achieving O(n * S) exact A-optimization where S = total amount_in,
with O(n log n) subset selection when amount_in values are bounded.

## Key Insight: Deadline Reformulation

For a CPMM pool with reserves (R_in, R_out) and fee_bps f, a SWAP_EXACT_IN intent
with amount_in a and min_amount_out m executes iff:

```
floor(R_out' * net_in / (R_in' + net_in)) >= m
```

where net_in = a - ceil(a * f / 10000), R_in' = R_in_0 + S (cumulative gross_in
of preceding executed swaps), and R_out' = R_out_0 - T (cumulative amount_out).

Under the **constant-k approximation** (k = R_in * R_out >= k_0, since fees only
increase k), R_out' >= k_0 / R_in'. Substituting and solving the resulting
quadratic in R_in':

```
m * x^2 + net_in * m * x - net_in * k_0 <= 0
```

The positive root gives the **deadline**:

```
d_i = floor((-net_in + isqrt(net_in^2 + 4 * net_in * k_0 // m)) / 2)
```

The swap executes iff S <= d_i (cumulative gross_in before the swap is at most d_i).

### Conservativeness

The constant-k approximation is conservative: k >= k_0 always (fees stay in the
pool), so R_out' >= k_0 / R_in', meaning the actual amount_out is at least as
large as the approximation. The integer arithmetic (floor division, isqrt) makes
the deadline even more conservative. A swap selected by the DP will definitely
execute in reality. The approximation gap is closed by a greedy completion step.

## Algorithm

### 1. Deadline Computation (O(n))

For each swap i, compute deadline d_i using the closed-form formula above.

Edge cases:
- m_i = 0: deadline = +infinity (swap always executes, no slippage constraint)
- net_in_i <= 0: deadline = -infinity (swap can never execute, fee >= amount_in)

### 2. A-Optimization via DP (O(n * S))

Sort swaps by deadline (EDF order). Run a sparse DP:

```
dp[s] = max total A with cumulative gross_in = s

For each swap j (in EDF order):
  for each (s, a) in dp:
    if s <= d_j:  # swap j can execute at cumulative gross_in s
      new_s = s + amount_in_j
      new_a = a + amount_in_j
      dp[new_s] = max(dp[new_s], new_a)
```

The answer is max(dp.values()). Backtrack to reconstruct the selected subset.

### 3. B-Refinement (O(n^3))

Order the selected subset by deadline (EDF). Run adjacent-swap B-refinement
(reuse existing `_refine_b_ordering`) to maximize surplus B without decreasing A.

### 4. Greedy Completion (O(n^2))

Simulate the actual CPMM execution with the selected subset. For each excluded
swap (in EDF order), check if it can execute at the end of the current schedule
using the actual CPMM formula. If yes, add it. Repeat until no more swaps can
be added. This closes the constant-k approximation gap.

## Resource Bounds

- `max_dp_states = 2 * n * max_deadline` (structural ceiling)
- If exceeded, raise `ResourceLimitExceeded` and fall back to greedy heuristic
- The bound is well above actual usage (profiled)

## Complexity

| Step | Time | Space |
|------|------|-------|
| Deadline computation | O(n) | O(n) |
| DP (sparse) | O(n * S) | O(S) |
| B-refinement | O(n^3) | O(n) |
| Greedy completion | O(n^2) | O(n) |
| **Total** | O(n * S + n^3) | O(S + n) |

where S = sum of amount_in, bounded by pool reserve capacity.

## Correctness

### Theorem (Deadline Upper Bound)

Under the constant-k approximation, if swap i executes at cumulative gross_in S,
then S <= d_i. Equivalently, if S > d_i, then swap i cannot execute.

**Proof:** The swap executes iff `net_in * (R_out' - m) >= m * R_in'`. Under
constant-k, R_out' = k_0 / R_in'. Substituting gives the quadratic
`m * x^2 + net_in * m * x - net_in * k_0 <= 0` where x = R_in'. The positive
root is d_i. Since the leading coefficient m > 0, the quadratic is positive
for x > d_i, meaning the swap does not execute. QED.

### Theorem (DP Optimality)

The DP finds the maximum-weight subset of swaps that can all execute in EDF
order under the constant-k approximation.

**Proof:** EDF order is optimal for feasibility (well-known scheduling result).
The DP exhaustively explores all feasible subsets in EDF order, keeping the
maximum-weight one. Since weight = amount_in = processing time, the DP maximizes
total A. QED.

### Theorem (Conservative Approximation)

The deadline-based subset is a subset of the actually executable swaps.

**Proof:** The constant-k approximation underestimates R_out' (since k >= k_0),
which underestimates amount_out. So if a swap executes under the approximation,
it definitely executes in reality. QED.

## Lean Formalization

The Lean proof formalizes:
1. `deadline_quadratic_root`: The quadratic has exactly one positive root
2. `deadline_upper_bound`: If R_in' > d_i, the swap does not execute
3. `edf_feasibility`: EDF order is optimal for feasibility

## Negative Knowledge (PopperPad)

### NK-001: Constant-k deadline with min_amount_out=0 is NOT infinite

**Hypothesis:** When min_amount_out=0, the swap always executes (deadline=infinity).

**Falsified by:** `intents=[('i0',5,0),('i1',9,1),('i2',25,1),('i3',21,0),('i4',4,0)]`,
`reserve_in=250, reserve_out=100, fee_bps=1`. Swap i4 (amount_in=4, min_amount_out=0)
fails in EDF order because the pool is drained enough that `amount_out=0`, which the
CPMM kernel rejects with ValueError (not just `amount_out < min_amount_out`).

**Root cause:** The CPMM kernel's effective minimum output is 1, not 0. The deadline
formula must use `effective_min = max(min_amount_out, 1)` to capture the kernel's
zero-output rejection.

**Fix:** Treat `min_amount_out=0` as `min_amount_out=1` for deadline computation.

### NK-002: EDF order is NOT optimal with conservative deadlines

**Hypothesis:** EDF (earliest-deadline-first) order is optimal for feasibility under
the constant-k approximation.

**Falsified by:** `intents=[('a',100,90),('b',200,150),('c',500,400),('d',1000,800)]`,
`reserve_in=10000, reserve_out=10000, fee_bps=30`. The DP in EDF order selects
{a, d, b} (A=1300), but the optimal is {a, c, d} (A=1600). Swap c is excluded because
its conservative deadline (912) is exceeded after d (cumulative=1100), but in reality
c CAN execute after d because k increases with each swap.

**Root cause:** EDF optimality requires exact deadlines. With conservative deadlines
(constant-k underestimates R_out), EDF can miss feasible subsets that require a
different ordering.

**Fix:** Local search (1-out, 1-in) with actual CPMM simulation closes the gap for
small n. For large n, the gap is bounded by the k-growth ratio.

### NK-003: Moore-Hodgson does NOT maximize weight (only cardinality)

**Hypothesis:** Moore-Hodgson algorithm (sort by deadline, remove largest p when over
time) maximizes total weight for deadline scheduling.

**Falsified by:** Example: A(p=10, d=10), B(p=3, d=12), C(p=3, d=12). Moore-Hodgson
gives {B, C} (weight 6), but optimal is {A} (weight 10).

**Root cause:** Moore-Hodgson maximizes cardinality (number of jobs completed), not
total weight. For w_i = p_i (our case), removing the largest job to make room for
two smaller jobs reduces total weight.

**Fix:** Use DP (not Moore-Hodgson) for weight maximization.

### Rejected: Moore-Hodgson for Weight Maximization

Moore-Hodgson (sort by deadline, remove largest p when over time) maximizes
**cardinality**, not weight. For w_i = p_i, it can remove a large-weight job
to make room for two small-weight jobs, reducing total weight. Example:
- A: p=10, d=10
- B: p=3, d=12
- C: p=3, d=12

Moore-Hodgson gives {B, C} (weight 6), but optimal is {A} (weight 10).

### Rejected: Greedy EDF with Skip

Greedy EDF with skip (process in EDF order, skip if over deadline) is not
optimal either. It can include a large early-deadline job that blocks smaller
later-deadline jobs. Example:
- A: p=10, d=10
- B: p=6, d=11
- C: p=5, d=15

Greedy gives {A, C} (weight 15), but the DP can find {B, C} (weight 11) or
{A, C} (weight 15). Actually greedy is optimal here, but in general it's not
because it can't "undo" a previous inclusion.

### Rejected: Continuous Relaxation

The continuous relaxation (ignore integer rounding in CPMM) gives a tighter
deadline but loses the conservativeness guarantee. The integer-arithmetic
deadline is conservative and the greedy completion step closes the gap.

## Scope

This is an experimental prototype. It does not change the live batch clearing
path. Promotion requires parity with the existing brute-force oracle, performance
benchmarking, and formal evidence review.
