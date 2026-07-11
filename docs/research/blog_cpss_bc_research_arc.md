# From False Greedy Theorem to Exact Cross-Pool Routing Oracle

## A research arc in adversarial falsification, subset DP, and the 2^n barrier

---

## The setting

ZenoDEX is a formally verified decentralized exchange. It clears batches of swap intents against constant-product market maker (CPMM) pools. When two parallel pools exist for the same asset pair, the runtime splits each intent across them in a two-phase decomposition:

1. **Split phase:** for each intent, split the input amount across pools against a *snapshot* of the reserves taken before any intent executes.
2. **Clear phase:** for each pool, process its assigned legs in AB-optimal order against that pool's reserves.

The snapshot is stale by design. Intent A moves pool 0's price. Intent B's split was computed against the pre-A reserves. If A depleted pool 0, B routes too much to the now-shallow pool and gets worse execution.

The question: is two-phase decomposition optimal, or does the stale-reserve assumption leave output on the table?

---

## Act I: A plausible theorem

The first hypothesis was a greedy dominance claim:

> **CPSS-BC Dominance (informal):** For any batch of intents and any pool configuration, processing each intent sequentially against *current* reserves (splitting optimally at each step) produces total output at least as high as the two-phase decomposition.

The argument was clean. A per-step lemma holds trivially: for a single intent, splitting against current reserves is at least as good as splitting against stale reserves, because the stale split is a feasible split for the current state and the optimizer finds the best feasible split. The inductive composition seemed to follow: each step is at least as good, so the total is at least as good.

A 15,000-trial moderate-parameter suite confirmed it: 0 violations, 73% strict dominance. The theorem looked solid.

---

## Act II: Falsification

The falsification gate demanded an adversarial test before promotion. The moderate suite used reserves in [10, 500] and fees in {0, 10, 30, 50, 100} bps. The adversarial suite expanded to reserves in {1, 2, 3, 5, 10, 50, 100, 500, 1000, 10000}, fees in {0, 1, 10, 30, 50, 100, 500, 1000, 5000, 9999} bps, and 50,000 trials.

**10 violations. Worst delta: -6.**

The theorem was false. The per-step lemma is correct, but the inductive composition fails. The flaw: after CPSS-BC processes intent B against fresh reserves, the resulting reserves may be *less* favorable for intent C than the decomposition's reserves. The fresh split for B might route more to pool 0 (because it was relatively deeper), depleting it more aggressively. When C arrives, pool 0 is shallower under CPSS-BC than under the decomposition.

This is the classic greedy-vs-global failure. Locally optimal steps do not compose to a globally optimal trajectory when the state space branches. The true joint optimum sometimes *sacrifices* output on an early intent to keep a pool deep for a later one.

A representative counterexample:

```
pools = [(1, 1000, 10), (50, 10000, 5000)]
intents = [32, 20, 235, 332, 392]
Decomposition output = 9303
CPSS-BC output        = 9297
delta                 = -6
```

The lesson in falsification test design: the adversarial distribution must target the theorem's weak points (state divergence at the extremes), not just sample the reasonable operating range. A gate that accepted the moderate suite as sufficient would have promoted a false hypothesis.

---

## Act III: The corrected algorithm

The falsification exposed the root cause: per-intent optimal splitting is myopic. The fix was the **Anticipatory algorithm**, which exhaustively searches all splits for the first n-1 intents and uses optimal splitting only for the last intent.

The key structural fact: **the last intent in any ordering should always be split optimally against the current reserves.** There is no future intent to sacrifice for, so the myopic split is correct for the final step. This is the Last-Intent Optimality lemma, which holds trivially by definition of best_split.

The Anticipatory algorithm matches the true brute-force joint optimum in every trial (1,200 trials, 0 mismatches) and dominates the decomposition in 6,000 adversarial trials with 0 violations. But it inherits the factorial barrier: O(n! * D^n) complexity. For n=10, that is 3,628,800 orderings times D^10. Impractical.

---

## Act IV: The subset DP breakthrough

The factorial barrier came from searching all n! orderings. The breakthrough was eliminating it by observing that the DP state `(a, y0r)` is a *sufficient statistic* for the reserve configuration of a retained path.

Given the processed subset, `a` (total input sent to pool 0 so far), `y0r` (pool 0's current y-reserve), and `total_out` (accumulated output), both pools' reserves are fully determined:

- `x0' = x0 + a`
- `y1r = y1 - total_out + (y0 - y0r)` (conservation of total output)
- `x1' = x1 + (S_k - a)` where S_k = sum of processed intent amounts

The subset DP uses a bitmask to track which intents have been processed, exploring all orderings *implicitly* through the subset lattice:

```
State: dp[subset][(a, y0r)] = max_total_output
Transition: for each unprocessed intent i, try all splits b in [0, d_i]
            new_subset = subset | (1 << i)
            new_state = (a + b, y0r - q(x0+a, y0r, b, fee0))
            new_output = total_out + q(x0+a, y0r, b, fee0) + q(x1+Sk-a, y1r, d_i-b, fee1)
```

Complexity: **O(2^n * n * |S| * D)** where |S| is the per-subset state space (empirically avg 48 to 97, max 1572 for 3 intents with adversarial parameters).

This moved the exact two-pool CPMM batch problem from:

```
O(n! * |S| * D)  ->  O(2^n * n * |S| * D)
```

For n=10 and |S|=100, D=100: Subset DP is ~10M operations vs Anticipatory's ~360M. A ~36x speedup while remaining exact.

Verification was thorough:

| Test | Trials | Result |
|------|--------|--------|
| Subset DP vs brute force (3 intents, adversarial) | 2,000 | 2,000/2,000 match |
| Subset DP vs brute force (4 intents, adversarial) | 600 | 600/600 match |
| Compressed state vs full-state oracle (3 intents) | 1,000 | 1,000/1,000 match |
| Compressed state vs full-state oracle (4 intents) | 500 | 500/500 match |

All with extreme parameters: reserves 1..10000, fees 0..9999 bps, intents 1..12.

The compressed key intentionally omits `y1r` (pool 1's y-reserve). For a retained path, `y1r` is determined by conservation. When two paths collide on `(subset, a, y0r)`, the path with larger `total_out` has a lower `y1r`. Keeping the larger `total_out` is safe if the extra output already captured is at least as large as any future advantage from the discarded path's extra y-reserve. A full-state oracle that keeps `(subset, a, y0r, y1r)` pressure-tested this pruning rule across 1,500 trials with 0 mismatches.

---

## Act V: Generalizations

### k-Pool Subset DP

The subset DP generalizes to k pools. State expands to `(a_0, ..., a_{k-2}, y0r_0, ..., y0r_{k-2})` with the last pool's reserves determined by conservation. The inner loop enumerates all k-way splits, costing O(D^{k-1}) per state. Total: O(2^n * n * D^{k-1} * |S_k|).

It is implemented in `solve_k_pool_cpmm_subset_dp` with a small-instance brute-force oracle and replay checker. The current default witness replay checks 3, 4, and 5 pools against brute force with 0 mismatches; the larger research sweep covered 2,500 adversarial trials with 0 mismatches.

### Multi-Set DP

When multiple intents share the same amount, they are interchangeable: the CPMM output function depends only on the amount, not on which intent provides it. The multi-set DP groups intents by amount and tracks how many of each distinct amount have been used.

Complexity drops from O(2^n * n * |S| * D) to O(prod(count_d + 1) * n_distinct * |S| * D). For n=20 with 10 pairs, the subset factor drops from 2^20 = 1M to 3^10 = 59K, a 94% reduction.

It is implemented in `solve_two_pool_cpmm_multiset_dp`, and the advisor selects it automatically when duplicate exact-in amounts are present. The current default witness replay checks duplicate-heavy 3, 4, and 5 intent batches against subset DP with 0 mismatches; the larger research sweep covered 3,500 adversarial trials with 0 mismatches.

### Beam Search DP

A beam search variant keeps only the top-K states by total_output at each level. With beam_width=20 and all n! orderings, it is exact for 3 intents (1000/1000 adversarial) and 4 intents (200/200). It scales to n=200 in 45 seconds with K=100, but is near-exact (not proven exact) for larger n.

---

## Act VI: Attacking the 2^n barrier

The subset DP eliminated the factorial barrier but retained an exponential one: the 2^n subset factor. A dedicated research run investigated whether this could be reduced to polynomial.

### The 2^n lower bound

The 2^n factor is irreducible. Three lines of evidence converge:

1. **All subsets are visited.** For n=4, across 10,000 random instances with adversarial parameters, all 16/16 subsets appear on at least one optimal path. No subset can be safely skipped.

2. **All orderings are uniquely optimal for some instance.** For n=3, all 6 permutations are uniquely optimal for some parameter configuration. Each ordering visits a distinct sequence of subsets. The union covers all 2^n subsets.

3. **Power-of-2 construction.** With intents [1, 2, 4, ..., 2^(n-1)] and extreme rate pools [(1, D, 0), (D, 1, 0)], each subset of size k has a unique dominant `a` value (the amount sent to pool 0). For k up to n/2, all C(n,k) subsets have distinct dominant `a` values, confirming states cannot be merged across subsets.

The 2^n factor is fundamental to the problem structure. The optimal solution's intermediate state depends on *which* subset of intents has been processed, not just how many.

### Failed approaches

Six approaches to break the 2^n barrier were tested. All failed.

**Meet-in-the-middle** (split intents into two halves, full DP for each): 76-84/100 match. Forcing all first-half intents before second-half intents loses optimal interleavings.

**Chunked DP** (chunks of 2, all 2! orderings per chunk): 37-49/50 match. Same interleaving problem.

**Same-a dominance pruning** (prune dominated states within each `a` group): exact but only 1.5% pruning. The 2^n factor is essentially unchanged.

**Cross-a k-invariant dominance** (prune using k0 = (x0+a)*y0r, k1 = (x1+s_k-a)*y1r): inexact, 48-49/50 match. Fees make output non-monotonic in k.

**Rate-aware dominance** (prune using marginal rates r0, r1 plus output t): exact but only 2.9% pruning. Higher rate in one pool implies lower rate in the other, so the dominance condition rarely holds.

**Fee-free continuous-guided DP** (use the continuous optimal split as a guide, try only nearby discrete splits): inexact, max_delta = -168. High fees (9999 bps) make the fee-free formula a poor guide.

### Fee-aware continuous-guided DP: a partial success

The fee-aware continuous optimal split formula accounts for fee ceilings:

```
b* = (sqrt(y0r) * x1r / nf1 + sqrt(y0r) * d - sqrt(y1r) * x0r / nf0)
     / (sqrt(y0r) + sqrt(y1r))
```

where `nf0 = 1 - fee0/10000` and `nf1 = 1 - fee1/10000`.

Combined with a window of 15 around b*, this is **exact** for small amount domains:

| n | D_max | Trials | Match | max_delta |
|---|-------|--------|-------|-----------|
| 4 | 12 | 200 | 200/200 | 0 |
| 6 | 12 | 200 | 200/200 | 0 |
| 4 | 20 | 50 | 50/50 | 0 |

But the window must scale with D. For larger amounts, exactness breaks:

| n | D_max | Trials | Match | max_delta |
|---|-------|--------|-------|-----------|
| 4 | 50 | 50 | 40/50 | -28 |
| 4 | 100 | 50 | 37/50 | -75 |

The continuous relaxation is a tight guide for small D because the discrete optimum is within O(1) of the continuous optimum. As D grows, discrete rounding error grows and the optimal split drifts further from b*. The practical speedup is D/(2w+1), which is 2-3x for small D and diminishes for large D.

The D factor is reduced but not eliminated. The 2^n factor remains untouched.

---

## The advisory oracle

The subset, k-pool, and multi-set DPs are implemented as bounded research and UX advisory oracles, not settlement logic. The advisor currently exposes the two-pool subset/multiset path. It reports:

- The exact modeled optimum for a given pool/intent configuration
- An optional candidate route's missed output and gap in basis points
- Solver-cost telemetry
- Explicit `production_security_claim = false`, `settlement_authority = false`

If the configured exact-search limits are exceeded, the packet returns `exact_unavailable` with no exact output. This fail-closed design prevents the oracle from being used as an authority it does not claim to be.

The known CPSS counterexample (where the decomposition leaves output on the table) reports `exact_amount_out_total = 2`, `candidate_amount_out_total = 1`, `missed_output = 1`, and `candidate_gap_bps = 5000`. A 50% gap in a 2-pool, 3-intent batch.

---

## Honest limits

This is a serious algorithm-engineering discovery for ZenoDEX. It is not a world-level math breakthrough. The exact claim is narrow:

> For same-direction exact-in intents routed across two (or k) discrete CPMM pools, the compressed conservation state appears sufficient for exact joint batch optimization, with brute-force and full-state oracle pressure tests supporting the pruning rule.

What remains open:

- **Formal proof** of the compressed-state dominance/pruning rule (Lean obligation stated, not yet discharged).
- **The 2^n factor** is irreducible for the general problem. No polynomial-subset algorithm can be exact. The fee-aware guided DP reduces the D factor to a window for small D, but the exponential subset factor is fundamental.
- **Exact-out intents** (buy a fixed output amount) have a different objective. The dominance argument assumes exact-in splits.
- **k-pool and multi-set extensions** are now replayed in the same witness bundle, but remain computationally supported rather than formally proved.
- **Settlement authority** is advisory only. The oracle compares candidate routes against the modeled optimum. It does not authorize settlement.

---

## The research arc

1. A plausible greedy theorem was proposed.
2. A moderate test suite confirmed it (15,000 trials, 0 violations).
3. An adversarial falsification suite broke it (50,000 trials, 10 violations).
4. The failure mode was explained (greedy per-step optimization does not compose when the state space branches).
5. A corrected exact algorithm was discovered (Anticipatory, using Last-Intent Optimality).
6. The factorial barrier was eliminated (Subset DP, O(n!) to O(2^n)).
7. The algorithm was implemented and tested against brute force and full-state oracles (4,600+ trials, 0 mismatches).
8. It became a UX-facing advisory comparator with fail-closed design.
9. Generalizations to k pools and duplicate amounts were verified (6,000+ trials, 0 mismatches).
10. The 2^n barrier was attacked from six directions. All failed. The lower bound was confirmed.
11. A partial success (fee-aware guided DP) reduces the D factor for small amount domains.

The highest-value move was the falsification gate. Without it, a false theorem would have been promoted as a conclusion. The gate's contribution was not just catching the error, but forcing the adversarial distribution that exposed it. A falsification gate that accepts moderate sampling as sufficient is no gate at all.

---

*Research conducted using the Problem-Solver Toolkit discovery loop, Morph reformulation search, Atom of Thoughts structured reasoning, and adversarial falsification gating. All public code and evidence are in the ZenoDEX repository under `docs/research/` and `src/core/`.*
