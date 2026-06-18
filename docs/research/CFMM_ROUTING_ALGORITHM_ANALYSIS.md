# CFMM Routing Algorithm Analysis

## Scope

This note records the current algorithmic state for two-pool CPMM exact-in split
routing and the next promotion gates for broader CFMM routing optimization.

The runtime surface reviewed here is:

- `src/core/split_routing.py`
- `src/core/split_routing_staircase.py`
- `tests/core/test_split_routing.py`
- `lean-mathlib/Proofs/SplitRoutingStaircase.lean`

## Current Runtime Shape

For two parallel CPMM pools and a total exact-in amount `D`, the objective is:

```text
maximize output0(a) + output1(D - a) over integer a in [0, D]
```

Tie-break: choose the smallest `a` among equal-output splits.

The live entrypoint `best_split_two_pools_exact_in` currently supports:

- bounded brute force for `D <= 4096`, exact, `O(D)` quote evaluations;
- adaptive profiles such as `adaptive_v6`, heuristic, sublinear in many cases,
  but not a theorem-level exact default;
- `staircase_exact`, exact by enumerating pool0 output jump points.

## Invariants

The route selector must preserve:

```text
FeasibleSplit(a) -> a in [0, D] and both positive legs either quote or are zero endpoints
```

Every returned split must be a feasible integer allocation.

```text
Selected(a*) -> forall a, total_out(a*) >= total_out(a)
```

For exact profiles, the selected split maximizes total output over all integer
splits.

```text
total_out(a*) = total_out(a) and a < a* -> reject a*
```

The canonical winner is the leftmost maximum.

## Complexity

Let:

- `D` be total input amount;
- `B` be the number of distinct positive pool0 input breakpoints reachable by
  `D`;
- `Q(a)` be one exact pool quote under v8 integer semantics.

Current exact brute force:

```text
O(D * Q)
```

Current adaptive profiles:

```text
O((grid_n * window + rescue_sweeps) * Q)
```

This is usually cheaper than brute force, but exactness depends on the profile
and corpus evidence.

Staircase exact profile:

```text
O(B * Q)
```

For CPMM exact-in, pool0 output is a monotone integer staircase. Between two
pool0 jumps, `output0(a)` is constant while `output1(D-a)` cannot improve as
more input is moved away from pool1. Therefore the leftmost optimum is attained
at an endpoint or at a pool0 jump point.

Worst case remains `B <= D`, but realistic skewed pools can have `B << D`.

## Literature Anchor

The general CFMM routing problem has a convex-optimization foundation when fixed
execution costs are ignored:

- Angeris, Chitra, Evans, Boyd, "Optimal Routing for Constant Function Market
  Makers", arXiv:2204.05238. The paper formulates no-fixed-cost CFMM routing as
  a tractable convex optimization problem and treats fixed costs as a
  mixed-integer extension.
- Diamandis, Resnick, Chitra, Angeris, "An Efficient Algorithm for Optimal
  Routing Through Constant Function Market Makers", arXiv:2302.04938. The paper
  introduces a decomposition method for routing over CFMM networks.
- Escudero, Lara, Sama, "Optimal Routing across Constant Function Market Makers
  with Gas Fees", arXiv:2603.02844. The paper models fixed gas costs through
  mixed-integer activation thresholds and relaxed optimality conditions.

These results are useful for ZenoDEX, but they do not directly replace the
consensus integer implementation. Consensus routing must preserve exact integer
rounding, fee ceil semantics, canonical tie-breaks, and fail-closed quote
rejection. Continuous or relaxed solvers are best used as advisory candidate
generators until a deterministic integer refinement proof is available.

## Promotion Assessment

The existing staircase profile is a strong candidate for the two-pool CPMM
exact-in default because it is exact and has better asymptotic behavior than
brute force on breakpoint-sparse instances.

Do not flip the default profile solely from this note. A default change affects
quote outputs and replay compatibility.

Required promotion evidence:

1. Runtime parity: staircase equals brute force over a larger hostile corpus,
   including skewed reserves, high fees, dust edges, zero-output gaps, and
   tie-heavy plateaus.
2. Performance: quote-count report comparing `adaptive_v6`, `dense24`,
   brute force, and `staircase_exact` on realistic and adversarial profiles.
3. Formal receipt: Lean theorem plus checker output recorded as a source-pinned
   artifact, with no `sorry` and with the runtime jump formula bound to the v8
   quote function.
4. Replay review: explicit sign-off that changing the default route selector is
   acceptable for the target network/version.

## Next Work

Short-term, safe:

- Add a benchmark/report tool for exact-in split profiles.
- Add a larger deterministic hostile corpus comparing staircase against brute
  force for bounded `D`.
- Keep `adaptive_v6` as default until replay compatibility is reviewed.

Medium-term:

- Generalize the staircase idea to k parallel CPMM pools using a deterministic
  marginal-jump frontier, with brute-force parity on small domains.
- Use the convex/decomposition literature as an advisory candidate generator for
  multi-asset routing, then verify the emitted integer candidate set with a
  deterministic certificate checker.

Long-term:

- Treat gas/fixed route activation costs as a separate mixed-integer layer.
  Activation thresholds must be explicit in the certificate; a continuous
  relaxation alone is insufficient for production routing claims.
