# v187 Certificate-Carrying Route Interval Graph

## Structural Target

This cycle tests whether two math objects can be fused into one proof-oriented
route/treasury primitive:

```text
integer CPMM interval edge
+ potential certificate
-> safe route pruning / no-positive-cycle certificate
```

The target is a **certificate-carrying route interval graph**. Each directed
edge carries:

- integer CPMM reserves,
- post-fee exact output semantics,
- a rational upper-rate certificate,
- a positive asset potential.

If every edge satisfies:

```text
upper_rate(i,j) * potential[j] <= potential[i]
```

then any certified route is value-nonincreasing under the potential, and any
prefix can produce a safe upper bound for pruning.

## Bounded Domain

- Asset count: `5`.
- Graphs:
  - discovery: `80` no-arb graphs and `40` injected-arb graphs.
  - holdout: `80` no-arb graphs and `40` injected-arb graphs.
- Edges: complete directed graph over the 5 assets.
- Fee model: `997 / 1000`.
- No-arb edge discounts: `{97/100, 98/100, 99/100}`.
- Injected edge boost: `103/100`, paired with ordinary reverse edge, so the
  two-edge upper-rate product is above one.
- Route candidates: simple paths from asset `1` to asset `5` with at most
  `3` edges.
- Integer CPMM floor grid:
  - discovery: reserves and post-fee inputs in `[1, 80]`.
  - holdout: reserves and post-fee inputs in `[81, 140]`.

## Reference Anchors

- Potential / reduced-cost view: shortest-path potential certificates, already
  mirrored in `lean-mathlib/Proofs/ArbitrageCertificate.lean`.
- Interval arithmetic and numerical methods: DLMF Chapter 3,
  `https://dlmf.nist.gov/3`.
- Formalization target: Lean Mathlib order/arithmetic plus existing ZenoDEX
  arbitrage and routing proof packets.
- Sequence/recurrence fallback for future residuals: OEIS.

## Claim Tier

`symbolic_state_compiler`.

The cycle does not produce a direct production router. It produces a certificate
shape and exact-rational Julia evidence that the shape is useful and worth
formalizing:

- potential certificates reject injected arbitrage edges in the bounded corpus,
- certified no-arb graphs produce zero false route-prunes in the bounded corpus,
- post-fee CPMM floor error is always in `[0,1)` in the bounded grid.

## Run

```bash
python3 run_cycle.py
pytest -q test_cycle.py
```

`run_cycle.py` invokes Julia, writes `generated/raw.tsv`, and builds
`generated/report.json`.

## Non-Claims

This is not a proof of production route optimality. It does not cover:

- all graph sizes,
- live reserve mutation during multi-hop execution,
- concurrency or MEV ordering,
- external venue execution,
- floating-point price feeds.

Promotion requires Lean/ESSO/Tau theorem closure.
