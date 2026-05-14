---
title: ZenoHypergraph UPBA Evidence V1
type: design_spec
permalink: autonomous-tau-dex-review/docs/zenohypergraph-upba-evidence-v1
---

# ZenoHypergraph UPBA Evidence V1

ZenoHypergraph v1 is a runtime-bound evidence layer for the existing UPBA v1
bounded price-grid path. It commits the admitted batch, price-grid table, winner,
and proof rails into one canonical root:

```text
uniform_batch_hypergraph_root
```

The root is a public verification artifact. It does not claim production FHE,
private balances, or confidential order settlement.

## Scope

The supported surface is the current UPBA v1 lane:

```text
single CPMM pool
SWAP_EXACT_IN intents
full-fill-or-reject policy
bounded integer price grid
complete price-grid table evidence
deterministic Python verifier
Lean padding/permutation model proof
```

It does not cover exact-out UPBA, partial fills, multi-hop routes, multi-pool
netting, LP actions, fair inclusion, oracle safety, or batch-boundary games.

## Canonical Root

The root is computed by:

```text
src/core/zenohypergraph_upba.py
```

The body commits to:

```text
schema
relation id
policy id
score function id
settlement id
uniform batch certificate hash
intent set hash
pool state hash
price-grid table root
canonical order vertices
canonical price-row vertices
complete order x price-row incidence summary
winner row
explicit non-claims
```

The root uses canonical JSON plus domain-separated SHA-256 through the same
canonical encoding primitives as the rest of the settlement evidence path.

## Why The Incidence Relation Is Compressed

A literal hyperedge for every `(order, price_row)` pair can be large:

```text
edge_count = order_count * price_row_count
```

The v1 root records the relation as a complete incidence law:

```text
orders x price_rows
```

The order vertices and price-row vertices are sorted canonically. The existing
price-grid verifier recomputes every bounded row, so the hypergraph root only
needs to bind the verified relation, vertices, table root, and winner.

## Runtime Enforcement

The settlement envelope accepts:

```text
uniform_batch_hypergraph_root
```

If the field is supplied, the DEX engine verifies it against the admitted intents,
pool state, balances, UPBA certificate, and bounded price-grid evidence.

Strict UPBA configuration now requires it:

```text
make_upba_v1_bounded_price_grid_engine_config()
  -> require_uniform_batch_certificate = True
  -> require_uniform_batch_price_grid_evidence = True
  -> require_uniform_batch_hypergraph_root = True
```

Fail-closed behavior:

```text
missing root under strict config -> reject
mismatched root -> reject
root without price-grid evidence -> reject
non-string root -> reject
tampered price-grid table -> reject before root acceptance
```

## Lean Evidence

The model proof is:

```text
lean-mathlib/Proofs/ZenoHypergraphPadding.lean
```

It proves:

```text
rowScore_perm_invariant
rowScore_padRight_neutral
evalFiber_direct_score_equiv
evalFiber_padRight_neutral
```

The proof supports fixed-shape ZK/FHE/Tau-Table encodings at the model layer:
order-price edge contributions can be permuted or padded with inactive slots
without changing the row score.

## Runtime Evidence

Focused tests:

```text
tests/core/test_zenohypergraph_upba.py
tests/integration/test_dex_engine_uniform_batch_certificate.py
```

The core tests cover:

```text
order permutation invariance
price-row permutation invariance
root mismatch rejection
tampered price-grid rejection
```

The integration tests cover:

```text
strict config accepts correctly bound root
strict config rejects missing root
engine rejects mismatched root
parser rejects non-string root
config rejects hypergraph requirement without price-grid requirement
```

## Production Boundary

Accepted claim:

```text
UPBA v1 bounded price-grid evidence can be bound to a canonical
ZenoHypergraph root and enforced by strict engine configuration.
```

Non-claims:

```text
no production FHE claim
no private order or private balance claim
no encrypted argmax claim
no fair inclusion claim
no unbounded optimality claim
```

This design prepares the evidence object that a future ZK or FHE backend can
reuse. It keeps experimental privacy work outside the trusted settlement path
until a separate proof-of-execution or verifiable-FHE lane exists.
