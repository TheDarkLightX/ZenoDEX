---
title: UPBA V1 Certificate Verifier
type: note
permalink: autonomous-tau-dex-review/docs/upba-v1-certificate
---

# UPBA V1 Certificate Verifier

UPBA v1 is the first runtime bridge from the uniform-price batch auction idea to
the Python functional core. The goal is intentionally small: verify a fixed
admission set of exact-in swaps for one existing CPMM pool under one rational
integer price vector.

The verifier lives in `src/core/uniform_batch_clearing.py`.

## Scope

Supported:

- one existing `PoolState`
- `PoolStatus.ACTIVE`
- `CURVE_TAG_CPMM`
- `SWAP_EXACT_IN` intents only
- the pool's two assets only
- one rational price vector `price_num / price_den`
- deterministic ceil fee on gross input
- deterministic floor output on net input
- canonical fill ordering by `intent_id`
- one aggregate reserve update
- aggregate CPMM invariant check

Excluded for v1:

- exact-out intents
- multi-hop routing
- create-pool, add-liquidity, and remove-liquidity intents
- clearing-price optimality
- order inclusion games
- oracle coupling
- batch-boundary timing games

These exclusions are deliberate. The v1 verifier proves the local certificate
shape is deterministic and conservative. It does not claim global auction
optimality.

## Certificate Contract

```text
UniformBatchCertificateV1 :=
  pool_id
  base_asset
  quote_asset
  intent_set_hash
  price_num
  price_den
  fills: [(intent_id, executed_in, executed_out)]
```

`intent_set_hash` is the canonical hash of the fixed admission set. It includes
the sorted intent identifiers, common intent fields, and full intent field maps.
This prevents a certificate from being replayed against a different order set.

For every filled exact-in intent, the verifier checks:

```text
fee = ceil(executed_in * fee_bps / 10_000)
net_in = executed_in - fee
executed_out = floor(net_in * price_num / price_den)       for base -> quote
executed_out = floor(net_in * price_den / price_num)       for quote -> base
```

The limit-price condition is cross-multiplied:

```text
executed_out * intent.amount_in >= intent.min_amount_out * executed_in
```

This avoids consensus-critical division in the limit check.

The aggregate reserve check is:

```text
(reserve0 + delta0) * (reserve1 + delta1) >= reserve0 * reserve1
```

The pool updates once from the aggregate deltas. The verifier does not simulate
any sequential ordering inside the batch.

## Negative Knowledge Captured

Sequential CPMM execution creates path dependence. A permutation of the same
orders can produce different intermediate reserves and different outputs. UPBA
v1 removes that dimension for this narrow surface because the certificate is
keyed by the order multiset and canonical fill list rather than input sequence.

The tests include a permutation-invariance check, an aggregate `k` decrease
rejection, a limit-price rejection, a noncanonical fill-order rejection, and a
tampered-settlement rejection.

## Promotion Boundary

Current evidence class: `implemented + tested_discovery`.

The next promotion step is a small Lean theorem mirroring the runtime shape:

```text
Perm intents1 intents2
same certificate
same fixed pool and balances
->
build(intents1, certificate) = build(intents2, certificate)
```

After that, the production path can add a settlement mode that accepts UPBA v1
only when the certificate verifier produces the exact accepted settlement.
