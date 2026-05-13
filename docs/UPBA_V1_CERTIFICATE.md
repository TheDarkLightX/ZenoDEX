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

The integration shell accepts the certificate only when
`DexEngineConfig.allow_uniform_batch_certificate=True`. The certificate is
carried inside `ops["3"].uniform_batch_certificate`, and the supplied settlement
must match the canonical settlement produced by the verifier when
`require_settlement_match=True`.

## Scope

Supported:

- one existing `PoolState`
- `PoolStatus.ACTIVE`
- `CURVE_TAG_CPMM`
- explicit policy id `zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in`
- committed pre-pool snapshot hash
- `SWAP_EXACT_IN` intents only
- the pool's two assets only
- one reduced rational price vector `price_num / price_den`
- `price_num` and `price_den` bounded by the UPBA price-ratio domain
- certificate outputs and intent `min_amount_out` bounded by the UPBA output
  domain
- at most 256 admitted intents and 256 certificate fills
- deterministic ceil fee on gross input
- deterministic floor output on net input
- canonical fill ordering by `intent_id`
- one fill for every intent in the fixed admission set
- full gross input consumption for every admitted intent
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
  policy_id
  pool_id
  base_asset
  quote_asset
  pool_state_hash
  intent_set_hash
  price_num
  price_den
  fills: [(intent_id, executed_in, executed_out)]
```

`pool_state_hash` is the same deterministic pool fingerprint used by quote
receipts. It includes reserves, fee, curve metadata, LP supply, status, and
creation time. A certificate replayed against a different pool snapshot fails
before settlement construction.

`policy_id` is fixed to
`zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in`. Certificates with a
different policy id fail closed, and v1 rejects unknown certificate or fill
keys. This prevents a future UPBA variant from being silently interpreted under
the current fixed-admission, full-fill exact-in semantics.

`price_num / price_den` must be reduced to lowest terms. This makes the
certificate hash canonical for the represented rational price and rejects
duplicate encodings such as `1 / 1` and `2 / 2`.

`price_num` and `price_den` are also capped at the same 3,000,000,000 domain
used by the CPMM reserve bound. Since v1 requires
`executed_in <= 3,000,000,000`, the uniform-price multiplication
`net_in * price_num` stays within the intended bounded-integer envelope instead
of falling back to arbitrary-size arithmetic as a protocol feature.

The derived output domain is:

```text
UNIFORM_BATCH_OUTPUT_AMOUNT_MAX :=
  DEX_SWAP_AMOUNT_MAX * UNIFORM_BATCH_PRICE_RATIO_MAX
```

Certificate `executed_out` values and intent `min_amount_out` values are capped
by this derived maximum. This keeps the limit-price cross multiplication inside
a documented finite domain.

The fixed admission set and certificate fill list are also capped at 256
entries. The verifier checks the intent count before computing the
`intent_set_hash`, so oversize UPBA batches fail before entering the heavier
canonical-hash and fill-matching path.

`intent_set_hash` is the canonical hash of the fixed admission set. It includes
the sorted intent identifiers, common intent fields, and full intent field maps.
This prevents a certificate from being replayed against a different order set.
The certificate must then provide exactly one sorted fill for every admitted
intent, and each fill must consume the intent's full `amount_in`. v1 fails
closed instead of producing local `REJECT` or partial-fill outcomes.

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
rejection, a limit-price rejection, a pre-pool snapshot rejection, a
nonreduced price rejection, price-domain and output-domain rejections, an
oversize certificate rejection, an oversize admission-set rejection, an
unsupported-policy rejection, closed-schema rejections, a noncanonical
fill-order rejection, an admitted-intent omission rejection, a partial-fill
rejection, and a tampered-settlement rejection.

## Promotion Boundary

Current evidence class: `proved model + implemented + tested_discovery`.

The model proof lives in `lean-mathlib/Proofs/UniformBatchClearingV1.lean`.
It proves that aggregate uniform execution is invariant under order-list
permutation for the abstract sum-of-deltas model.

```text
List.Perm fills1 fills2
->
executeUniform state fills1 = executeUniform state fills2
```

The runtime bridge now accepts UPBA v1 only when the local verifier produces the
exact accepted settlement. Remaining non-claims:

- the submitted price maximizes volume or surplus;
- the fixed admission set is fair or inclusion-resistant;
- support for partially-filled or rejected members of an admitted UPBA batch;
- the price is safe as an oracle or derivatives mark;
- exact-out, multi-hop, or LP-management intents are supported.
