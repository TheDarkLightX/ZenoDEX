---
title: UPBA V2 Certificate Verifier
type: note
permalink: autonomous-tau-dex-review/docs/upba-v2-certificate
---

# UPBA V2 Certificate Verifier

UPBA v2 extends the v1 uniform-price certificate verifier with bounded partial
fills. The scope remains deliberately small: one existing active CPMM pool,
`SWAP_EXACT_IN` intents only, one fixed admission set, one canonical reduced
rational price, and one aggregate reserve update.

The verifier lives in `src/core/uniform_batch_clearing.py`.

## Scope

Supported beyond v1:

- explicit schema `zenodex/uniform_batch_clearing_certificate/v2`;
- explicit policy id
  `zenodex/upba_v2/fixed_admission_partial_fill_cpmm_exact_in`;
- `0 <= executed_in <= intent.amount_in`;
- zero-fill certificate members represented as local `REJECT` fills with reason
  `UNIFORM_BATCH_UNFILLED`;
- canonical price computed from executed net flow, excluding zero-fill members;
- at least one positive fill per accepted v2 certificate.

Still excluded:

- exact-out intents;
- multi-hop routing;
- create-pool, add-liquidity, and remove-liquidity intents;
- solver-side volume or surplus optimality;
- order inclusion and censorship-resistance claims;
- using the uniform clearing price as an oracle or derivatives mark.

## Certificate Contract

```text
UniformBatchCertificateV1 with:
  schema = zenodex/uniform_batch_clearing_certificate/v2
  policy_id = zenodex/upba_v2/fixed_admission_partial_fill_cpmm_exact_in
```

The Python type name remains `UniformBatchCertificateV1` for compatibility with
the current module API. The schema and policy id carry the runtime semantics.

Each certificate fill obeys:

```text
0 <= executed_in <= intent.amount_in
0 <= executed_out <= UNIFORM_BATCH_OUTPUT_AMOUNT_MAX
```

If `executed_in = 0`, v2 requires `executed_out = 0` and emits a rejected fill:

```text
FillAction.REJECT, reason = UNIFORM_BATCH_UNFILLED
```

Positive fills are priced exactly as v1:

```text
fee = ceil(executed_in * fee_bps / 10_000)
net_in = executed_in - fee
```

For `base -> quote`:

```text
executed_out = floor(net_in * price_num / price_den)
```

For `quote -> base`:

```text
executed_out = floor(net_in * price_den / price_num)
```

Limit checks remain cross-multiplied:

```text
executed_out * intent.amount_in >= intent.min_amount_out * executed_in
```

This keeps the consensus-relevant limit predicate division-free. A zero-fill
member satisfies the arithmetic inequality only as an explicit unfilled member;
it does not create deltas.

## Canonical Price Objective

V2 computes the canonical objective from executed net flow:

```text
base_net  = sum(net_in for positive base -> quote fills)
quote_net = sum(net_in for positive quote -> base fills)
```

If both sides have positive executed net flow:

```text
price_num / price_den := quote_net / base_net
```

The ratio must be reduced to lowest terms.

If the positive executed flow is one-sided, the fallback remains the reduced
pre-pool spot ratio:

```text
price_num / price_den := reserve1 / reserve0
```

The verifier rejects an all-zero v2 certificate before settlement construction.
This avoids a certificate whose price is meaningful only by fallback while no
trade occurred.

## Negative Knowledge Captured

The v1 verifier rejected partial fills to keep the first runtime bridge small.
That kept the certificate boundary simple, but it made the model too rigid for a
real auction lane where some admitted orders may be partially filled or left
unfilled by a solver.

The v2 extension keeps the admission set fixed and certificate-bound while
moving the clearing arithmetic from `intent.amount_in` to `executed_in`. The
core invariant is:

```text
same executed-flow multiset -> same aggregate deltas and same price objective
```

The admission set is still a separate problem. V2 verifies a proposed settlement
for the admitted set; it does not prove the admitted set is the best or fairest
set.

## Optimality Boundary

The starter model proof in `lean-mathlib/Proofs/UniformBatchOptimality.lean`
formalizes a fixed-price aggregate volume bound:

```text
matchedVolume <= min(acceptableDemand, acceptableSupply)
```

It also proves a finite audit-set certificate lemma: if a verifier checks that
no audited candidate has more volume, and no equal-volume audited candidate has
more surplus, then the submitted candidate is weakly optimal inside that audited
set.

This is useful for the next verifier generation. It is not yet a runtime
optimality claim for UPBA v2 because the current certificate does not carry an
audited candidate set or a proof that the solver searched every admissible
price.

## Tests

Focused runtime tests cover:

- partial-fill acceptance;
- zero-fill rejected members;
- fill-above-intent rejection;
- all-zero v2 rejection;
- schema/policy mismatch rejection;
- v2 permutation invariance over randomized partial fills;
- engine acceptance when `allow_uniform_batch_certificate=True`.

Replay command:

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```
