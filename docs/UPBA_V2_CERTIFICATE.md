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

The first local admission certificate verifier is now
`src/core/uniform_batch_admission.py`. It verifies this deterministic policy for
a known eligible set:

```text
zenodex/upba_admission_v1/canonical_intent_id_prefix
```

The policy admits the canonical `intent_id` prefix up to `max_admitted` and
hash-binds the eligible, admitted, and overflow sets. It now supports homogeneous
exact-in and exact-out swap sets and rejects mixed-kind or mixed-asset-pair
sets. This gives a UPBA clearing certificate a deterministic admitted-set source
after a batch-builder or ledger has defined the eligible set boundary. It still
does not prove global mempool fairness, censorship resistance, or Sybil
resistance by itself.

## Optimality Boundary

The model proof in `lean-mathlib/Proofs/UniformBatchOptimality.lean`
formalizes a fixed-price aggregate volume bound:

```text
matchedVolume <= min(acceptableDemand, acceptableSupply)
```

It also proves a finite audit-set certificate lemma: if a verifier checks that
no audited candidate has more volume, and no equal-volume audited candidate has
more surplus, then the submitted candidate is weakly optimal inside that audited
set.

The same file now includes the v2 partial-fill bridge:

```text
upba_v2_partial_fill_bounded_grid_upper_bound_certificate_implies_global_weak_optimal
```

This theorem says that an upper-bound certificate proves global weak optimality
over the bounded v2 candidate family when the audited set enumerates every
canonical bounded-grid price and every admitted bounded partial-fill plan.

Runtime support comes through the existing
`uniform_batch_optimality_certificate` envelope field. The checker binds the
winner id to the v2 UPBA certificate hash, then verifies the finite audited-set
upper-bound predicate. Completeness of the audited set remains a separate
obligation carried by the grid/plan enumeration process.

The v2 runtime now has a deterministic table-root helper for that enumeration
process:

```text
table_root = H(schema, objective_id, candidate_set_hash, rows)
```

`build_uniform_batch_v2_bounded_grid_audit_candidates_v1` enumerates a reduced
positive integer price grid against a supplied finite set of canonical
partial-fill vectors, keeps only candidates accepted by the v2 certificate
verifier, and attaches a `fill_vector_hash` to each audit candidate.

`verify_uniform_batch_v2_bounded_grid_optimality_certificate_v1` rebuilds the
same table, checks an optional expected root, and requires the submitted
optimality certificate to match the rebuilt complete-domain
`candidate_set_hash`. If the supplied grid/vector domain contains a better
accepted candidate that the optimality certificate omitted, the verifier rejects
before the bound certificate can be used as complete-domain evidence.

The engine also exposes a strict UPBA posture through `DexEngineConfig`:

```python
DexEngineConfig(
    allow_uniform_batch_certificate=True,
    require_uniform_batch_certificate_for_supported_swaps=True,
    require_uniform_batch_optimality_certificate=True,
    require_uniform_batch_v2_bounded_grid_optimality=True,
    require_uniform_batch_v3_exact_out_grid_optimality=True,
)
```

For production-candidate wiring, use the named helper:

```python
make_strict_upba_engine_config()
```

Under that posture, supported single-pool exact-in and exact-out swap batches
fail closed if they omit the UPBA certificate, and any UPBA settlement fails
closed if it omits bound optimality evidence. V2 partial-fill certificates must
carry bounded-grid evidence, and v3 exact-out certificates must carry exact-out
grid evidence.

## Tests

Focused runtime tests cover:

- partial-fill acceptance;
- zero-fill rejected members;
- fill-above-intent rejection;
- all-zero v2 rejection;
- schema/policy mismatch rejection;
- v2 permutation invariance over randomized partial fills;
- optimality-certificate winner binding to a v2 partial-fill certificate;
- v3 exact-out complete-domain grid evidence;
- deterministic admission-certificate prefix selection and hash binding;
- strict UPBA engine posture requiring certificate and bound optimality evidence;
- engine acceptance only when both `allow_uniform_batch_certificate=True` and `allow_uniform_batch_partial_fill_certificate=True`.

Replay command:

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_admission.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```
