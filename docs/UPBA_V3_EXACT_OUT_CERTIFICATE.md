---
title: UPBA V3 Exact-Out Certificate
type: note
permalink: autonomous-tau-dex-review/docs/upba-v3-exact-out-certificate
---

# UPBA V3 Exact-Out Certificate

UPBA v3 adds a narrow exact-out certificate surface for one existing CPMM pool.
It supports admitted `SWAP_EXACT_OUT` intents only.

## Scope

The fixed policy id is:

```text
zenodex/upba_v3/fixed_admission_full_fill_cpmm_exact_out
```

The schema is:

```text
zenodex/uniform_batch_clearing_certificate/v3
```

The price objective remains:

```text
zenodex/upba_v1/net_flow_ratio_or_pool_spot_price
```

The objective id is shared with v1/v2 because the canonical price formula is
still based on aggregate executed net flow. The intent kind and fill rule
changed.

## Runtime Contract

For each admitted exact-out intent, the certificate must supply:

```text
executed_out = intent.amount_out
executed_in <= intent.max_amount_in
```

The verifier computes the net input after the CPMM fee rule:

```text
net_in = executed_in - ceil(executed_in * fee_bps / 10_000)
```

Then it checks the uniform price output:

```text
uniform_out(net_in, price) >= executed_out
```

Finally, it requires `executed_in` to be the minimal gross input that can satisfy
the requested output at the uniform price:

```text
executed_in =
  ceil(required_net_in(executed_out, price) * 10_000 / (10_000 - fee_bps))
```

This prevents a certificate from overcharging exact-out users while still
allowing integer rounding to retain any overdelivery gap inside the pool.

Focused runtime tests cover the rounding case where the minimal exact-out input
would produce more than the requested output at the uniform price. The verifier
keeps the requested `executed_out` in the user fill and retains the integer
rounding gap in pool reserves.

## Checks

The verifier rejects:

- non-`SWAP_EXACT_OUT` intents under the v3 policy;
- mixed exact-in/exact-out admitted sets under the v3 policy;
- schema/policy mismatch;
- non-positive fills;
- exact-out fills whose `executed_out` differs from `intent.amount_out`;
- fills above `intent.max_amount_in`;
- inputs that do not satisfy the uniform price;
- inputs that are larger than the minimal uniform-price exact-out input;
- 100% fee exact-out computation;
- aggregate reserve negativity;
- aggregate CPMM `K` decrease.

## Evidence Boundary

This is runtime certificate evidence for exact-out execution under a fixed
admitted set.

`lean-mathlib/Proofs/UniformBatchOptimality.lean` includes the conditional
model theorem:

```text
upba_v3_exact_out_bounded_grid_upper_bound_certificate_implies_global_weak_optimal
upba_v3_exact_out_exact_grid_upper_bound_certificate_implies_global_weak_optimal
upba_v3_full_fill_exact_out_grid_upper_bound_certificate_implies_global_weak_optimal
```

That theorem has the same premise shape as the v2 partial-fill bridge: if the
audited set enumerates every canonical bounded-grid price and every admitted
bounded exact-out fill plan, then the upper-bound certificate proves global weak
optimality over that bounded family.

The exact-grid variant derives winner feasibility from the audited set itself:
soundness plus winner membership means the declared winner is one of the
generated bounded exact-out candidates.

The full-fill variant specializes the v3 theorem to the current runtime shape:
the admitted intent set fixes one deterministic exact-out fill plan, so the
bounded search domain is the canonical price grid scored with that plan.
The theorem `exactOutFullFillCanonicalGridCandidates_eq_singleton_plan` ties
that specialized list back to the general exact-out candidate model with a
singleton plan list.

The runtime helper
`build_uniform_batch_exact_out_grid_audit_candidates_v1` enumerates accepted v3
exact-out certificates over a reduced integer price grid and scores each
accepted candidate by:

```text
volume  = sum(executed_out)
surplus = sum(max_amount_in - executed_in)
```

This creates the finite audited candidate set consumed by the generic UPBA
optimality certificate checker.

`verify_uniform_batch_v3_exact_out_grid_optimality_certificate_v1` rebuilds that
audited set from the supplied intents, pool, balances, and grid bounds before it
accepts an optimality certificate. It rejects a certificate whose
`candidate_set_hash` does not match the rebuilt v3 exact-out grid set, and it
requires the declared winner certificate to use the v3 policy and schema.
The engine consumes the evidence through the settlement field
`uniform_batch_v3_exact_out_grid` when
`require_uniform_batch_v3_exact_out_grid_optimality=True` is enabled.
The evidence object is closed over:

```text
max_price_num
max_price_den
```

The engine rejects missing bounds, unknown fields, boolean bounds, non-object v3
grid evidence, v3 grid evidence without an optimality certificate, v3 grid
evidence attached to a non-v3 certificate, and settlements that try to provide
both v2 and v3 bounded-grid evidence.

The regression
`test_uniform_batch_exact_out_grid_candidates_match_independent_reduced_grid_replay`
replays the same bounded reduced grid through an independent test-side
certificate builder, runs each candidate through the public verifier, and checks
that the helper output matches exactly the independently accepted candidate set.
This is the runtime evidence for the Lean-side premise that the audited set is
complete over the configured bounded exact-out grid family.

The same regression projects every grid certificate to its non-price exact-out
plan:

```text
plan = [(intent_id, executed_out)]
```

Every helper candidate and every independently rebuilt grid candidate has the
same projection, matching the admitted intent `amount_out` values. Runtime
evidence therefore matches the full-fill theorem's singleton-plan premise.

`lean-mathlib/Proofs/UniformBatchExactOutMinimality.lean` proves the
fixed-price integer input contract used by the v3 verifier:

```text
minimalGrossForOut_satisfies_and_minimal
```

For a positive price ratio and `fee_bps < 10000`, the gross input computed from
the exact-out amount is sufficient to satisfy the uniform price and minimal
among all gross inputs that satisfy that same fixed price.

The current runtime work does not yet include:

- multi-hop exact-out;
- partial exact-out fills;
- proof that the eligible/admitted set is fair;
- unbounded rational-price completeness;
- proof that the selected price grid is economically sufficient.

The v3 surface is useful because it removes a previous functional gap: exact-out
orders can now use the same uniform-price settlement verifier shape as exact-in
orders, with deterministic integer fee and rounding checks.

## Replay

```bash
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```
