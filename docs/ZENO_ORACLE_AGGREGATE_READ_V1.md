# Zeno Oracle Aggregate Read Bridge V1

This document describes the narrow aggregate-read bridge currently accepted by
the local verifier:

```bash
python3 tools/zenodex_oracle_aggregate_read.py verify <bridge>
```

The aggregate-read bridge ties an admitted aggregate to a generic accepted
read/action receipt bundle. The generic bundle can prove that a read and
downstream action are internally consistent; this bridge proves that the read
value was derived from the admitted aggregate.

## Bridge Shape

```json
{
  "schema": "zenodex.oracle.aggregate_read_bridge.v1",
  "bridge_id": "sha256:...",
  "freshness_window_epochs": 4,
  "aggregate": {
    "schema": "zenodex.oracle.admitted_median3_aggregate.v1"
  },
  "receipt_bundle": {
    "schema": "zenodex.oracle.receipt_bundle.v1"
  }
}
```

Unknown fields reject. Local bridge files above `3_000_000` bytes are
inconclusive rather than accepted.

## Content Binding

The bridge ID is content-addressed:

```text
bridge_id := sha256(canonical_json(bridge without bridge_id))
```

Plain English: the bridge ID commits to the admitted aggregate, the accepted
read/action bundle, and the freshness window used to derive the read.

The read value hash commits to the aggregate result:

```text
value_hash := sha256(canonical_json({
  aggregate_id,
  query_id,
  value_e8,
  confidence_e8,
  deviation_bps,
  observed_epoch,
  report_count,
  admission_count
}))
```

Plain English: a downstream action does not just receive a loose price hash.
The hash binds the median value, uncertainty radius, deviation, epoch, admitted
report count, and source aggregate identity.

## Acceptance Contract

The verifier accepts only when all of these checks hold:

```text
AggregateReadAccepted
  -> AdmittedMedian3Accepted
  and ReceiptBundleAccepted
  and BundleQueryMatchesAggregate
  and BundleValueHashMatchesAggregateValue
  and BundleObservedEpochMatchesAggregate
  and BundleExpiryMatchesBridgeFreshness
  and BundleActionFreshnessMatchesBridgeFreshness
```

Plain English: an accepted read/action bundle cannot point at one aggregate for
the query, another value hash for execution, and a third freshness window. All
of those facts must be derived from the same admitted aggregate.

## Output Receipt

Successful verification returns:

```json
{
  "schema": "zenodex.oracle.aggregate_read_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "bridge_id": "sha256:...",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "value_e8": 100000000,
  "confidence_e8": 1000000,
  "deviation_bps": 100,
  "observed_epoch": 102,
  "expires_at_epoch": 106,
  "errors": []
}
```

The `not_claimed` list remains part of the receipt. In particular, this bridge
does not claim that the median is the true market price. It only verifies that
the read bundle is bound to the admitted aggregate result.

## Replay

Generate and verify a minimal accepted aggregate-read bridge:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_aggregate_read.py sample --output "$tmp/aggregate-read.json"
python3 tools/zenodex_oracle_aggregate_read.py verify "$tmp/aggregate-read.json"
```

Run deterministic aggregate-read chaos replay:

```bash
python3 tools/zenodex_oracle_aggregate_read_chaos.py
```

The current aggregate-read chaos lane covers `16` named bridge-hash,
aggregate-rejection, bundle-rejection, query mismatch, value-hash mismatch,
observed-epoch mismatch, expiry mismatch, freshness-window mismatch, missing
subobject, hidden-field, schema, type-confusion, evidence weakening, and
expiry-before-observed disaster shapes.

## Non-Claims

This V1 shell does not yet claim:

- the production Oracle network is live;
- every aggregate policy can become a read;
- the median is the true market price;
- ZenoDEX critical consumers are runtime-wired to this bridge.
