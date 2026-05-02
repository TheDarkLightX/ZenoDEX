# Zeno Oracle Aggregate Adapter Bridge V1

This document describes the narrow aggregate-adapter bridge currently accepted
by the local verifier:

```bash
python3 tools/zenodex_oracle_aggregate_adapter.py verify <bridge>
```

The aggregate-adapter bridge ties the complete local Oracle chain together:

```text
admitted reports -> admitted median3 -> aggregate read -> action/profile adapter
```

Plain English: this verifier checks that a concrete downstream action is bound
to a read bundle that is itself derived from an admitted aggregate.

## Bridge Shape

```json
{
  "schema": "zenodex.oracle.aggregate_adapter_bridge.v1",
  "bridge_id": "sha256:...",
  "aggregate_read": {
    "schema": "zenodex.oracle.aggregate_read_bridge.v1"
  },
  "action": {
    "schema": "zenodex.oracle.consumer_action_binding.v1"
  },
  "profile": {
    "schema": "zenodex.oracle.consumer_profile.v1"
  }
}
```

Unknown fields reject. Local bridge files above `3_500_000` bytes are
inconclusive rather than accepted.

## Content Binding

The bridge ID is content-addressed:

```text
bridge_id := sha256(canonical_json(bridge without bridge_id))
```

Plain English: the bridge ID commits to the aggregate-read bridge, the concrete
downstream action binding, and the consumer profile.

## Acceptance Contract

The verifier accepts only when all of these checks hold:

```text
AggregateAdapterAccepted
  -> AggregateReadAccepted
  and AdapterAccepted(action, aggregate_read.receipt_bundle, profile)
```

Plain English: the bridge does not let a downstream action bring its own looser
receipt bundle. The adapter is run against the exact bundle proven by the
aggregate-read bridge.

The nested adapter also enforces:

```text
AdapterAccepted
  -> ActionFactsMatchAcceptedBundle
  and ActionPolicyNoWeakerThanProfile
```

Plain English: the action must match the consumer module, action kind, action
ID, query, value hash, read receipt, consumer-action receipt, evidence floor,
and freshness window in the accepted bundle and profile.

## Output Receipt

Successful verification returns:

```json
{
  "schema": "zenodex.oracle.aggregate_adapter_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "bridge_id": "sha256:...",
  "aggregate_read_bridge_id": "sha256:...",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_aggregate_read",
  "action_id": "sha256:...",
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "profile_id": "sha256:...",
  "errors": []
}
```

The `not_claimed` list remains part of the receipt. In particular, this bridge
does not claim that the downstream module is already runtime-integrated. It
only checks the local artifact chain.

## Replay

Generate and verify a minimal accepted aggregate-adapter bridge:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_aggregate_adapter.py sample --output "$tmp/aggregate-adapter.json"
python3 tools/zenodex_oracle_aggregate_adapter.py verify "$tmp/aggregate-adapter.json"
```

Run deterministic aggregate-adapter chaos replay:

```bash
python3 tools/zenodex_oracle_aggregate_adapter_chaos.py
```

The current aggregate-adapter chaos lane covers `16` named bridge-hash,
aggregate-read rejection, action query/value/action/read/consumer-receipt
mismatch, profile hash, profile mismatch, freshness weakening, non-critical
action, missing subobject, hidden-field, and schema-downgrade disaster shapes.

## Non-Claims

This V1 shell does not yet claim:

- the production Oracle network is live;
- the downstream ZenoDEX modules are runtime-wired to this verifier;
- profile catalogs are automatically loaded by production consumers;
- the median is the true market price.
