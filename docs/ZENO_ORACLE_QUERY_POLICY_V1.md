# Zeno Oracle Query Policy V1

Status: first public local verifier format for query-policy versioning.

This document describes the narrow query-policy lifecycle currently accepted by:

```text
python3 tools/zenodex_oracle_query_policy.py verify <trace>
```

The purpose is to block a common oracle failure shape: a critical consumer binds
to a price query, then the freshness, evidence, deviation, quorum, or schema
requirements are silently weakened before execution.

## Trace Shape

```json
{
  "schema": "zenodex.oracle.query_policy_trace.v1",
  "query_id": "sha256:...",
  "events": []
}
```

Allowed top-level fields are exactly:

- `schema`
- `query_id`
- `events`

The verifier bounds traces to `64` events and local files to `250_000` bytes.

## Event Types

The first shell supports:

| Event | Required Fields |
| --- | --- |
| `publish_policy` | `type`, `epoch`, `policy` |
| `bind_consumer` | `type`, `epoch`, `consumer_module`, `action_kind`, `action_id`, `action_epoch`, `critical`, `policy_id` |

Unknown event fields reject. Event epochs must be monotone nondecreasing.

## Policy Shape

```json
{
  "policy_id": "sha256:...",
  "query_id": "sha256:...",
  "version": 1,
  "supersedes_policy_id": null,
  "evidence_floor": "O3",
  "max_staleness_epochs": 4,
  "max_deviation_bps": 200,
  "min_distinct_sources": 3,
  "min_distinct_reporters": 3,
  "aggregation_schema": "zenodex.oracle.median3_aggregate.v1",
  "read_schema": "zenodex.oracle.receipt_bundle.v1"
}
```

Allowed policy fields are exactly:

- `policy_id`
- `query_id`
- `version`
- `supersedes_policy_id`
- `evidence_floor`
- `max_staleness_epochs`
- `max_deviation_bps`
- `min_distinct_sources`
- `min_distinct_reporters`
- `aggregation_schema`
- `read_schema`

Every policy ID is content-addressed:

```text
policy_id := sha256(canonical_json(policy without policy_id))
```

Plain English: a policy ID commits to the complete policy body. If freshness,
evidence, quorum, deviation, or schema requirements change, the policy ID must
also change.

## Monotone Revision Rule

The first policy for a query must be version `1` and must not supersede another
policy. Every later policy must supersede the currently active policy and
increment the version by exactly one.

Policy revisions may tighten the envelope. They may not loosen it:

```text
NewPolicyAccepted ->
  evidence_floor_new >= evidence_floor_old
  and max_staleness_epochs_new <= max_staleness_epochs_old
  and max_deviation_bps_new <= max_deviation_bps_old
  and min_distinct_sources_new >= min_distinct_sources_old
  and min_distinct_reporters_new >= min_distinct_reporters_old
  and aggregation_schema_new = aggregation_schema_old
  and read_schema_new = read_schema_old
```

Plain English: a later policy can demand stronger evidence, fresher data, lower
deviation, or higher reporter/source quorum. It cannot quietly make critical
oracle use easier.

## Critical Consumer Binding

Consumer bindings must be critical and must bind to the active policy at the
time of binding:

```text
CriticalConsumerBindingAccepted ->
  critical = true
  and policy_id = active_policy_id
  and action_epoch >= binding_epoch
```

Plain English: the consumer cannot bind an unknown policy, an older weaker
policy after a tighter one exists, a non-critical policy shell, or an action
that happened before the binding event.

## Replay Commands

Generate and verify a minimal accepted trace:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_query_policy.py sample --output "$tmp/query-policy.json"
python3 tools/zenodex_oracle_query_policy.py verify "$tmp/query-policy.json"
rm -rf "$tmp"
```

Run deterministic query-policy chaos replay:

```bash
python3 tools/zenodex_oracle_query_policy_chaos.py
```

The current query-policy chaos lane covers `19` named downgrade, schema-drift,
hash-forgery, wrong-query, wrong-supersedes, version-skip, stale-binding,
hidden-field, and epoch-regression disaster shapes. Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- query-policy governance is live;
- every future policy dimension is finalized;
- every downstream ZenoDEX consumer is wired to this shell;
- reporter sources are honest;
- oracle values are true market prices.

The claim is narrower: this first query-policy shell rejects silent downgrades
and stale policy bindings before they can be used as critical Oracle policy
authority.
