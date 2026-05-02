# Zeno Oracle Adapter V1

Status: first public local verifier format for downstream critical-action
binding.

This document describes the narrow adapter currently accepted by:

```text
python3 tools/zenodex_oracle_adapter.py verify --action <action> --bundle <bundle>
```

It can also verify an action against a consumer profile:

```text
python3 tools/zenodex_oracle_adapter.py verify --action <action> --bundle <bundle> --profile <profile>
```

The adapter is the first local shell for:

```text
OracleUseOK(action, receipt_bundle) -> bool
```

Plain English: a downstream ZenoDEX-critical action should not inspect raw
oracle values or rebuild oracle policy by hand. It should ask one small adapter
whether the action and the Oracle receipt bundle match exactly.

## Action Binding Shape

```json
{
  "schema": "zenodex.oracle.consumer_action_binding.v1",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_critical_read",
  "action_id": "sha256:...",
  "action_epoch": 102,
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "required_evidence_floor": "O3",
  "max_freshness_window_epochs": 4,
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "critical": true
}
```

Allowed action fields are exactly:

- `schema`
- `consumer_module`
- `action_kind`
- `action_id`
- `action_epoch`
- `query_id`
- `value_hash`
- `required_evidence_floor`
- `max_freshness_window_epochs`
- `read_receipt_id`
- `consumer_action_receipt_id`
- `critical`

Unknown fields reject. Local action files above `250_000` bytes are treated as
`inconclusive` before JSON parsing. Local bundle files above `1_000_000` bytes
are also treated as `inconclusive`.

## Consumer Profile Shape

```json
{
  "schema": "zenodex.oracle.consumer_profile.v1",
  "profile_id": "sha256:...",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_critical_read",
  "query_id": "sha256:...",
  "required_evidence_floor": "O3",
  "max_freshness_window_epochs": 4,
  "critical": true
}
```

Allowed profile fields are exactly:

- `schema`
- `profile_id`
- `consumer_module`
- `action_kind`
- `query_id`
- `required_evidence_floor`
- `max_freshness_window_epochs`
- `critical`

Every profile ID is content-addressed:

```text
profile_id := sha256(canonical_json(profile without profile_id))
```

Plain English: the profile commits to the module/action/query policy. If a
consumer changes its required evidence floor or freshness limit, the profile ID
must change.

## Adapter Law

The adapter first verifies the receipt bundle using
`tools/zenodex_oracle.py`. Then it compares the accepted bundle facts against
the downstream action binding:

```text
OracleUseOK(action, bundle) ->
  BundleAccepted
  and action.critical = true
  and action.consumer_module = bundle.consumer_module
  and action.action_kind = bundle.action_kind
  and action.action_id = bundle.action_id
  and action.action_epoch = bundle.action_epoch
  and action.query_id = bundle.query_id
  and action.value_hash = bundle.value_hash
  and action.read_receipt_id = bundle.read_receipt_id
  and action.consumer_action_receipt_id = bundle.consumer_action_receipt_id
  and bundle.evidence_class >= action.required_evidence_floor
  and bundle.freshness_window_epochs <= action.max_freshness_window_epochs
```

Plain English: the action cannot borrow a receipt from another module, action
kind, action ID, query, value, epoch, read receipt, or consumer-action receipt.
It also cannot accept weaker evidence or a looser freshness window than the
action itself declares.

When a profile is supplied, the action must also satisfy:

```text
ProfileBoundAction(action, profile) ->
  profile.critical = true
  and action.consumer_module = profile.consumer_module
  and action.action_kind = profile.action_kind
  and action.query_id = profile.query_id
  and action.required_evidence_floor >= profile.required_evidence_floor
  and action.max_freshness_window_epochs <= profile.max_freshness_window_epochs
```

Plain English: the action cannot set its own weaker policy. It must be at least
as strict as the published profile for that module, action kind, and query.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.adapter_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_critical_read",
  "action_id": "sha256:...",
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "evidence_class": "O3",
  "required_evidence_floor": "O3",
  "action_epoch": 102,
  "freshness_window_epochs": 4,
  "max_freshness_window_epochs": 4,
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "profile_id": "sha256:...",
  "profile_required_evidence_floor": "O3",
  "profile_max_freshness_window_epochs": 4,
  "errors": []
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | The action and bundle satisfy the V1 adapter shell. |
| `rejected` | The action and bundle parsed, but at least one policy check failed. |
| `inconclusive` | The verifier could not load or parse the action/bundle safely. |

## Replay Commands

Generate and verify a minimal accepted action/bundle pair:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_adapter.py sample \
  --action-output "$tmp/action.json" \
  --bundle-output "$tmp/bundle.json" \
  --profile-output "$tmp/profile.json"
python3 tools/zenodex_oracle_adapter.py verify \
  --action "$tmp/action.json" \
  --bundle "$tmp/bundle.json" \
  --profile "$tmp/profile.json"
rm -rf "$tmp"
```

Run deterministic adapter chaos replay:

```bash
python3 tools/zenodex_oracle_adapter_chaos.py
```

The current adapter chaos lane covers `27` named unaccepted-bundle,
module/action/query/value/receipt mismatch, action evidence/freshness,
consumer-profile mismatch, profile weakening, non-critical, hidden-field,
schema, missing-field, and type-confusion disaster shapes. Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- all perps, production zUSD, routing, or trigger execution paths are already
  runtime-wired to the adapter;
- a live production Oracle network exists;
- reporter sources are honest;
- oracle values are true market prices;
- every future downstream action family has a final binding schema.

The claim is narrower: this first adapter shell rejects receipt borrowing and
action/bundle mismatch before a critical action can treat an Oracle receipt as
authority.
