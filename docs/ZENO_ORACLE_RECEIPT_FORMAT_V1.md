# Zeno Oracle Receipt Format V1

Status: first public local verifier format.

This document describes the narrow receipt bundle currently accepted by:

```text
python3 tools/zenodex_oracle.py verify <bundle>
```

The format is intentionally small. It is not the full future reporter network,
aggregation protocol, token reward system, or dispute system. It is the first
fail-closed object shape for letting a downstream ZenoDEX-critical action
consume an oracle read by receipt rather than by raw value.

## Bundle Shape

```json
{
  "schema": "zenodex.oracle.receipt_bundle.v1",
  "terminal": {
    "read_receipt_id": "sha256:...",
    "consumer_action_receipt_id": "sha256:..."
  },
  "receipts": []
}
```

Allowed top-level fields are exactly:

- `schema`
- `terminal`
- `receipts`

Unknown fields reject. Local bundle files above `1_000_000` bytes are treated
as `inconclusive` before JSON parsing.

## Terminal

The terminal object identifies the one accepted read and the one downstream
consumer action being verified.

Allowed terminal fields are exactly:

- `read_receipt_id`
- `consumer_action_receipt_id`

Both must be lowercase `sha256:<64 hex chars>` IDs, and they must be distinct.

## Receipt IDs

Every receipt ID is content-addressed:

```text
receipt.id := sha256(canonical_json(receipt without id))
```

Plain English: the ID commits to the receipt body. If a field changes but the
ID stays the same, the verifier rejects the receipt.

The current canonical JSON rule is:

- remove only the `id` field from the receipt object;
- encode UTF-8 JSON with sorted object keys;
- use compact separators, with no extra whitespace;
- reject values that cannot be encoded as strict JSON.

## Accepted Read Receipt

```json
{
  "id": "sha256:...",
  "type": "accepted_read_receipt",
  "status": "accepted",
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "evidence_class": "O3",
  "fresh": true,
  "observed_epoch": 100,
  "expires_at_epoch": 104,
  "dispute_clear": true,
  "uncertainty_accepted": true,
  "depends_on": []
}
```

Allowed read fields are exactly:

- `id`
- `type`
- `status`
- `query_id`
- `value_hash`
- `evidence_class`
- `fresh`
- `observed_epoch`
- `expires_at_epoch`
- `dispute_clear`
- `uncertainty_accepted`
- `depends_on`

Read acceptance requires:

```text
status = accepted
evidence_class >= O3
fresh = true
observed_epoch <= expires_at_epoch
dispute_clear = true
uncertainty_accepted = true
depends_on = []
```

Plain English: a critical consumer cannot use weak, stale, disputed,
high-uncertainty, or dependency-bearing read receipts in this first shell.

## Consumer Action Receipt

```json
{
  "id": "sha256:...",
  "type": "consumer_action_receipt",
  "status": "accepted",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_critical_read",
  "action_id": "sha256:...",
  "action_epoch": 102,
  "freshness_window_epochs": 4,
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "read_receipt_id": "sha256:...",
  "critical": true,
  "emergency_oracle_bypass": false,
  "depends_on": ["sha256:..."]
}
```

Allowed action fields are exactly:

- `id`
- `type`
- `status`
- `consumer_module`
- `action_kind`
- `action_id`
- `action_epoch`
- `freshness_window_epochs`
- `query_id`
- `value_hash`
- `read_receipt_id`
- `critical`
- `emergency_oracle_bypass`
- `depends_on`

Action acceptance requires:

```text
status = accepted
critical = true
emergency_oracle_bypass = false
read_receipt_id = terminal.read_receipt_id
query_id = read.query_id
value_hash = read.value_hash
depends_on = [read.id]
read.observed_epoch <= action_epoch <= read.expires_at_epoch
action_epoch - read.observed_epoch <= freshness_window_epochs
```

Plain English: the downstream action must be explicitly bound to one read,
one query, one value hash, one consumer module, one action kind, one action ID,
and one valid freshness window.

## Dependency Closure

The first public shell accepts only one independent read receipt and one action
receipt depending on that read. The verifier rejects:

- receipt IDs that do not equal the canonical body hash;
- missing dependencies;
- duplicate receipt IDs;
- duplicate dependency edges;
- self-dependencies;
- dependencies that appear after their consumers;
- receipts unreachable from the terminal read/action closure;
- unsupported receipt types;
- any extra reachable dependency in the action receipt.

This keeps the first format intentionally non-recursive. Richer aggregate,
source, reporter, dispute, and token receipts should be added as new explicitly
versioned types rather than hidden inside unknown fields.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.verify_result.v1",
  "ok": true,
  "status": "accepted",
  "query_id": "sha256:...",
  "value_hash": "sha256:...",
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "evidence_class": "O3",
  "consumer_module": "zenodex.oracle.sample",
  "action_kind": "sample_critical_read",
  "action_id": "sha256:...",
  "observed_epoch": 100,
  "expires_at_epoch": 104,
  "action_epoch": 102,
  "freshness_window_epochs": 4,
  "errors": [],
  "not_claimed": [
    "does_not_claim_true_market_price",
    "does_not_claim_source_honesty",
    "does_not_claim_production_network_live"
  ]
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | The local bundle satisfies the V1 shell. |
| `rejected` | The bundle parsed, but at least one policy check failed. |
| `inconclusive` | The verifier could not load or parse the bundle safely. |

## Replay Commands

Generate and verify a minimal accepted bundle:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle.py sample-bundle --output "$tmp/bundle.json"
python3 tools/zenodex_oracle.py verify "$tmp/bundle.json"
rm -rf "$tmp"
```

Run the deterministic chaos replay:

```bash
python3 tools/zenodex_oracle_chaos.py
```

Current chaos replay coverage for this shell is tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This format does not claim:

- the oracle value is the true market price;
- reporter sources are honest;
- a production Zeno Oracle network is live;
- token rewards, slashing, and disputes are implemented;
- every future receipt type has already been designed.

The claim is narrower: a critical consumer can reject raw or weak oracle use
unless a local bundle satisfies the declared V1 receipt contract.
