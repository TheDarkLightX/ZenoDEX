# Zeno Oracle Source Diversity V1

Status: first public local verifier format for declared Oracle source diversity.

This document describes the narrow source-classification receipt currently
accepted by:

```text
python3 tools/zenodex_oracle_source_diversity.py verify <receipt>
```

The format is deliberately conservative. It does not prove that sources are
honest or economically independent in the real world. It does prevent the first
`median_3` shell from treating three different strings as independent sources
unless those strings are bound to distinct declared operators, venues, data
families, transports, and jurisdictions.

## Receipt Shape

```json
{
  "schema": "zenodex.oracle.source_diversity.v1",
  "source_set_id": "sha256:...",
  "query_id": "sha256:...",
  "min_sources": 3,
  "min_operators": 3,
  "min_venues": 3,
  "min_data_families": 3,
  "min_transports": 3,
  "min_jurisdictions": 3,
  "max_same_operator": 1,
  "max_same_venue": 1,
  "max_same_data_family": 1,
  "max_same_transport": 1,
  "max_same_jurisdiction": 1,
  "sources": []
}
```

Allowed top-level fields are exactly the fields shown above. Unknown fields
reject. Local source-diversity files above `500_000` bytes are treated as
`inconclusive` before JSON parsing.

## Source Shape

Each source object has exactly these fields:

```json
{
  "source_id": "source.dex.pool.local",
  "operator_id": "operator.dex",
  "venue_id": "venue.zenodex",
  "data_family_id": "family.onchain.dex",
  "transport_id": "transport.local.node",
  "jurisdiction_id": "jurisdiction.us"
}
```

Plain English: a source is not just a name. It must declare who operates it,
which venue it represents, what kind of data it contributes, how it is
transported, and which jurisdiction bucket it belongs to.

## Source Set ID

The source set ID is content-addressed:

```text
source_set_id := sha256(canonical_json(source set without source_set_id))
```

Plain English: the ID commits to the full source policy. If the operator,
venue, data family, transport, jurisdiction, thresholds, or query binding
changes, the source-set ID must also change.

## Acceptance Rules

Let `S` be the source list. Acceptance requires:

```text
|S| >= min_sources
distinct(source_id) = |S|
distinct(operator_id) >= min_operators
distinct(venue_id) >= min_venues
distinct(data_family_id) >= min_data_families
distinct(transport_id) >= min_transports
distinct(jurisdiction_id) >= min_jurisdictions
```

Plain English: the receipt must contain enough sources, no source ID can be
duplicated, and the declared diversity must meet every minimum dimension.

Acceptance also requires:

```text
max_count(operator_id) <= max_same_operator
max_count(venue_id) <= max_same_venue
max_count(data_family_id) <= max_same_data_family
max_count(transport_id) <= max_same_transport
max_count(jurisdiction_id) <= max_same_jurisdiction
```

Plain English: no single operator, venue, data family, transport, or
jurisdiction bucket may dominate the source set beyond the declared policy.

## Median3 Binding

The current `median_3` aggregate embeds a source-diversity receipt and requires
the aggregate's three report `source_id` values to match the source-diversity
source set exactly.

```text
Median3Accepted ->
  SourceDiversityAccepted
  and report_source_ids = source_diversity_source_ids
```

Plain English: the aggregate does not merely check that report source strings
are distinct. It checks that those source strings are the same sources covered
by the declared diversity receipt.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.source_diversity_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "source_set_id": "sha256:...",
  "query_id": "sha256:...",
  "source_count": 3,
  "distinct_operator_count": 3,
  "distinct_venue_count": 3,
  "distinct_data_family_count": 3,
  "distinct_transport_count": 3,
  "distinct_jurisdiction_count": 3,
  "max_operator_concentration": 1,
  "max_venue_concentration": 1,
  "max_data_family_concentration": 1,
  "max_transport_concentration": 1,
  "max_jurisdiction_concentration": 1,
  "errors": []
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | The local source-diversity receipt satisfies the V1 shell. |
| `rejected` | The receipt parsed, but at least one policy check failed. |
| `inconclusive` | The verifier could not load or parse the receipt safely. |

## Replay Commands

Generate and verify a minimal accepted source-diversity receipt:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_source_diversity.py sample --output "$tmp/source-diversity.json"
python3 tools/zenodex_oracle_source_diversity.py verify "$tmp/source-diversity.json"
rm -rf "$tmp"
```

Run deterministic source-diversity chaos replay:

```bash
python3 tools/zenodex_oracle_source_diversity_chaos.py
```

The current source-diversity chaos lane covers `16` named source-set hash,
duplicate-source, operator, venue, data-family, transport, jurisdiction,
hidden-field, schema, type-confusion, and malformed-source disaster shapes.
Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- any source is honest;
- declared operators, venues, or jurisdictions are independently audited;
- one organization cannot secretly control multiple declared entities;
- the median is the true market price;
- a production Zeno Oracle network is live.

The claim is narrower: accepted Oracle source sets must expose and satisfy a
declared diversity policy before they can back the first `median_3` aggregate
shell.
