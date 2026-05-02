# Zeno Oracle Median3 Aggregate V1

Status: first public local verifier format for a deterministic Oracle aggregate.

This document describes the narrow `median_3` aggregate currently accepted by:

```text
python3 tools/zenodex_oracle_median3.py verify <aggregate>
```

The format is intentionally small. It is the first replayable aggregation shell,
not a live production reporter network or a claim that the median is the true
market price.

## Aggregate Shape

```json
{
  "schema": "zenodex.oracle.median3_aggregate.v1",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "current_epoch": 104,
  "max_staleness_epochs": 10,
  "max_deviation_bps": 200,
  "min_distinct_sources": 3,
  "reports": [],
  "aggregate": {
    "value_e8": 100000000,
    "confidence_e8": 1000000,
    "deviation_bps": 100,
    "observed_epoch": 102,
    "report_count": 3
  }
}
```

Allowed top-level fields are exactly:

- `schema`
- `aggregate_id`
- `query_id`
- `current_epoch`
- `max_staleness_epochs`
- `max_deviation_bps`
- `min_distinct_sources`
- `reports`
- `aggregate`

Unknown fields reject. Local aggregate files above `500_000` bytes are treated
as `inconclusive` before JSON parsing.

## Report Shape

Each aggregate must contain exactly three report objects:

```json
{
  "report_id": "sha256:...",
  "reporter_id": "reporter.alpha",
  "source_id": "source.alpha",
  "query_id": "sha256:...",
  "value_e8": 100000000,
  "observed_epoch": 100
}
```

Allowed report fields are exactly:

- `report_id`
- `reporter_id`
- `source_id`
- `query_id`
- `value_e8`
- `observed_epoch`

Every report ID is content-addressed:

```text
report_id := sha256(canonical_json(report without report_id))
```

Plain English: a report ID commits to the report body. If the reporter, source,
query, value, or observed epoch changes, the report ID must also change.

## Aggregate ID

The aggregate ID is also content-addressed:

```text
aggregate_id := sha256(canonical_json(aggregate receipt without aggregate_id))
```

Plain English: the aggregate ID commits to the reports, policy fields, computed
median fields, and query binding.

## Aggregation Math

Let the three accepted report values be positive integers:

```text
p0, p1, p2 > 0
m := median(p0, p1, p2)
confidence_e8 := max(|p0 - m|, |p1 - m|, |p2 - m|)
deviation_bps := ceil(confidence_e8 * 10000 / m)
```

Plain English: the aggregate value is the middle price. The confidence radius
is the largest distance from any included report to that middle price. The
deviation is the same radius expressed in basis points, rounded up.

Acceptance requires:

```text
aggregate.value_e8 = m
aggregate.confidence_e8 = confidence_e8
aggregate.deviation_bps = deviation_bps
aggregate.deviation_bps <= max_deviation_bps
```

Plain English: the receipt cannot claim a nicer median, narrower confidence
radius, or lower deviation than the included reports justify.

## Freshness And Source Policy

Acceptance also requires:

```text
report.query_id = aggregate.query_id
report.observed_epoch <= current_epoch
current_epoch - report.observed_epoch <= max_staleness_epochs
distinct_reporters = 3
distinct_sources >= min_distinct_sources
```

Plain English: all reports must answer the same query, no report may come from
the future, every report must fit the staleness window, and the first shell does
not let one reporter or source masquerade as three independent reports.

## Result Shape

Verification returns:

```json
{
  "schema": "zenodex.oracle.median3_verify_result.v1",
  "ok": true,
  "status": "accepted",
  "aggregate_id": "sha256:...",
  "query_id": "sha256:...",
  "value_e8": 100000000,
  "confidence_e8": 1000000,
  "deviation_bps": 100,
  "observed_epoch": 102,
  "report_count": 3,
  "distinct_reporter_count": 3,
  "distinct_source_count": 3,
  "errors": []
}
```

Statuses:

| Status | Meaning |
| --- | --- |
| `accepted` | The local aggregate satisfies the V1 shell. |
| `rejected` | The aggregate parsed, but at least one policy check failed. |
| `inconclusive` | The verifier could not load or parse the aggregate safely. |

## Replay Commands

Generate and verify a minimal accepted aggregate:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_median3.py sample --output "$tmp/aggregate.json"
python3 tools/zenodex_oracle_median3.py verify "$tmp/aggregate.json"
rm -rf "$tmp"
```

Run deterministic aggregate chaos replay:

```bash
python3 tools/zenodex_oracle_median3_chaos.py
```

The current median_3 chaos lane covers `18` named median, confidence,
deviation, query, freshness, source, reporter, hash, schema, and hidden-field
disaster shapes. Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- the median is the true market price;
- reporters are honest;
- distinct reporter/source IDs prove real-world independence;
- signatures and on-chain reporter identity are implemented in this shell;
- a production Zeno Oracle network is live;
- higher-redundancy aggregation policies are finalized.

The claim is narrower: this first aggregate shell rejects malformed or
miscomputed `median_3` receipts before they can be promoted into accepted reads.
