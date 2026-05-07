# Zeno Oracle Feed Registry V1

Status: first local verifier contract.

The feed registry defines which Oracle feeds are admissible before reporters,
aggregates, reads, or downstream ZenoDEX actions can rely on them. A feed is not
just a symbol pair. It is a hash-stable object that binds query semantics,
source-diversity requirements, aggregate policy, report schema, freshness, and
deviation limits.

The local verifier is:

```bash
python3 tools/zenodex_oracle_feed_registry.py verify <registry>
```

To emit a minimal accepted `AGRS/ZDEX` sample:

```bash
python3 tools/zenodex_oracle_feed_registry.py sample --output /tmp/zeno-oracle-feed-registry.json
python3 tools/zenodex_oracle_feed_registry.py verify /tmp/zeno-oracle-feed-registry.json
```

## Object Shape

The root object has schema `zenodex.oracle.feed_registry.v1`:

```json
{
  "schema": "zenodex.oracle.feed_registry.v1",
  "registry_id": "sha256:...",
  "current_epoch": 10,
  "feeds": [
    {
      "schema": "zenodex.oracle.feed.v1",
      "feed_id": "sha256:...",
      "status": "active",
      "created_epoch": 10,
      "query_spec": {
        "schema": "zenodex.oracle.query_spec.v1",
        "query_id": "sha256:...",
        "query_kind": "price_e8",
        "base_asset": "agrs",
        "quote_asset": "zdex",
        "unit": "quote_per_base",
        "value_scale": 100000000
      },
      "source_diversity": {
        "schema": "zenodex.oracle.source_diversity.v1"
      },
      "aggregate_policy": {
        "schema": "zenodex.oracle.aggregate_policy.v1",
        "policy_id": "sha256:...",
        "aggregation_schema": "zenodex.oracle.admitted_median3_aggregate.v1",
        "report_schema": "zenodex.oracle.signed_report.v1",
        "evidence_floor": "O3",
        "min_reporters": 3,
        "min_sources": 3,
        "freshness_window_epochs": 4,
        "max_deviation_bps": 200
      }
    }
  ]
}
```

`registry_id`, `feed_id`, `query_id`, and `policy_id` are content hashes of the
corresponding object with that ID field omitted. The embedded
`source_diversity` object is verified by
[ZENO_ORACLE_SOURCE_DIVERSITY_V1.md](ZENO_ORACLE_SOURCE_DIVERSITY_V1.md).

## Acceptance Rules

The first local verifier accepts a registry only when:

- the registry, feed, query spec, aggregate policy, and source-diversity
  objects have the expected schemas;
- all content hashes match their canonical JSON bodies;
- every feed is active and was not created in the future;
- query specs use `price_e8`, `quote_per_base`, distinct base/quote assets, and
  `value_scale = 100000000`;
- source diversity verifies and binds to the same `query_id` as the feed;
- aggregate policy uses admitted-report median3, signed-report inputs, `O3` or
  stronger evidence, at least three reporters, at least three sources, positive
  freshness, and deviation at most `10000` bps;
- feed IDs, query IDs, and source-set IDs are not duplicated in the registry;
- unknown fields fail closed.

The key local invariant is:

```text
FeedRegistryAccepted ->
  QuerySpecHashMatches
  and SourceDiversityAccepted
  and AggregatePolicyHashMatches
  and FeedHashMatches
  and NoDuplicateFeedOrQuery
```

No accepted feed can silently change its pair semantics, source policy,
aggregate policy, freshness window, deviation bound, report schema, or evidence
floor without changing a checked content hash.

## Chaos Replay

Run:

```bash
python3 tools/zenodex_oracle_feed_registry_chaos.py
```

The replay starts from one accepted `AGRS/ZDEX` feed registry and applies
single-axis mutations. The current lane rejects `26` named disaster shapes,
including:

- registry/feed/query/policy/source hash forgery;
- duplicate feed IDs and duplicate query IDs;
- base/quote aliasing;
- weak reporter/source quorums;
- zero freshness;
- excessive deviation;
- evidence-floor downgrades;
- unsupported aggregate or report schemas;
- source-diversity query mismatch;
- correlated source operators;
- future or inactive feeds;
- hidden registry, feed, query, or policy fields;
- schema downgrades and type confusion.

The expected replay summary is:

```json
{
  "schema": "zenodex.oracle.feed_registry_chaos_replay.v1",
  "ok": true,
  "baseline_status": "accepted",
  "case_count": 26,
  "rejected_case_count": 26,
  "failed_case_count": 0
}
```

## Not Claimed

This verifier does not claim:

- feed governance is live;
- any reporter network is live;
- source classifications prove real-world independence;
- a feed value is the true market price;
- the Oracle token is live;
- production ZenoDEX consumers are already runtime-wired to this registry.

This is a local, replayable admission contract for feed definitions.
