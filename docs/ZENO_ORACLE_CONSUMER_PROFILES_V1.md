# Zeno Oracle Consumer Profiles V1

Status: first public local verifier format for the critical consumer profile
catalog.

This document describes the narrow catalog currently accepted by:

```text
python3 tools/zenodex_oracle_consumer_profiles.py verify <catalog>
```

The goal is to stop critical modules from silently inventing weaker Oracle
requirements. The adapter can compare a concrete action against a profile; this
catalog verifies the profiles themselves for the first named ZenoDEX consumers.

## Catalog Shape

```json
{
  "schema": "zenodex.oracle.consumer_profile_catalog.v1",
  "profiles": []
}
```

Allowed top-level fields are exactly:

- `schema`
- `profiles`

Unknown fields reject. Local catalog files above `500_000` bytes are treated as
`inconclusive` before JSON parsing.

## Profile Shape

Profiles reuse the adapter profile shape:

```json
{
  "schema": "zenodex.oracle.consumer_profile.v1",
  "profile_id": "sha256:...",
  "consumer_module": "zenodex.perps",
  "action_kind": "settle_epoch",
  "query_id": "sha256:...",
  "required_evidence_floor": "O3",
  "max_freshness_window_epochs": 2,
  "critical": true
}
```

Every profile ID is content-addressed:

```text
profile_id := sha256(canonical_json(profile without profile_id))
```

Plain English: the profile ID commits to the consumer module, action kind,
query, evidence floor, freshness window, and critical flag.

## Required First-Shell Profiles

The first catalog is intentionally closed. It must contain exactly these
consumer/action profiles:

| Consumer Module | Action Kind | Evidence Floor | Max Freshness Window |
| --- | --- | --- | --- |
| `zenodex.perps` | `settle_epoch` | `O3` | `2` |
| `zenodex.perps` | `liquidate_account` | `O3` | `1` |
| `zenodex.zusd` | `mint` | `O3` | `2` |
| `zenodex.zusd` | `liquidate_vault` | `O3` | `1` |
| `zenodex.routing` | `guarded_quote` | `O3` | `4` |
| `zenodex.trigger` | `execute_trigger` | `O3` | `2` |

The profile query IDs are deterministic `sha256:` identifiers for the current
design-level query families:

- perps index price;
- zUSD collateral price;
- routing reference price;
- trigger reference price.

These query IDs are stable inside this V1 shell, but they are not yet the final
production query registry.

## Catalog Law

```text
CatalogAccepted ->
  exactly_required_profiles
  and each_profile_id_matches_body
  and no_duplicate_profile_key
  and no_duplicate_profile_id
  and each_profile_is_critical
  and each_profile_query_matches_required_query
  and each_profile_evidence_floor >= required_floor
  and each_profile_freshness_window <= required_window
```

Plain English: the catalog cannot omit a critical profile, add an unsupported
profile, duplicate a profile, weaken evidence, loosen freshness, or point a
consumer action at the wrong query.

## Replay Commands

Generate and verify a minimal accepted catalog:

```bash
tmp=$(mktemp -d)
python3 tools/zenodex_oracle_consumer_profiles.py sample --output "$tmp/catalog.json"
python3 tools/zenodex_oracle_consumer_profiles.py verify "$tmp/catalog.json"
rm -rf "$tmp"
```

Run deterministic consumer-profile chaos replay:

```bash
python3 tools/zenodex_oracle_consumer_profiles_chaos.py
```

The current consumer-profile chaos lane covers `14` named missing-profile,
duplicate-profile, hash-forgery, unsupported-profile, wrong-query, weak
evidence, loose freshness, non-critical, schema, hidden-field, and
type-confusion disaster shapes. Details are tracked in
[ZENO_ORACLE_CHAOS_ENGINEERING.md](ZENO_ORACLE_CHAOS_ENGINEERING.md).

## Non-Claims

This verifier does not claim:

- the runtime perps, zUSD, routing, or trigger modules are wired to the adapter;
- the query registry is final;
- the chosen freshness windows are production-final;
- a live production Oracle network exists;
- oracle values are true market prices.

The claim is narrower: this first catalog shell rejects weakened or malformed
critical consumer profiles before those profiles can be used as adapter policy.
