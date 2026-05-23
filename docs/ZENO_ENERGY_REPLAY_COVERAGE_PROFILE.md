# ZenoEnergy Replay Coverage Profile

ZenoEnergy now has a deterministic coverage-profile checker for real replay
evidence:

```text
tools/check_zenoenergy_replay_coverage_profile.py
```

The checker validates this profile schema:

```text
zenodex/energy/replay_coverage_profile/v1
```

and emits:

```text
zenodex/energy/replay_coverage_profile_check/v1
```

The profile is a breadth guard for production-adjacent evidence. It prevents a
single narrow replay source from passing promotion only because the aggregate
batch or row counts are large.

## UPBA Profile

An UPBA profile must match the real replay report source fields and satisfy:

| field | minimum |
| --- | ---: |
| pool_count | 3 |
| intent_size_bucket_count | 3 |
| candidate_family_count | 4 |
| hard_negative_family_count | 4 |
| min_batches_per_market_day | 50 |

The profile must also match `source_kind`, `source_descriptor`,
`market_day_count`, and the number of hashed source reports in the real replay
report.

Example:

```json
{
  "schema": "zenodex/energy/replay_coverage_profile/v1",
  "profile_type": "upba",
  "source_kind": "production-shadow",
  "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
  "market_day_count": 9,
  "source_report_count": 1,
  "batch_count": 1250,
  "pool_count": 4,
  "intent_size_bucket_count": 3,
  "candidate_family_count": 5,
  "hard_negative_family_count": 4,
  "min_batches_per_market_day": 75
}
```

## AutoTrader Profile

An AutoTrader profile must match the real shadow report source fields and
satisfy:

| field | minimum |
| --- | ---: |
| strategy_family_count | 3 |
| guard_family_count | 4 |
| decision_family_count | 3 |
| min_contexts_per_market_day | 20 |

Example:

```json
{
  "schema": "zenodex/energy/replay_coverage_profile/v1",
  "profile_type": "autotrader",
  "source_kind": "production-shadow",
  "source_descriptor": "prod-shadow:autotrader:2026-05-01..2026-05-09",
  "market_day_count": 9,
  "source_report_count": 1,
  "context_count": 700,
  "strategy_family_count": 3,
  "guard_family_count": 4,
  "decision_family_count": 3,
  "min_contexts_per_market_day": 50
}
```

## Command

```bash
python3 tools/check_zenoenergy_replay_coverage_profile.py \
  --real-report data/private/upba_real_replay_report.json \
  --coverage-profile data/private/upba_replay_coverage_profile.json \
  --output-json data/private/upba_replay_coverage_profile_check.json
```

The real replay report builder can attach a passing summary directly:

```bash
python3 tools/build_zenoenergy_real_replay_report.py upba \
  --benchmark-report data/private/upba_replay_benchmark.json \
  --source-manifest data/private/upba_replay_source_manifest.json \
  --coverage-profile data/private/upba_replay_coverage_profile.json \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --output-json data/private/upba_real_replay_report.json
```

## Limits

The profile is deterministic and replayable, but it is still an evidence
normalizer. It checks declared breadth counts against the report envelope. It
does not prove that production traffic is representative, that collection
custody was truthful, or that external logs are complete.

The production promotion gate still requires deterministic verification,
source-manifest checks, zero invalid accepts, top-25 recall, learned-versus-hand
improvement, and operator ranking-only enablement.
