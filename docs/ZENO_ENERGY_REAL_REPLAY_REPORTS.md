# ZenoEnergy Real Replay Reports

ZenoEnergy promotion now has a deterministic report builder for the two real
evidence schemas consumed by the production gate:

```text
zenodex/energy/upba_real_replay_report/v1
zenodex/energy/autotrader_real_shadow_report/v1
```

The tool is:

```text
tools/build_zenoenergy_real_replay_report.py
```

It validates input report schemas, records canonical SHA-256 hashes for source
reports, rejects obvious fixture or synthetic source descriptors, requires a
deterministic replay attestation, and requires a no-live-secrets attestation.
For production promotion, pass `--source-manifest` so the report carries a
passing `zenodex/energy/replay_source_manifest_check/v1` summary. The production
promotion gate still decides whether coverage and performance are sufficient.

Source manifest details:
[ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md](./ZENO_ENERGY_REPLAY_SOURCE_MANIFEST.md)

## UPBA

UPBA real replay can be built from a benchmark report:

```bash
python3 tools/build_zenoenergy_real_replay_report.py upba \
  --benchmark-report data/private/upba_replay_benchmark.json \
  --source-manifest data/private/upba_replay_source_manifest.json \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --output-json data/private/upba_real_replay_report.json
```

It may also be built from separate learned and hand evaluation reports:

```bash
python3 tools/build_zenoenergy_real_replay_report.py upba \
  --learned-report data/private/upba_learned_eval.json \
  --hand-report data/private/upba_hand_eval.json \
  --source-manifest data/private/upba_replay_source_manifest.json \
  --source-kind historical-replay \
  --source-descriptor historical-replay:2026-04-20..2026-04-27 \
  --market-day-count 7 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --output-json data/private/upba_real_replay_report.json
```

The generated report includes:

```text
batch_count
candidate_count
market_day_count
invalid_accept_count
permutation_violation_count
top_25_recall
top_25_objective_recall
learned_mean_verifier_calls
hand_mean_verifier_calls
source_reports[].sha256
```

## AutoTrader

AutoTrader real shadow reports are built from the shadow bridge receipt:

```bash
python3 tools/build_zenoenergy_real_replay_report.py autotrader \
  --shadow-bridge-report data/private/autotrader_shadow_bridge.json \
  --source-manifest data/private/autotrader_replay_source_manifest.json \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:autotrader:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --output-json data/private/autotrader_real_shadow_report.json
```

The builder rejects the built-in AutoTrader fixture source, because that fixture
is useful for boundary replay and schema checks while lacking production
distribution coverage.

## Promotion

The production gate remains the release decision point:

```bash
python3 tools/check_zenoenergy_production_promotion.py \
  --upba-real-replay data/private/upba_real_replay_report.json \
  --autotrader-real-shadow data/private/autotrader_real_shadow_report.json \
  --operator-release-enable
```

The builder does not prove the source descriptor is truthful. It records the
source assertion, input hashes, and safety attestations in a stable format so the
gate can replay the decision. Data custody, replay job provenance, and secret
scrubbing remain operational obligations.
