# ZenoEnergy Replay Source Manifest Builder

The manifest builder creates `zenodex/energy/replay_source_manifest/v1` files
from real replay reports:

```text
tools/build_zenoenergy_replay_source_manifest.py
```

It computes canonical JSON SHA-256 hashes for source reports, records source
kind and market-day coverage, attaches deterministic replay and clean
secret-scan attestations, and immediately runs the replay source manifest
checker. The command writes the manifest only when the local check passes.

## Example

```bash
python3 tools/build_zenoenergy_replay_source_manifest.py \
  --manifest-id prod-shadow-upba-20260501-20260509 \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --source-report upba-benchmark=data/private/upba_replay_benchmark.json \
  --deterministic-replay-ok \
  --no-live-secrets \
  --secret-scan-tool local-secret-scan-v1 \
  --secret-scan-ok \
  --secret-scan-finding-count 0 \
  --output-json data/private/upba_replay_source_manifest.json \
  --output-check-json data/private/upba_replay_source_manifest_check.json
```

For AutoTrader:

```bash
python3 tools/build_zenoenergy_replay_source_manifest.py \
  --manifest-id prod-shadow-autotrader-20260501-20260509 \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:autotrader:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --source-report autotrader-shadow-bridge=data/private/autotrader_shadow_bridge.json \
  --deterministic-replay-ok \
  --no-live-secrets \
  --secret-scan-tool local-secret-scan-v1 \
  --secret-scan-ok \
  --secret-scan-finding-count 0 \
  --output-json data/private/autotrader_replay_source_manifest.json
```

## Fail-Closed Rules

The builder exits with code `2` and does not write the manifest when:

- no source report is supplied;
- a source report path is missing;
- the descriptor is synthetic, fixture-like, built-in, or generated;
- deterministic replay is not attested;
- no-live-secrets is not attested;
- the secret scan is missing, dirty, or reports findings;
- the generated artifact hashes fail the manifest checker.

The builder is an operator intake helper. It does not prove external custody,
truthful collection, log completeness, or correct redaction policy.

## Production Flow

```text
real replay report
-> replay source manifest builder
-> replay source manifest checker
-> real replay report builder
-> production evidence bundle
-> production promotion gate
```

This keeps source hashing and manifest validation deterministic while leaving
the real-data custody obligations explicit.
