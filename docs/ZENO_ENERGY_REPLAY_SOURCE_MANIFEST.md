# ZenoEnergy Replay Source Manifest

Real ZenoEnergy replay evidence now has a source manifest schema:

```text
zenodex/energy/replay_source_manifest/v1
```

The checker is:

```text
tools/check_zenoenergy_replay_source_manifest.py
```

The manifest records the operational source boundary behind a real replay or
shadow report:

```text
source_kind
source_descriptor
market_day_count
deterministic_replay_ok
no_live_secrets
secret_scan
artifacts[].schema
artifacts[].sha256
```

The checker emits:

```text
zenodex/energy/replay_source_manifest_check/v1
```

Production promotion requires real reports to carry a passing manifest check.

## Example

```json
{
  "schema": "zenodex/energy/replay_source_manifest/v1",
  "manifest_id": "prod-shadow-upba-20260501-20260509",
  "source_kind": "production-shadow",
  "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
  "market_day_count": 9,
  "deterministic_replay_ok": true,
  "no_live_secrets": true,
  "secret_scan": {
    "tool": "local-secret-scan-v1",
    "ok": true,
    "finding_count": 0
  },
  "artifacts": [
    {
      "name": "upba-benchmark",
      "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
      "sha256": "..."
    }
  ]
}
```

Validate it against source reports:

```bash
python3 tools/check_zenoenergy_replay_source_manifest.py \
  --manifest data/private/upba_replay_source_manifest.json \
  --source-report data/private/upba_replay_benchmark.json \
  --output-json data/private/upba_replay_source_manifest_check.json
```

Then build the real replay report:

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

## Limits

The manifest binds hashes and attestations into the replay evidence path. It
does not prove external custody, truthful collection, or the absence of data
that never entered the manifest. Those remain operator and audit obligations.

The checker rejects obvious fixture, synthetic, built-in, and generated source
descriptors. That catches accidental promotion of research fixtures. It cannot
detect a dishonest descriptor string without external custody evidence.
