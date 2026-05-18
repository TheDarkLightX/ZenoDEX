# ZenoEnergy Replay Secret Scan

The replay secret scanner checks real replay report artifacts before they are
bound into a replay source manifest:

```text
tools/check_zenoenergy_replay_secret_scan.py
```

It emits:

```text
zenodex/energy/replay_secret_scan/v1
```

The scanner is intentionally small and deterministic. It flags obvious private
key material, common API-token patterns, and sensitive JSON keys such as
`private_key`, `api_key`, `secret_key`, `mnemonic`, `seed_phrase`, and
`access_token`.

## Example

```bash
python3 tools/check_zenoenergy_replay_secret_scan.py \
  --source-report data/private/upba_replay_benchmark.json \
  --source-report data/private/autotrader_shadow_bridge.json \
  --output-json data/private/zenoenergy_replay_secret_scan.json \
  --output-markdown data/private/zenoenergy_replay_secret_scan.md
```

Then pass the clean scan into the manifest builder:

```bash
python3 tools/build_zenoenergy_replay_source_manifest.py \
  --manifest-id prod-shadow-upba-20260501-20260509 \
  --source-kind production-shadow \
  --source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --market-day-count 9 \
  --source-report upba-benchmark=data/private/upba_replay_benchmark.json \
  --deterministic-replay-ok \
  --no-live-secrets \
  --secret-scan-report data/private/zenoenergy_replay_secret_scan.json \
  --output-json data/private/upba_replay_source_manifest.json
```

## Limits

The scanner catches obvious key material. It does not prove privacy compliance,
custody, correct redaction, or the absence of all possible secrets. It is a
deterministic guardrail that supports the `no_live_secrets` evidence path.

The scanner returns:

- exit code `0` when no findings are detected;
- exit code `1` when findings are detected;
- exit code `2` for malformed invocation or missing files.
