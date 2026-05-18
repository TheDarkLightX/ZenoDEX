# ZenoEnergy Production Evidence Bundle

ZenoEnergy now has a single evidence-bundle command for production-adjacent
review:

```text
tools/build_zenoenergy_production_evidence_bundle.py
```

It assembles:

```text
zenodex/energy/upba_real_replay_report/v1
zenodex/energy/autotrader_real_shadow_report/v1
zenodex/energy/replay_source_manifest_check/v1
zenodex/energy/production_promotion_gate/v1
```

The emitted bundle schema is:

```text
zenodex/energy/production_evidence_bundle/v1
```

## Command

```bash
python3 tools/build_zenoenergy_production_evidence_bundle.py \
  --upba-benchmark-report data/private/upba_replay_benchmark.json \
  --upba-source-manifest data/private/upba_replay_source_manifest.json \
  --upba-source-kind production-shadow \
  --upba-source-descriptor prod-shadow:2026-05-01..2026-05-09 \
  --upba-market-day-count 9 \
  --autotrader-shadow-bridge-report data/private/autotrader_shadow_bridge.json \
  --autotrader-source-manifest data/private/autotrader_replay_source_manifest.json \
  --autotrader-source-kind production-shadow \
  --autotrader-source-descriptor prod-shadow:autotrader:2026-05-01..2026-05-09 \
  --autotrader-market-day-count 9 \
  --deterministic-replay-ok \
  --no-live-secrets \
  --operator-release-enable \
  --output-json data/private/zenoenergy_production_evidence_bundle.json \
  --output-markdown data/private/zenoenergy_production_evidence_bundle.md
```

UPBA may also use separate learned and hand reports:

```bash
python3 tools/build_zenoenergy_production_evidence_bundle.py \
  --upba-learned-report data/private/upba_learned_eval.json \
  --upba-hand-report data/private/upba_hand_eval.json \
  ...
```

## Release Contract

```text
ProductionEvidenceBundle :=
  UPBARealReplayReport
  and AutoTraderRealShadowReport
  and ReplaySourceManifestChecks
  and ProductionPromotionGate
```

A passing bundle can only support advisory ranking. The deterministic UPBA
verifier and AutoTrader policy guards remain authoritative for acceptance.

## Fail-Closed Behavior

The bundle command exits with code `2` when source manifests fail, source
descriptors look synthetic or fixture-like, required replay/secret attestations
are missing, or report schemas are incompatible.

If evidence is well-formed but still insufficient, the command writes a bundle
with `decision: blocked`. Missing operator enable, inadequate real coverage, or
learned ordering failing to beat hand ordering are gate blocks, not malformed
evidence.

## Limits

The bundle is an evidence assembler. It records canonical source report hashes,
source manifest checks, real replay summaries, and the promotion gate decision.
It cannot prove external custody, truthful collection, or the completeness of
logs outside the manifest.

Production readiness still depends on real or production-shadow replay:

| surface | minimum |
| --- | ---: |
| UPBA real replay batches | 1000 |
| UPBA real replay candidates | 20000 |
| AutoTrader real shadow contexts | 500 |
| AutoTrader real shadow rows | 5000 |
| market days | 7 |
| top-25 recall | 0.99 |

The scorer stays outside consensus, state roots, settlement validity, and policy
validity.
