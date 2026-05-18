# ZenoEnergy Production Promotion Gate

decision: blocked
promotion_allowed: false
scope: advisory_ranking_only
operator_release_enabled: false

```text
ProductionEligible :=
  ResearchReplayClean
  and RealUPBAReplayOK
  and RealAutoTraderShadowOK
  and OperatorRankingOnlyEnable
```

Promotion is restricted to advisory ranking. Deterministic verification
and policy guards remain authoritative for acceptance.

| obligation | result | reason |
| --- | --- | --- |
| research_replay_clean | pass | research replay, fallback, and invalid-accept receipts must be clean |
| operator_ranking_only_enable | block | operator must explicitly enable advisory ranking-only promotion |
| upba_real_replay_coverage | block | missing real UPBA replay report |
| autotrader_real_shadow_coverage | block | missing real AutoTrader shadow report |

## Blocked Reasons

- operator must explicitly enable advisory ranking-only promotion
- missing real UPBA replay report
- missing real AutoTrader shadow report

## Thresholds

| threshold | value |
| --- | ---: |
| min_upba_real_batches | 1000 |
| min_upba_real_candidates | 20000 |
| min_autotrader_real_contexts | 500 |
| min_autotrader_real_rows | 5000 |
| min_real_market_days | 7 |
| min_top25_recall | 0.99 |

## Required Real Reports

`upba_real_replay` must use schema
`zenodex/energy/upba_real_replay_report/v1` and include broad
historical-replay or production-shadow coverage, zero invalid accepts,
zero permutation violations, a passing replay source manifest, top-25
recall above threshold, and lower mean verifier calls than hand energy.

`autotrader_real_shadow` must use schema
`zenodex/energy/autotrader_real_shadow_report/v1` and include broad
historical-replay or production-shadow coverage, zero invalid accepts,
a passing replay source manifest, authoritative policy guards, no
state-root model output, top-25 recall above threshold, and lower mean
guard calls than hand energy.

## Report Builder

Use `tools/build_zenoenergy_real_replay_report.py` to construct these
report schemas from replay outputs. The builder validates source
schemas, records canonical source report hashes, rejects obvious
fixture or synthetic source descriptors, and requires deterministic
replay plus no-live-secrets attestations.

The builder is an evidence normalizer. It does not replace replay
provenance, data-custody checks, secret-scrubbing proof, or the
production promotion gate.
