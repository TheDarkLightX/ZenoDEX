# Disaster Hardness and Assurance Metric

Status: current public metric for bounded disaster-state hardening. Production
readiness still depends on the open ZenoOracle and ZenoProof production gates.

The Disaster Hardness and Assurance Index, `DHAI`, is a 100-point metric based
on replayable disaster-state statistics. It is designed to answer two separate
questions with one headline number:

- hardness: how much adversarial pressure the current public evidence survived;
- assurance: how much of the named disaster-state frontier is closed, replayed,
  and attached to proof schemas.

## Formula

```text
DHAI :=
  min(ProductionBlockerCap,
      PromotedClosure
    + FrontierExposure
    + WitnessReduction
    + ProofSchemaCoverage
    + SearchPressure)
```

The current `ProductionBlockerCap` is `84/100` while live Oracle production
network evidence, live economics settlement, ZenoProof production governance,
production code signing, verifier sandboxing, and broader generalized proof
coverage remain open.

| Component | Weight | Current value | Points |
| --- | ---: | ---: | ---: |
| Promoted closure | 30 | `(29 + 17 + 65) / (29 + 17 + 65)` | `30.0` |
| Frontier exposure | 25 | `29 / 125` | `5.8` |
| Witness reduction | 20 | `(43 - 0) / 43` | `20.0` |
| Proof-schema coverage | 15 | `29 / 29` | `15.0` |
| Search pressure | 10 | `min(1, 1,700,256 / 1,000,000)` | `10.0` |

Current score:

```text
raw_score = 80.8 / 100
DHAI = 80.8 / 100
rounded_readme_score = 81 / 100
level = L3_STRONG_BOUNDED_DISASTER_HARDENING
```

The production blocker cap is not currently binding because the raw score is
below `84`. It prevents the metric from entering the production-candidate range
until the live production blockers are closed.

## Current Statistics

| Lane | Statistic | Current value |
| --- | --- | ---: |
| Core public disaster receipt | closed axes | `29` |
| Core public disaster inventory | known axes | `125` |
| Core public disaster inventory | open axes | `96` |
| ZenoOracle devnet disaster harness | selected states | `17` |
| ZenoOracle devnet disaster harness | unreachable states | `17` |
| MacOS scout witness space | materialized witnesses | `65` |
| MacOS scout witness space | pre-hardening reachable witnesses | `43` |
| MacOS scout witness space | post-hardening reachable witnesses | `0` |
| Closed-axis proof-schema map | mapped closed axes | `29` |
| MacOS compute campaign | screened candidates | `1,700,256` |

The headline value is strong because every promoted bounded disaster family in
these lanes is currently closed, the MacOS scout witness space went from `43`
reachable witnesses to `0`, and every closed core axis has a proof-schema
attachment. The score remains below production-candidate status because the
core public inventory still names `96` open search axes and the live production
gates remain outside the public closure claim.

## Level Scale

| Level | Score range | Meaning |
| --- | ---: | --- |
| `L0_NAMED_RISK_INVENTORY` | `0-39` | named risks exist, replay evidence is too thin |
| `L1_REPLAY_SEEDED` | `40-59` | some public replay exists, frontier exposure is weak |
| `L2_BOUNDED_REPLAY_SUPPORTED` | `60-74` | replayed closures dominate the promoted slice |
| `L3_STRONG_BOUNDED_DISASTER_HARDENING` | `75-84` | strong bounded closure with explicit open production blockers |
| `L4_PRODUCTION_CANDIDATE_DISASTER_ASSURANCE` | `85-94` | live production-candidate gates and broader frontier closure |
| `L5_PRODUCTION_OPERATIONAL_DISASTER_ASSURANCE` | `95-100` | live operational evidence, signing, sandboxing, monitoring, and formal replay are all active |

## Replay Commands

```bash
python3 tools/check_disaster_hardness_assurance_metric.py --format text
python3 tools/check_disaster_search_closed_receipt.py
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
python3 tools/check_disaster_proof_schema_map.py
python3 tools/macos_scout/build_witness_space_receipt.py \
  --run-dir tests/fixtures/macos_scout/post_hardening_zero \
  --blocked-run-dir tests/fixtures/macos_scout/pre_hardening_blocked \
  --require-clean \
  --format text
```

## How To Raise The Score

The fastest way to raise `DHAI` is to close more of the `125` named public
disaster axes. Each promoted closed axis increases the frontier-exposure
component. The next durable gains come from turning the proof schemas into
concrete Lean or SMT instantiations for specific Oracle, proof-market, perps,
settlement, and routing objects.

The score can enter `L4` only after the production blocker cap is lifted. That
requires production Oracle network evidence, live reporter economics settlement,
ZenoProof verifier sandboxing, production code signing, verifier release
transparency, revocation drills, and proof-market settlement gates.

## Non-Claims

This metric does not claim exhaustive disaster-state closure, a live production
Oracle network, a live ZenoProof market, or unbounded formal proof coverage. It
is a compact public measure of the current bounded disaster-hardening surface.
