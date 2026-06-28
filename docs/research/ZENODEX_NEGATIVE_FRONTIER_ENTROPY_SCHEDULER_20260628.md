# ZenoDEX Negative-Frontier Entropy Scheduler - 2026-06-28

## Executive Result

A deterministic advisory scheduler ranks falsifier campaign axes by severity-preserving entropy gain over recent negative-family history.

The scheduler has no settlement, governance, production-claim, or runtime authority.

- Bounded corpus axes: `125`
- Eligible axes: `20`
- Budget: `10`
- Entropy unique families: `14`
- Recency unique families: `12`
- Stable-random unique families: `7`
- Entropy priority floor: `50`

## Entropy Schedule

| rank | axis | priority | families |
| ---: | --- | ---: | --- |
| `1` | `identity_registry_drift` | `92` | `identity_nonce, other_negative_family, wallet_authority` |
| `2` | `serialization_width_aliasing` | `88` | `canonicalization, serialization` |
| `3` | `epoch_split_brain` | `96` | `other_negative_family, settlement_semantics` |
| `4` | `market_namespace_version_isolation` | `64` | `other_negative_family, perps_safety` |
| `5` | `bounded_advisory_search_envelope` | `60` | `fee_accounting, other_negative_family` |
| `6` | `confidential_receipt_attestation_drift` | `52` | `confidential_boundary, other_negative_family, receipt_binding` |
| `7` | `strategy_session_capability_replay` | `50` | `identity_nonce, other_negative_family, wallet_authority` |
| `8` | `external_state_drift` | `78` | `oracle_recovery, route_certificate, settlement_semantics` |
| `9` | `tau_gate_policy_aliasing` | `56` | `serialization, tau_policy` |
| `10` | `atomicity_partial_side_effect` | `74` | `other_negative_family, proof_mining, wallet_authority` |

## Baseline Comparison

| scheduler | unique families | post entropy | priority min |
| --- | ---: | ---: | ---: |
| `entropy` | `14` | `2.518747` | `50` |
| `recency` | `12` | `2.254158` | `52` |
| `stable_random` | `7` | `2.159578` | `50` |

## Negative Controls

| case | ok |
| --- | --- |
| `entropy_beats_recency_unique_families` | `True` |
| `entropy_beats_random_unique_families` | `True` |
| `deterministic_replay` | `True` |
| `severity_floor_preserved` | `True` |
| `authority_boundary` | `True` |

## Non-Claims

- This scheduler is advisory and does not authorize settlement, governance, production claims, or runtime route selection.
- Unique-family improvement is measured on the declared bounded disaster-search axis corpus and fixed recent-history profile.
- The scheduler ranks next falsifier tasks; it does not prove that selected tasks will find real bugs.
- Family labels are deterministic keyword projections and remain a bounded replay abstraction.

## Replay

```bash
python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py
```
