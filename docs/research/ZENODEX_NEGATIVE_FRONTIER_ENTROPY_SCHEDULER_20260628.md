# ZenoDEX Negative-Frontier Entropy Scheduler - 2026-06-28

## Executive Result

A deterministic negative-frontier entropy scheduler can select the next ZenoDEX falsifier campaigns with higher unique negative-family discovery than collapsed recency and stable-random baselines on this fixed bounded corpus, while preserving severity, AB/CoW coverage, replay, Tau runtime-subset, resource, and no-authority facts.

- Candidates: `12`
- Selection budget: `5`
- Tau replay ok: `True`
- Unique-family lift vs recency: `3`
- Unique-family lift vs stable-random: `1`
- Entropy lift vs recency: `0.3902` nats
- Entropy lift vs stable-random: `0.0870` nats

## Scheduler Comparison

| scheduler | selected tasks | unique families | entropy nats | min severity | axes |
| --- | --- | ---: | ---: | ---: | --- |
| `negative_frontier_entropy` | `ab_state_pruning`, `cow_capacity_grouped`, `tau_direct_bv_refuter`, `proof_scope_overclaim`, `route_dominance_projection` | `12` | `2.4849` | `4` | `ab`, `cow`, `proof`, `route`, `tau` |
| `collapsed_recency` | `ui_claim_scope`, `low_severity_repeat`, `route_split_plateau`, `ab_state_pruning`, `cow_capacity_grouped` | `9` | `2.0947` | `3` | `ab`, `cow`, `docs`, `route` |
| `stable_random` | `cow_capacity_grouped`, `sealed_bid_apportionment`, `tau_direct_bv_refuter`, `kpool_multiset_capacity`, `tokenomics_pol_threshold` | `11` | `2.3979` | `3` | `cow`, `kpool`, `sealed_bid`, `tau`, `tokenomics` |

## Tau Boundary

`src/tau_specs/recommended/negative_frontier_entropy_scheduler_v1.tau` admits only host-projected scheduler facts: deterministic replay, baseline lift, severity floor, AB and CoW coverage, Tau runtime-subset compatibility, negative controls, resource budget, nonvacuity, and no authority effects.

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_recency_lift` | `False` | scheduler must beat the collapsed recency baseline |
| `missing_random_lift` | `False` | scheduler must beat the stable-random baseline |
| `missing_ab_coverage` | `False` | AB frontier coverage is load-bearing |
| `missing_cow_coverage` | `False` | CoW frontier coverage is load-bearing |
| `authority_effect` | `False` | advisory scheduler must not have authority effects |

## Non-Claims

- This is an advisory research scheduler, not a production security or settlement mechanism.
- The result is bounded to the fixed corpus and seed in this replay.
- Tau does not compute entropy, choose tasks, run fuzzers, or authorize repository changes.

## Replay

```bash
python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py
```
