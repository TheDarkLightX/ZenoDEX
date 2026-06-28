# ZenoDEX Negative-Frontier Exact Scheduler - 2026-06-28

## Executive Result

A bounded exact negative-frontier scheduler can exhaustively select ZenoDEX falsifier campaigns that match or exceed greedy entropy, collapsed recency, and stable-random baselines under the declared frontier tuple on a deterministic adversarial scenario corpus, with strict wins recorded separately while preserving AB/CoW coverage, severity, resource, replay, mutation, and no-authority facts.

- Scenarios: `7`
- Selection budget: `5`
- Total combinations checked: `11572`
- Strict dominance vs greedy: `3` scenarios
- Strict dominance vs recency: `7` scenarios
- Strict dominance vs stable-random: `7` scenarios
- Tau replay ok: `True`

## Scenario Table

| scenario | candidates | combinations | exact families | greedy families | recency families | random families |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `base_frontier` | `12` | `792` | `12` | `12` | `9` | `11` |
| `greedy_overlap_alpha` | `8` | `56` | `10` | `9` | `8` | `8` |
| `greedy_overlap_beta` | `8` | `56` | `10` | `10` | `8` | `9` |
| `greedy_overlap_gamma` | `8` | `56` | `10` | `9` | `8` | `8` |
| `greedy_overlap_delta` | `8` | `56` | `10` | `9` | `8` | `8` |
| `recency_duplicate_trap` | `16` | `4368` | `12` | `12` | `2` | `11` |
| `stable_random_duplicate_trap` | `17` | `6188` | `12` | `12` | `9` | `2` |

## Exact Selector

The host enumerates every eligible `selection_budget` subset and maximizes the tuple `(AB covered, CoW covered, unique negative families, entropy nats, severity sum, axis count)`, with deterministic task-id tie-breaks.

## Tau Boundary

`src/tau_specs/recommended/negative_frontier_exact_scheduler_v1.tau` admits only host-projected facts: deterministic replay, exact-search completeness, baseline dominance, coverage, severity floor, resource budget, mutation checks, nonvacuity, and no authority effects.

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_exact_search` | `False` | exact search completeness is load-bearing |
| `missing_greedy_dominance` | `False` | greedy-baseline dominance is load-bearing |
| `missing_recency_dominance` | `False` | recency-baseline dominance is load-bearing |
| `missing_random_dominance` | `False` | stable-random dominance is load-bearing |
| `missing_coverage` | `False` | AB and CoW frontier coverage are load-bearing |
| `authority_effect` | `False` | advisory scheduler must not have authority effects |

## Non-Claims

- This is an advisory research scheduler, not a production security, governance, or settlement mechanism.
- The result is bounded to the deterministic scenario corpus, selection budget, and candidate cap in this replay.
- Tau does not enumerate combinations, compute entropy, choose tasks, run fuzzers, or authorize repository changes.

## Replay

```bash
python3 tools/check_negative_frontier_exact_scheduler.py
```
