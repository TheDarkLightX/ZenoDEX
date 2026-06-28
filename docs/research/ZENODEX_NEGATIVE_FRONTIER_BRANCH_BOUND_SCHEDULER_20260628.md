# ZenoDEX Negative-Frontier Branch-Bound Scheduler - 2026-06-28

## Executive Result

A branch-and-bound exact negative-frontier scheduler can preserve brute-force oracle parity on bounded ZenoDEX falsifier-campaign scenarios while replaying larger duplicate-stress cases with safe pruning-bound evidence and materially fewer evaluated leaves than raw combination enumeration.

- Scenarios: `9`
- Oracle-compared scenarios: `8`
- Oracle-skipped large scenarios: `1`
- Max raw combinations: `8936928`
- Max branch-bound nodes: `310981`
- Leaf reduction range: `2.07x` to `62.97x`
- Tau replay ok: `True`

## Scenario Table

| scenario | candidates | combinations | nodes | leaves | leaf reduction | oracle match |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `exact_base_frontier` | `12` | `792` | `387` | `116` | `6.83x` | `True` |
| `exact_greedy_overlap_alpha` | `8` | `56` | `111` | `27` | `2.07x` | `True` |
| `exact_greedy_overlap_beta` | `8` | `56` | `81` | `20` | `2.80x` | `True` |
| `exact_greedy_overlap_gamma` | `8` | `56` | `97` | `20` | `2.80x` | `True` |
| `exact_greedy_overlap_delta` | `8` | `56` | `111` | `27` | `2.07x` | `True` |
| `exact_recency_duplicate_trap` | `16` | `4368` | `1491` | `521` | `8.38x` | `True` |
| `exact_stable_random_duplicate_trap` | `17` | `6188` | `1425` | `551` | `11.23x` | `True` |
| `medium_duplicate_stress` | `36` | `376992` | `40973` | `17370` | `21.70x` | `True` |
| `large_duplicate_stress` | `66` | `8936928` | `310981` | `141929` | `62.97x` | `None` |

## Pruning Certificate

Each branch is pruned only when its replayed optimistic upper bound is strictly below the incumbent frontier key. The replay records `unsafe_prune_count=0` for every scenario.

## Tau Boundary

`src/tau_specs/recommended/negative_frontier_branch_bound_scheduler_v1.tau` admits only host-projected facts: deterministic replay, bounded oracle parity, pruning-bound validity, node reduction, large-case replay, baseline dominance, coverage, mutation checks, resource budget, nonvacuity, and no authority effects.

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_oracle_parity` | `False` | bounded oracle parity is load-bearing |
| `missing_pruning_bounds` | `False` | pruning-bound evidence is load-bearing |
| `missing_node_reduction` | `False` | node-reduction evidence is load-bearing |
| `missing_large_case` | `False` | large-case replay is load-bearing |
| `missing_baseline_dominance` | `False` | baseline dominance is load-bearing |
| `authority_effect` | `False` | advisory scheduler must not have authority effects |

## Non-Claims

- This is an advisory research scheduler, not a production security, governance, or settlement mechanism.
- Large-case exactness is supported by the replayed branch-and-bound pruning certificate, not by an external theorem.
- Tau does not enumerate combinations, compute entropy, choose tasks, run fuzzers, or authorize repository changes.

## Replay

```bash
python3 tools/check_negative_frontier_branch_bound_scheduler.py
```
