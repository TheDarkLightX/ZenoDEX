# ZenoDEX Research Kernel Frontier Spec Selector - 2026-06-28

## Executive Result

A bounded host-side DP can convert the current-branch Research Kernel Tau frontier snapshot into a nonvacuous next-spec queue that covers host projection, counterexample synthesis, performance, compiler/search, energy-model, state-space, AB-ordering, and CoW-matching axes while dominating priority-order and single-lens baselines under the declared objective.

- Research Kernel run: `tau-spec-frontier-ebrm-20260626`
- Candidate pool: `8`
- Budget: `7`
- Axis count: `8`
- DP states: `122`
- DP/bruteforce parity: `True`
- Tau replay ok: `True`

## Selected Queue

| selected candidate |
| --- |
| `rk_counterexample_compiler_synthesis` |
| `rk_cow_capacity_extension` |
| `rk_host_projection_perf_energy_selector` |
| `rk_state_ab_ordering_witness` |

## Coverage Comparison

| selector | cost | value | axes covered | missing axes |
| --- | ---: | ---: | ---: | --- |
| exact DP | `7` | `110` | `8` | `none` |
| priority order | `7` | `91` | `5` | `state_space_reformulation, ab_ordering, cow_matching` |
| single lens | `7` | `104` | `6` | `state_space_reformulation, ab_ordering` |

## Algorithm

The host solves a budgeted max-coverage problem by DP over `(spent, axis_mask)`. The exact objective is `(all axes covered, axis count, value, negative-control count, dependency count, -cost)` with deterministic candidate-id tie-breaks.

Complexity: `O(n * B * 2^m)` time and `O(B * 2^m)` space, where `n` is candidate count, `B` is budget, and `m` is the number of frontier axes.

## Tau Boundary

`src/tau_specs/recommended/rk_frontier_spec_selector_v1.tau` admits only host-projected facts: deterministic replay, exact-DP completeness, frontier-axis coverage, baseline dominance, negative controls, runtime-subset compatibility, resource budget, Research Kernel dependencies, nonvacuity, replay evidence, and no authority effects.

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_exact_dp` | `False` | exact DP completeness is load-bearing |
| `missing_axis_coverage` | `False` | frontier-axis coverage is load-bearing |
| `missing_priority_dominance` | `False` | priority-baseline dominance is load-bearing |
| `missing_single_lens_dominance` | `False` | single-lens-baseline dominance is load-bearing |
| `missing_negative_controls` | `False` | negative controls are load-bearing |
| `missing_rk_dependencies` | `False` | Research Kernel dependency refs are load-bearing |
| `authority_effect` | `False` | the selector must not carry authority effects |

## Non-Claims

- This is an advisory research selector, not a settlement, oracle, governance, release, or repository authority.
- The candidate pool is the declared Research Kernel frontier snapshot in this receipt.
- This receipt does not supersede the broader TauSpecEBRM compounding-frontier certificate on the tokenomics POL branch.
- Tau does not query Research Kernel, score candidates, solve the DP, run tests, or promote claims.
- Selected experiments still require their own replay, proof, fuzzing, and review gates before promotion.

## Replay

```bash
python3 tools/check_rk_frontier_spec_selector.py
```
