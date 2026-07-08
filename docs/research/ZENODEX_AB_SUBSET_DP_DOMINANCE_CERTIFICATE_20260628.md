# ZenoDEX AB Subset-DP Dominance Certificate - 2026-06-28

## Executive Result

A Tau host-projected certificate gates same-pool, same-direction, exact-in AB subset-DP dominance pruning by requiring bounded DP parity, brute-force parity, dominance refutation, unsupported-domain boundary witnesses, replay determinism, resource limits, nonvacuous pruning, and no authority effects.

Tau admits a research certificate only. It does not compute swaps, run DP, prune states, select AB orders, or authorize settlement.

## Tau Specification

- Spec: `src/tau_specs/recommended/ab_subset_dp_dominance_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Certificate ok: `True`

The spec requires exact-in same-direction scope, unpruned DP parity, brute-force parity, bounded dominance refutation, adversarial parity, exact-out and mixed-direction boundary witnesses, performance evidence, deterministic replay, resource budget, and no authority effects.

## Evidence Summary

| component | result | key receipt |
| --- | --- | --- |
| dominance refuter | `True` | `3959` checked pairs, `12707` suffix permutations, first counterexample `None` |
| parity reduction | `True` | `24` cases, state reduction `28.63x`, transition reduction `12.35x` |
| adversarial corpus | `True` | `33` cases, seed `2026062804`, state reduction `42.51x`, transition reduction `16.14x` |
| boundary refuter | `True` | exact-out witness `True`, mixed-direction witness `True` |

## Certificate Flags

| flag | value |
| --- | ---: |
| `adversarial_corpus_ok` | `1` |
| `boundary_refuters_ok` | `1` |
| `brute_force_parity_ok` | `1` |
| `deterministic_replay_ok` | `1` |
| `dominance_refutation_ok` | `1` |
| `no_authority_effect` | `1` |
| `nonvacuous_pruning` | `1` |
| `resource_budget_ok` | `1` |
| `same_direction_exact_in_scope_ok` | `1` |
| `state_reduction_ok` | `1` |
| `transition_reduction_ok` | `1` |
| `unpruned_parity_ok` | `1` |

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `ab_dominance_certificate_pass` | `True` | All host-computed evidence facts admit the scoped dominance-pruning certificate. |
| `parity_reject` | `True` | Missing unpruned DP parity fails closed. |
| `brute_force_reject` | `True` | Missing brute-force parity fails closed. |
| `dominance_refuter_reject` | `True` | A bounded dominance-refuter gap cannot admit the certificate. |
| `boundary_refuter_reject` | `True` | Missing unsupported-domain boundary witnesses fail closed. |
| `performance_reject` | `True` | Missing state-reduction evidence fails closed. |
| `determinism_reject` | `True` | Missing deterministic replay fails closed. |
| `authority_reject` | `True` | A certificate with authority effects is rejected. |
| `inactive_safe` | `True` | Inactive certificates do not admit while the no-authority rail remains true. |

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `parity_reject` | `False` | Missing unpruned DP parity fails closed. |
| `brute_force_reject` | `False` | Missing brute-force parity fails closed. |
| `dominance_refuter_reject` | `False` | A bounded dominance-refuter gap cannot admit the certificate. |
| `boundary_refuter_reject` | `False` | Missing unsupported-domain boundary witnesses fail closed. |
| `performance_reject` | `False` | Missing state-reduction evidence fails closed. |
| `determinism_reject` | `False` | Missing deterministic replay fails closed. |
| `authority_reject` | `False` | A certificate with authority effects is rejected. |

## Boundary Witnesses

- Exact-out: Exact-out improves user price by lowering required input, while the AB objective treats larger executed input as better.
- Mixed-direction: The same reserve tuple that is favorable for asset0-to-asset1 is unfavorable after reversing the direction to asset1-to-asset0.

These witnesses are part of the certificate boundary. They prevent reusing the exact-in dominance rule in domains where its order relation is known to fail.

## New Specification Frontier

- `src/tau_specs/recommended/ab_subset_dp_dominance_certificate_v1.tau`: Turns AB dominance-pruned subset DP into a replay-gated research lane with explicit unsupported-domain witnesses.
- `src/tau_specs/recommended/route_split_window_certificate_v1.tau`: Existing route-split rail for local-window exact-out split certificates.
- `src/tau_specs/recommended/negative_frontier_entropy_scheduler_v1.tau`: Existing frontier-selection rail for high-value falsifier campaigns.

## Non-Claims

- This artifact is a research certificate, not a production ordering change.
- The dominance rule is scoped to same-pool, same-direction, exact-in AB subset-DP states.
- Exact-out and mixed-direction counterexamples are unsupported-domain boundary witnesses.
- Passing this bounded corpus is not a machine-checked proof of universal dominance.
- Tau does not compute the DP, dominance relation, swaps, balances, hashes, or settlement effects.

## Replay

```bash
python3 tools/check_ab_subset_dp_dominance_certificate.py
```
