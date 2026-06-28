# ZenoDEX CoW Capacity-DP Certificate - 2026-06-28

## Executive Result

A Tau host-projected certificate gates bounded grouped-capacity CoW exact-DP evidence by requiring DP/brute-force parity, core-selector parity, adversarial coupled-sender cases, nonvacuous greedy lift, resource limits, deterministic replay, fallback boundaries, separation from the uncoupled assignment surface, and no settlement authority.

Tau admits a research certificate only. It does not select CoW pairs, compute matching or DP, materialize settlement, mutate balances, or authorize state roots.

## Tau Specification

- Spec: `src/tau_specs/recommended/cow_capacity_dp_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Certificate ok: `True`

## Evidence Summary

| component | result | key receipt |
| --- | --- | --- |
| capacity breakthrough | `True` | `5` cases, exact mismatches `0`, core mismatches `0`, greedy lifts `5`, max candidates `9` |
| adversarial corpus | `True` | `20` cases, `5` patterns, assignment-safe cases `0`, greedy lifts `15`, max candidates `14` |
| shared AB/CoW envelope | `True` | Tau ok `True`, CoW matching ok `True`, Tau cases `ab_item_1_pass, cow_item_2_pass, coupled_capacity_reject, two_modes_reject` |

## Certificate Flags

| flag | value |
| --- | ---: |
| `adversarial_corpus_ok` | `1` |
| `core_selector_dp_parity_ok` | `1` |
| `deterministic_replay_ok` | `1` |
| `dp_bruteforce_parity_ok` | `1` |
| `exact_assignment_boundary_ok` | `1` |
| `fallback_boundary_ok` | `1` |
| `greedy_lift_nonvacuous` | `1` |
| `grouped_capacity_scope_ok` | `1` |
| `no_settlement_authority` | `1` |
| `resource_budget_ok` | `1` |
| `settlement_materialization_boundary_ok` | `1` |

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `cow_capacity_certificate_pass` | `True` | All host-computed proof-surface facts admit the grouped-capacity CoW certificate. |
| `scope_reject` | `True` | Missing grouped-capacity scope fails closed. |
| `bruteforce_parity_reject` | `True` | Missing DP versus brute-force parity fails closed. |
| `core_selector_reject` | `True` | Missing core-selector parity fails closed. |
| `adversarial_reject` | `True` | Missing adversarial corpus evidence fails closed. |
| `lift_reject` | `True` | Missing nonvacuous lift evidence fails closed. |
| `determinism_reject` | `True` | Missing deterministic replay fails closed. |
| `fallback_boundary_reject` | `True` | Missing fallback boundary rejects the certificate. |
| `authority_reject` | `True` | Any settlement-authority effect rejects the certificate. |
| `assignment_boundary_reject` | `True` | Missing separation from the uncoupled assignment surface fails closed. |
| `inactive_safe` | `True` | Inactive certificates do not admit while no-authority remains true. |

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `scope_reject` | `False` | Missing grouped-capacity scope fails closed. |
| `bruteforce_parity_reject` | `False` | Missing DP versus brute-force parity fails closed. |
| `core_selector_reject` | `False` | Missing core-selector parity fails closed. |
| `adversarial_reject` | `False` | Missing adversarial corpus evidence fails closed. |
| `lift_reject` | `False` | Missing nonvacuous lift evidence fails closed. |
| `determinism_reject` | `False` | Missing deterministic replay fails closed. |
| `fallback_boundary_reject` | `False` | Missing fallback boundary rejects the certificate. |
| `authority_reject` | `False` | Any settlement-authority effect rejects the certificate. |
| `assignment_boundary_reject` | `False` | Missing separation from the uncoupled assignment surface fails closed. |

## Pattern Coverage

| pattern | cases | exact mismatches | core mismatches | greedy lifts |
| --- | ---: | ---: | ---: | ---: |
| `deterministic_fuzz` | `4` | `0` | `0` | `4` |
| `dual_coupled` | `4` | `0` | `0` | `4` |
| `shared_left` | `4` | `0` | `0` | `3` |
| `shared_right` | `4` | `0` | `0` | `0` |
| `sparse_cliff` | `4` | `0` | `0` | `4` |

## Non-Claims

- This is a research certificate, not production activation.
- The exact DP claim is bounded to small grouped-capacity CoW batches.
- This does not claim a polynomial algorithm for arbitrary grouped-capacity matching.
- Uncoupled large batches remain on the Hungarian assignment surface; large coupled batches retain fallback bounds.
- Settlement authority remains with deterministic fail-closed materialization and balance checks.

## Replay

```bash
python3 tools/check_cow_capacity_dp_certificate.py
```
