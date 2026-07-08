# ZenoDEX AB Bounded-Oracle Pruning Certificate - 2026-06-28

## Executive Result

A bounded suffix-oracle certificate upgrades AB exact-in dominance pruning from a pure heuristic into a locally certified research lane: every removed state is checked against all remaining suffix permutations within the suffix cap.

Tau admits a research certificate only. It does not compute swaps, run DP, prune states, select AB orders, or authorize settlement.

## Scope

- Suffix cap: `4` remaining intents
- Case count: `14`
- Certified prunes: `2437`
- Suffix permutations checked: `13467`
- Aggregate state-insertion reduction: `20.90x`
- Aggregate transition reduction: `9.27x`

The oracle only prunes when every remaining suffix permutation inside the cap preserves the AB objective key.

## Tau Specification

- Spec: `src/tau_specs/recommended/ab_bounded_oracle_pruning_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau trace replay ok: `True`
- Certificate ok: `True`

## Certificate Flags

| flag | value |
| --- | ---: |
| `all_prunes_suffix_certified` | `1` |
| `brute_force_parity_ok` | `1` |
| `deterministic_replay_ok` | `1` |
| `no_authority_effect` | `1` |
| `nonvacuous_pruning` | `1` |
| `resource_budget_ok` | `1` |
| `same_direction_exact_in_scope_ok` | `1` |
| `state_reduction_ok` | `1` |
| `suffix_bound_ok` | `1` |
| `unpruned_parity_ok` | `1` |

## Case Summary

| n | variant | ok | state reduction | certified prunes | suffix checks |
| ---: | ---: | --- | ---: | ---: | ---: |
| `4` | `0` | `True` | `2.24x` | `18` | `21` |
| `4` | `1` | `True` | `2.32x` | `17` | `20` |
| `4` | `2` | `True` | `3.25x` | `17` | `22` |
| `4` | `3` | `True` | `2.71x` | `15` | `20` |
| `5` | `0` | `True` | `5.93x` | `61` | `117` |
| `5` | `1` | `True` | `5.82x` | `61` | `116` |
| `5` | `2` | `True` | `5.53x` | `61` | `117` |
| `5` | `3` | `True` | `4.66x` | `58` | `114` |
| `6` | `0` | `True` | `14.08x` | `197` | `716` |
| `6` | `1` | `True` | `13.98x` | `189` | `716` |
| `6` | `2` | `True` | `12.79x` | `196` | `714` |
| `6` | `3` | `True` | `14.83x` | `177` | `714` |
| `7` | `0` | `True` | `34.60x` | `661` | `5031` |
| `7` | `1` | `True` | `29.85x` | `709` | `5029` |

## Tau Mode Checks

| case | ok | rationale |
| --- | --- | --- |
| `bounded_oracle_pass` | `True` | All host-computed bounded-oracle evidence facts admit the certificate. |
| `missing_suffix_bound_reject` | `True` | Missing suffix-bound evidence fails closed. |
| `missing_certification_reject` | `True` | A prune without suffix-oracle certification fails closed. |
| `missing_parity_reject` | `True` | Missing unpruned DP parity fails closed. |
| `missing_bruteforce_reject` | `True` | Missing brute-force parity fails closed. |
| `missing_determinism_reject` | `True` | Missing deterministic replay fails closed. |
| `authority_reject` | `True` | Authority-bearing certificates are rejected. |
| `inactive_safe` | `True` | Inactive certificates do not admit while the no-authority rail remains true. |

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `missing_suffix_bound_reject` | `False` | Missing suffix-bound evidence fails closed. |
| `missing_certification_reject` | `False` | A prune without suffix-oracle certification fails closed. |
| `missing_parity_reject` | `False` | Missing unpruned DP parity fails closed. |
| `missing_bruteforce_reject` | `False` | Missing brute-force parity fails closed. |
| `missing_determinism_reject` | `False` | Missing deterministic replay fails closed. |
| `authority_reject` | `False` | Authority-bearing certificates are rejected. |

## Non-Claims

- This artifact is a research certificate, not a production ordering change.
- The suffix oracle is bounded; it does not prove a universal dominance theorem.
- The certificate is scoped to same-pool, same-direction, exact-in AB states.
- Tau does not compute the DP, suffix oracle, swaps, balances, hashes, or settlement effects.
- No settlement authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_bounded_oracle_pruning_certificate.py
```
