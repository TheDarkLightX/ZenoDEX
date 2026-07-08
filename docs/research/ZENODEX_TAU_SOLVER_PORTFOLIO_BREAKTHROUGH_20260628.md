# ZenoDEX Tau Solver Portfolio Breakthrough - 2026-06-28

## Executive Result

Tau gates a combined AB/CoW solver-upgrade decision with host-computed parity, capacity-scope, performance, fallback, rollback, negative replay, and no-authority facts.

- Tau ok: `True`
- Tau cases: `8`
- Invalid accepts: `0`
- AB n=12 proxy ratio: `812.109375`
- CoW n=20 proxy ratio: `304112751022080.0`

## Portfolio Facts

| fact | value |
| --- | ---: |
| `ab_bruteforce_oracle_parity_ok` | `1` |
| `ab_full_state_scope_ok` | `1` |
| `ab_solver_candidate_present` | `1` |
| `advisory_model_only` | `1` |
| `certificate_active` | `1` |
| `cow_bruteforce_oracle_parity_ok` | `1` |
| `cow_solver_candidate_present` | `1` |
| `cow_uncoupled_or_bounded_capacity_scope_ok` | `1` |
| `deterministic_tie_ok` | `1` |
| `fallback_paths_ok` | `1` |
| `negative_replay_ok` | `1` |
| `no_authority_effect` | `1` |
| `performance_floor_ok` | `1` |
| `resource_budget_ok` | `1` |
| `rollback_available` | `1` |

## Tau Cases

| case | ok | rationale |
| --- | --- | --- |
| `portfolio_pass` | `True` | AB and CoW solver evidence, performance floor, fallback, rollback, and no-authority facts all hold. |
| `ab_parity_reject` | `True` | AB subset-DP promotion fails when brute-force parity is missing. |
| `cow_scope_reject` | `True` | CoW promotion fails when uncoupled or bounded-capacity scope is not proven. |
| `negative_replay_reject` | `True` | A portfolio without negative replay cannot be promoted. |
| `performance_reject` | `True` | A portfolio that does not clear the host-computed performance floor is rejected. |
| `rollback_reject` | `True` | Solver rollout requires an explicit fallback or rollback path. |
| `authority_reject` | `True` | The certificate cannot carry settlement, oracle, governance, or state-root authority. |
| `inactive_safe` | `True` | Inactive portfolio certificates do not admit while the no-authority rail remains true. |

## Work Items

| work item | status | evidence | non-claim |
| --- | --- | --- | --- |
| `1_ab_ordering` | `covered` | bounded full-state subset DP with brute-force parity and explicit fallback after 12 | The certificate does not claim a compressed Held-Karp state is sound for integer CPMM ordering. |
| `2_cow_matching` | `covered` | uncoupled Hungarian assignment plus bounded coupled-capacity DP evidence | The certificate does not claim arbitrary grouped-capacity CoW matching is polynomial. |

## Non-Claims

- The certificate is a research and rollout evidence gate, not a settlement verifier.
- All numeric complexity, matching, CPMM, and DP computations stay host-side.
- The performance floor is host-computed evidence over bounded reports, not a Tau timing measurement.
- Rollback availability is an external rollout fact supplied to Tau and must be backed by deployment evidence before production use.

## Replay

```bash
python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py
```
