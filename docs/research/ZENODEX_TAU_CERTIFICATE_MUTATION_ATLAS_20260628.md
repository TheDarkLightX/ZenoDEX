# ZenoDEX Tau Certificate Mutation Atlas - 2026-06-28

## Executive Result

A reusable mutation-replay atlas for promoted Tau frontier certificates. Every required host-projected fact is flipped at least once and must make the primary certificate output reject.

Tau validates certificate facts only; host/kernel verifiers remain authoritative for arithmetic, matching, routing, oracle updates, settlement, and state transitions.

## Mutation Coverage

- Surfaces: `7`
- Cases: `89`
- Mutations: `82`
- Required input flips: `78`
- Invalid accepts: `0`
- False rejects: `0`

## Surfaces

| surface | spec | primary | mutations | invalid accepts |
| --- | --- | --- | ---: | ---: |
| `frontier_menu_route_mode` | `frontier_certificate_menu_v1` | `o4` | `12` | `0` |
| `ab_cow_exact_solver_ab_mode` | `ab_cow_exact_solver_envelope_v1` | `o6` | `11` | `0` |
| `ab_cow_exact_solver_cow_mode` | `ab_cow_exact_solver_envelope_v1` | `o6` | `11` | `0` |
| `route_split_window_certificate` | `route_split_window_certificate_v1` | `o4` | `11` | `0` |
| `oracle_polytope_certificate` | `oracle_polytope_frontier_envelope_v1` | `o5` | `11` | `0` |
| `solver_portfolio_upgrade_certificate` | `solver_portfolio_upgrade_certificate_v1` | `o6` | `15` | `0` |
| `tauspec_ebrm_frontier_selector` | `tauspec_ebrm_frontier_selection_certificate_v1` | `o5` | `11` | `0` |

## Design Pattern

`required_fact_mutation_atlas`: Turns promoted Tau specs into executable fail-closed checklists. Missing evidence, hidden authority, mode collisions, and budget/profile gaps become replayed rejects.

## Non-Claims

- The atlas does not prove the host-computed facts are true; it verifies Tau rejects when those facts are absent.
- The atlas does not authorize settlement, oracle updates, governance, or state roots.
- The atlas covers the declared promoted frontier certificate surfaces, not every Tau file in the repository.

## Replay

```bash
python3 tools/zenodex_tau_certificate_mutation_atlas_20260628.py
```
