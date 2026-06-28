# ZenoDEX Evidence-DAG Hitting-Set Breakthrough - 2026-06-28

## Executive Result

A bounded public-assurance blocker graph is reduced to an exact minimum evidence-task bundle, then certified by Tau using host-projected graph, minimality, refutation, and authority-boundary facts.

Research certificate only. Tau has no settlement, liquidation, oracle-update, production-promotion, or state-root authority.

- Spec: `src/tau_specs/recommended/evidence_dag_hitting_set_certificate_v1.tau`
- Tau version: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Public claims in bounded model: `3`
- Blockers in bounded model: `8`
- Evidence tasks in bounded model: `13`
- Exact subset evaluations: `4096`
- Naive single-purpose tasks: `8`
- Exact selected tasks: `3`
- Compression: `8:3`
- Tau invalid accepts: `0`

## Breakthrough Shape

The public-assurance backlog is represented as:

```text
public claims -> blockers -> eligible evidence tasks -> task dependencies
```

The host computes the exact minimum evidence-task bundle over the bounded corpus. Tau certifies the projected facts: bounded graph, acyclic dependencies, every-claim path coverage, blocker coverage, objective minimality, deterministic tie-breaking, quality floor, redundancy pruning, negative-case rejection, resource bounds, and advisory-only authority.

## Exact Bundle

| selected task | covers | dependencies |
| --- | --- | --- |
| `public_claim_gate_bundle` | `claims_registry_ok, public_claim_scope_ok, no_authority_boundary_ok` | `claims_registry_source` |
| `research_kernel_packet` | `rk_evidence_ok, replay_report_ok, contradiction_cases_ok` | `tau_replay_bundle` |
| `tau_replay_bundle` | `tau_syntax_current, focused_pytest_ok, replay_report_ok, contradiction_cases_ok` | `tau_spec_source` |

The exact bundle closes eight blockers with three evidence tasks. The deterministic tie-break chooses `research_kernel_packet` over an equivalent alternative with the same cost and cover.

## Tau Certificate Cases

| case | ok | primary output |
| --- | --- | ---: |
| `certificate_pass` | `True` | `1` |
| `cycle_guard_reject` | `True` | `0` |
| `missing_path_guard_reject` | `True` | `0` |
| `blocker_cover_reject` | `True` | `0` |
| `minimality_reject` | `True` | `0` |
| `tie_break_reject` | `True` | `0` |
| `quality_floor_reject` | `True` | `0` |
| `redundancy_prune_reject` | `True` | `0` |
| `cycle_refutation_missing_reject` | `True` | `0` |
| `missing_path_refutation_missing_reject` | `True` | `0` |
| `nonminimal_refutation_missing_reject` | `True` | `0` |
| `resource_budget_reject` | `True` | `0` |
| `advisory_boundary_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## New Tau Specification Frontier For ZenoDEX

| spec | status | benefit |
| --- | --- | --- |
| `evidence_dag_hitting_set_certificate_v1.tau` | `implemented_in_this_report` | Turns assurance backlog selection into an exact bounded optimization problem with cycle, coverage, minimality, and authority-boundary gates. |
| `ab_ordering_subset_dp_certificate_v1.tau` | `frontier_candidate` | Host can compute Held-Karp style subset DP for AB ordering and Tau can certify candidate completeness, exact bounded optimality flags, and negative oracle coverage. |
| `cow_hungarian_matching_certificate_v1.tau` | `frontier_candidate` | Host can solve CoW pairing as maximum-weight bipartite matching and Tau can certify feasibility, optimality witness checks, and settlement authority separation. |

## Tau Language Constraint Learned

Tau 0.7.0-alpha host-projected sbf formulas: host computes graph search and comparisons; Tau composes booleans. This keeps the spec small, replayable, and compatible with the current local Tau binary while preserving the verifier boundary.

## Negative Knowledge

- A cyclic dependency graph is rejected before certificate admission.
- A public claim with an uncovered blocker is rejected.
- A non-minimal evidence bundle is rejected.
- A minimum-cost tie that violates deterministic ordering is rejected.
- A Tau certificate with authority effects disabled is accepted only as inactive-safe, not as a positive certificate.

## Non-Claims

- This does not parse arbitrary prose into a complete evidence graph.
- This does not change production-promotion posture or claims-registry semantics.
- The exact minimum is over the declared bounded blocker corpus and eligible task list.
- Tau does not compute graph search, hitting sets, signatures, test execution, or Research Kernel promotion.
- External legal, hardware, operator, and live-network assumptions remain explicit non-claims.

## Replay

```bash
python3 tools/zenodex_evidence_dag_hitting_set_breakthrough_20260628.py
```
