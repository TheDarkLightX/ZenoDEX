# ZenoDEX Evidence DAG Hitting-Set Contradiction Search - 2026-06-28

## Executive Result

A bounded public-assurance evidence DAG can be checked as an exact hitting-set certificate: the host enumerates minimal blocker-closing evidence bundles, rejects cycle, missing-coverage, non-minimal, tie-break, and authority-boundary contradictions, and projects only those facts into Tau.

- Scenarios: `6`
- Negative cases: `5`
- False accepts: `0`
- Max exact subsets enumerated: `64`
- Tau replay ok: `True`

## Scenario Table

| scenario | expected | host accept | reject reasons | exact subsets | selected exact bundle | presented bundle |
| --- | --- | --- | --- | ---: | --- | --- |
| `valid_minimal_bundle` | `True` | `True` | `` | `64` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` |
| `dependency_cycle_reject` | `False` | `False` | `graph_cycle,objective_not_minimal` | `0` | `None` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` |
| `missing_blocker_candidate_reject` | `False` | `False` | `missing_blocker_coverage,objective_not_minimal` | `16` | `None` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan']` |
| `non_minimal_bundle_reject` | `False` | `False` | `objective_not_minimal` | `64` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` | `['broad_release_audit', 'claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` |
| `tie_break_violation_reject` | `False` | `False` | `deterministic_tie_violation` | `16` | `['a_manifest_combo', 'claim_scope_scan', 'quote_receipt_replay']` | `['claim_scope_scan', 'quote_receipt_replay', 'z_manifest_combo']` |
| `authority_boundary_reject` | `False` | `False` | `authority_boundary_disabled` | `64` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` | `['claim_scope_scan', 'quote_receipt_replay', 'source_manifest_scan', 'zk_receipt_manifest']` |

## Tau Boundary

`src/tau_specs/recommended/evidence_dag_hitting_set_certificate_v1.tau` admits only host-projected facts: graph acyclicity, claim-path coverage, blocker coverage, dependency closure, objective minimality, deterministic tie-breaking, negative-case rejection, resource budget, nonvacuity, deterministic replay, and no authority effects.

## Mutation Checks

| mutation | accepted | rationale |
| --- | --- | --- |
| `drop_acyclicity` | `False` | acyclicity is load-bearing |
| `drop_claim_path_coverage` | `False` | claim path coverage is load-bearing |
| `drop_blocker_coverage` | `False` | blocker coverage is load-bearing |
| `drop_dependency_closure` | `False` | dependency closure is load-bearing |
| `drop_minimality` | `False` | minimality is load-bearing |
| `drop_tie_break` | `False` | deterministic tie-breaking is load-bearing |
| `drop_authority_boundary` | `False` | no-authority boundary is load-bearing |

## Non-Claims

- This is an advisory public-assurance planning certificate, not production-promotion authority.
- Tau does not enumerate evidence bundles, parse repository claims, or decide which work should be merged.
- The bounded corpus is synthetic; it stress-tests the claim shape rather than proving every future assurance graph.

## Replay

```bash
python3 tools/check_evidence_dag_hitting_set_contradictions.py
```
