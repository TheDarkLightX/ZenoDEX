# ZenoDEX Research Kernel n7 Tau Scope Closure - 2026-06-29

## Executive Result

The n7 Tau scope certificate resolves the RK risk for the bounded AB child-frontier bidirectional-transition scope surface: all required host facts are present, every missing-fact Tau case rejects, digest pins and deterministic replay match, and the no-authority rail remains explicit.

- Target RK atom: `atom_f16f64e92cd14d74`
- Closure kind: `resolves`
- Edge type: `SUPERSEDES`
- Source report: `generated/zenodex_ab_child_frontier_bidirectional_transition_tau_certificate_20260629/report.json`

## Checks

| check | value |
| --- | ---: |
| `source_schema_ok` | `True` |
| `spec_id_ok` | `True` |
| `tau_ok` | `True` |
| `invalid_accepts_zero` | `True` |
| `tau_case_count_ok` | `True` |
| `source_report_hash_ok` | `True` |
| `source_tool_hash_ok` | `True` |
| `source_test_hash_ok` | `True` |
| `source_doc_hash_ok` | `True` |
| `source_spec_hash_ok` | `True` |
| `source_report_ok_present` | `True` |
| `n7_zero_min_scope_ok_present` | `True` |
| `transition_counts_complete_present` | `True` |
| `generated_child_count_ok_present` | `True` |
| `linked_child_coverage_ok_present` | `True` |
| `transition_digest_pinned_present` | `True` |
| `linked_digest_pinned_present` | `True` |
| `deterministic_replay_ok_present` | `True` |
| `negative_controls_reject_present` | `True` |
| `authority_boundary_ok_present` | `True` |
| `no_authority_effect_present` | `True` |
| `corpus_nonvacuous_present` | `True` |
| `fact_set_exact` | `True` |
| `bidirectional_transition_certificate_pass_case_present` | `True` |
| `bidirectional_transition_certificate_pass_case_ok` | `True` |
| `missing_source_report_reject_case_present` | `True` |
| `missing_source_report_reject_case_ok` | `True` |
| `wrong_scope_reject_case_present` | `True` |
| `wrong_scope_reject_case_ok` | `True` |
| `transition_counts_reject_case_present` | `True` |
| `transition_counts_reject_case_ok` | `True` |
| `generated_child_count_reject_case_present` | `True` |
| `generated_child_count_reject_case_ok` | `True` |
| `linked_child_coverage_reject_case_present` | `True` |
| `linked_child_coverage_reject_case_ok` | `True` |
| `transition_digest_reject_case_present` | `True` |
| `transition_digest_reject_case_ok` | `True` |
| `linked_digest_reject_case_present` | `True` |
| `linked_digest_reject_case_ok` | `True` |
| `nondeterministic_replay_reject_case_present` | `True` |
| `nondeterministic_replay_reject_case_ok` | `True` |
| `negative_controls_missing_reject_case_present` | `True` |
| `negative_controls_missing_reject_case_ok` | `True` |
| `authority_boundary_reject_case_present` | `True` |
| `authority_boundary_reject_case_ok` | `True` |
| `authority_effect_reject_case_present` | `True` |
| `authority_effect_reject_case_ok` | `True` |
| `empty_corpus_reject_case_present` | `True` |
| `empty_corpus_reject_case_ok` | `True` |
| `inactive_safe_case_present` | `True` |
| `inactive_safe_case_ok` | `True` |
| `positive_case_admits` | `True` |
| `missing_source_report_reject_rejects` | `True` |
| `wrong_scope_reject_rejects` | `True` |
| `transition_counts_reject_rejects` | `True` |
| `generated_child_count_reject_rejects` | `True` |
| `linked_child_coverage_reject_rejects` | `True` |
| `transition_digest_reject_rejects` | `True` |
| `linked_digest_reject_rejects` | `True` |
| `nondeterministic_replay_reject_rejects` | `True` |
| `negative_controls_missing_reject_rejects` | `True` |
| `authority_boundary_reject_rejects` | `True` |
| `authority_effect_reject_rejects` | `True` |
| `empty_corpus_reject_rejects` | `True` |
| `inactive_safe_rejects` | `True` |
| `inactive_safe_no_authority` | `True` |
| `case_count_ok` | `True` |
| `child_mask_count_ok` | `True` |
| `transition_row_count_ok` | `True` |
| `expected_transition_count_ok` | `True` |
| `covered_transition_count_ok` | `True` |
| `unique_transition_count_ok` | `True` |
| `generated_child_count_ok` | `True` |
| `linked_child_coverage_witness_count_ok` | `True` |
| `negative_control_count_ok` | `True` |
| `negative_control_accepts_zero` | `True` |
| `transition_digest_ok` | `True` |
| `linked_digest_ok` | `True` |
| `replay_hash_ok` | `True` |
| `n7_scope_nonclaim_ok` | `True` |
| `python_refinement_nonclaim_ok` | `True` |
| `lean_generation_nonclaim_ok` | `True` |
| `host_verifier_nonclaim_ok` | `True` |
| `nonzero_min_nonclaim_ok` | `True` |
| `authority_nonclaim_ok` | `True` |
| `forbidden_tau_replaces_the_host_verifier` | `True` |
| `forbidden_proves_python-to-lean_refinement` | `True` |
| `forbidden_proves_lean_refinement` | `True` |
| `forbidden_covers_nonzero_min_amount_out` | `True` |
| `forbidden_authorizes_settlement` | `True` |
| `forbidden_grants_production_authority` | `True` |
| `forbidden_authorizes_production` | `True` |

## Research Kernel Edge To Add

| source atom | target atom | edge type |
| --- | --- | --- |
| `atom_zenodex_research_kernel_n7_tau_scope_closure_20260629` | `atom_f16f64e92cd14d74` | `SUPERSEDES` |

## Residual Open Frontier

- n7 bidirectional transition mutation risk
- reserve-state observed-summary bridge risk
- sampled n8 canonical-index Merkle certificate risk
- sampled n8 bidirectional transition certificate risk
- full subset-mask DP construction and Python-to-Lean refinement

## Non-Claims

- This receipt closes only the RK tracking risk for the bounded n7 Tau scope certificate.
- This receipt does not replace the host Merkle verifier or transition checker.
- This receipt does not prove Python-to-Lean refinement.
- This receipt does not prove child-frontier generation in Lean.
- This receipt does not cover nonzero min_amount_out behavior.
- This receipt grants no settlement, governance, state-root, routing, matching, pool-mutation, production, or deployment authority.

## Replay

```bash
python3 tools/check_research_kernel_n7_tau_scope_closure_20260629.py
```

Live replay:

```bash
python3 tools/check_research_kernel_n7_tau_scope_closure_20260629.py --live-replay
```
