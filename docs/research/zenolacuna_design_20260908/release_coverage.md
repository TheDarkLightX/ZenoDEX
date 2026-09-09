# ZenoLacuna signed-release acceptance ledger

Date: 2026-09-09. Release qualification is recorded separately in
`release_evidence.md`. This ledger maps the original 32 scenarios to executable
checks of the supported finite project workflow. The original design files are
preserved. S22, S29 and S32 use the explicit amendments in
[release_contract.md](release_contract.md).

`TESTED` is an executable evidence grade for the named obligation under those
premises. It does not establish complete human intent, all possible programs,
an unbounded graph, physical storage reliability, or deployment authority.
The earlier prototype inventory in [implementation_coverage.md](implementation_coverage.md)
is historical and is not the signed-release status.

All files below are under `tests/`; test names are exact. The final qualification
also uses `tools/zenolacuna_qualify.py`, which drives the public CLI, and compares
its saved completion with a new process replaying the exported bundle.

| Key | File |
| --- | --- |
| SEM | `test_zenolacuna_semantics.py` |
| PROJECT | `test_zenolacuna_project.py` |
| EVIDENCE | `test_zenolacuna_project_evidence.py` |
| CLOSE | `test_zenolacuna_project_closure.py` |
| HISTORY | `test_zenolacuna_release_acceptance.py` |
| RECOVERY | `test_zenolacuna_project_recovery.py` |
| MIGRATION | `test_zenolacuna_project_migration.py` |
| SOLVER | `test_zenolacuna_project_solvers.py` |
| EXECUTION | `test_zenolacuna_project_execution.py` |
| QUALIFY | `test_zenolacuna_qualification.py` |

| Scenario | Named acceptance evidence | Scope of closure |
| --- | --- | --- |
| S01 | EVIDENCE::`test_given_valid_witness_when_admitted_then_all_premises_and_observations_bound` | Independent canonical construction checks premise and receipt hashes, complete observations, revision and source fields. |
| S02 | EVIDENCE::`test_given_valid_witness_when_admitted_then_all_premises_and_observations_bound`; SEM::`test_s02_false_witness_premise_rejects_without_mutating_scope` | False witnesses reject and the signed archive is unchanged. |
| S03 | SEM::`test_s03_complete_observation_quotient_retains_reject_and_terminal_effect` | Complete tagged observation equivalence retains declared rejection and terminal effects. |
| S04 | HISTORY::`test_given_set_valued_whole_traces_when_replay_order_varies_then_no_positionwise_union` | Every replay permutation preserves both permitted traces and rejects the outside trace without changing the family. |
| S05 | PROJECT::`test_given_owner_when_answering_then_all_compatible_interpretations_survive` | Signed filtering retains exactly the compatible family, including equivalent representatives. |
| S06 | CLOSE::`test_given_empty_family_when_owner_requests_complete_then_inconclusive_no_effect` | Signed completion rejects EMPTY_H_CONFLICT; state remains INCONCLUSIVE. |
| S07 | CLOSE::`test_given_pending_decision_when_complete_or_outside_answer_arrives_then_no_effect` | Out-of-language answers require model revision and preserve accepted history. |
| S08 | SEM::`test_s08_all_protected_positive_behaviors_survive_not_just_one`; SEM::`test_closure_cannot_silently_drop_required_outcome_from_approved_family` | Every required behavior survives; preserving a different positive cannot excuse its loss. |
| S09 | CLOSE::`test_given_reject_only_scope_when_complete_requested_then_positive_witness_required` | MISSING_POSITIVE_WITNESS prevents reject-only completion and commits no evidence. |
| S10 | QUALIFY::`test_public_cli_qualification_completes_and_replays_without_secret_artifacts`; CLOSE::`test_given_pending_decision_when_complete_or_outside_answer_arrives_then_no_effect` | The real finite migration exposes a missing decision, rejects premature work, and completes after a signed owner decision and requirement revision. |
| S11 | EVIDENCE::`test_given_invalid_candidate_source_when_verified_then_no_code_runs_or_claim_commits` | Actual source mismatch names the candidate as CODE_BUG and leaves its contract/history intact. |
| S12 | MIGRATION::`test_given_incomplete_or_relabeled_runtime_contract_when_inspected_or_completed_then_unknown_no_effect` | Omitted auth/freshness, missing input, changed context and relabeled rejection cannot acquire runtime completion. |
| S13 | EVIDENCE::`test_given_complete_pipeline_when_source_is_revised_then_archive_replays_old_bytes`; RECOVERY::`test_given_source_changes_at_last_commit_boundary_then_transaction_rolls_back` | Current source drift blocks use; an authorized successor invalidates current evidence while exact old bytes remain historical. |
| S14 | PROJECT::`test_given_agent_without_delegation_when_answering_then_no_accepted_change`; EVIDENCE::`test_given_exact_scope_delegation_when_agent_answers_then_owner_can_revoke` | Owner pins and exact scoped grants control decisions; revocation is owner-only. |
| S15 | PROJECT::`test_given_old_answer_when_owner_revises_then_old_approval_is_stale`; HISTORY::`test_given_bound_k_evidence_when_extended_to_k_plus_one_then_old_receipt_cannot_promote` | Revisions bind new semantics and obsolete old decisions/completion requests. |
| S16 | PROJECT::`test_given_owner_when_answering_then_all_compatible_interpretations_survive`; RECOVERY::`test_given_two_workers_when_same_command_races_then_exactly_one_event` | Exact retries and racing duplicates have one accepted history event. |
| S17 | HISTORY::`test_given_first_answer_when_conflicting_answer_reuses_binding_then_first_is_authoritative` | A conflicting answer cannot replace the first binding. |
| S18 | SOLVER::`test_given_failed_or_disagreeing_native_tau_when_signed_completion_applied_then_no_effect`; SOLVER::`test_given_external_deadline_when_complete_runs_then_timeout_cannot_be_logical_false`; SOLVER::`test_given_incomplete_native_esso_result_when_classified_then_no_proof`; EVIDENCE::`test_given_missing_solver_when_complete_request_forged_into_history_then_no_success` | Required native failure, unknown, disagreement, missing query and fabricated success cannot become completion. |
| S19 | SEM::`test_s19_questions_without_any_separator_never_complete` | An unseparable language keeps the family unresolved. |
| S20 | SEM::`test_s20_partial_question_search_cannot_claim_exact_optimality`; SEM::`test_closure_without_replay_budget_is_inconclusive` | Exhausted budgets cannot advertise exact search or closure. |
| S21 | HISTORY::`test_given_bound_k_evidence_when_extended_to_k_plus_one_then_old_receipt_cannot_promote` | Old COMPLETE and bundle claims cannot be used for the successor bound; historical replay still displays the original bound. |
| S22 | RECOVERY::`test_given_interrupted_transaction_when_reopened_then_previous_revision_exact`; RECOVERY::`test_given_new_source_revision_when_aborted_then_source_blob_and_event_roll_back`; RECOVERY::`test_given_complete_evidence_when_process_dies_then_atomic_receipt_and_idempotent_retry`; RECOVERY::`test_given_torn_database_when_read_then_never_fall_back_to_old_success` | SQLite transaction/crash and corruption evidence, with the documented locking/fsync premise. |
| S23 | RECOVERY::`test_given_assessed_repair_when_cancelled_then_late_complete_cannot_revive_it`; EVIDENCE::`test_given_cancelled_project_and_changed_source_when_owner_revises_then_recovery_succeeds` | Late completion cannot revive cancellation; authorized recovery remains possible after source edits. |
| S24 | HISTORY::`test_given_valid_duplicate_and_already_stale_jobs_when_reordered_then_same_state_and_codes` | All six delivery orders preserve exact archive and stale rejection behavior. |
| S25 | EVIDENCE::`test_given_invalid_candidate_source_when_verified_then_no_code_runs_or_claim_commits` | Candidate source remains data in a restricted interpreter; unsupported top-level side effects never execute. |
| S26 | SEM::`test_s26_noncongruent_question_cannot_split_equivalent_source_representatives`; SEM::`test_s26_questions_are_total_on_all_interpretations` | Question partitions are total and respect complete observational equivalence. |
| S27 | SEM::`test_s27_unseparable_child_propagates_infinity_to_root`; SEM::`test_minimax_matches_independent_complete_tree_enumeration` | An impossible child is not mistaken for zero cost; the independent tree oracle checks finite minimax. |
| S28 | HISTORY::`test_given_narrowed_applicability_with_surviving_positive_when_retirement_unacknowledged_then_reject` | Narrowing A with two protected positives requires explicit retirement acknowledgment; retained K survives and old candidate/completion is invalidated. |
| S29 | HISTORY::`test_given_set_valued_whole_traces_when_replay_order_varies_then_no_positionwise_union`; SEM::`test_graph_closure_without_complete_graph_adapter_is_unknown` | Whole bounded trace membership excludes cross-products; generic unsupported graph closure remains UNKNOWN. |
| S30 | EVIDENCE::`test_given_unenumerated_domain_when_runtime_completion_requested_then_no_promotion`; MIGRATION::`test_given_incomplete_or_relabeled_runtime_contract_when_inspected_or_completed_then_unknown_no_effect` | A missing concrete input prevents completion. |
| S31 | SEM::`test_s31_question_order_does_not_change_exact_minimax_tie_break`; SEM::`test_minimax_matches_independent_complete_tree_enumeration` | Question input order cannot change the declared deterministic optimal tie-break. |
| S32 | CLOSE::`test_given_real_owner_project_when_simulated_receipt_substituted_then_no_effect`; PROJECT::`test_given_owner_when_downgrading_real_profile_then_no_change` | Unsupported legacy wire and explicit authorization-profile downgrade both fail closed under the amended codes. |

Additional release regressions cover forged persisted completion, stale Python
bytecode, package initialization before sealing, outside module origins, root
sibling and stdlib shadowing, unpinned ESSO-root Z3 shadowing, and the exact
256-source archive budget. These are distinct negative controls, not additional
claims that the 32-scenario inventory is universally complete.

The real graph also has an independent transition oracle in
`test_zenolacuna_signal_migration.py`, including a mutated supplied ESSO-IR model.
Native Tau derives a consumer precondition and checks all 18 capability states.
The native ESSO profile checks initialization and all eight transition invariant
queries using both Z3 and CVC5, after independent finite IR/runtime parity.
