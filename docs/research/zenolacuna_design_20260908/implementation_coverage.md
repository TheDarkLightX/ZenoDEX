# ZenoLacuna implementation coverage

Historical prototype inventory. See [release_coverage.md](release_coverage.md)
and [release_evidence.md](release_evidence.md) for the completed signed release.

Assessment date: 2026-09-08. This is an implementation inventory against the
32 planned cases in [scenarios.json](scenarios.json) and
[acceptance.md](acceptance.md). Those frozen design documents retain their
`PLANNED` status; this note does not rewrite their acceptance contract.

The integrator's earlier integrated run reported **127 focused tests passed**.
After the follow-up repairs, this reviewer independently ran the shell, hostile
review, run-bound program workflow, program-port, and demo suites: **57 passed,
1 skipped** (`TAU_BIN` was unset). The 127-test result remains the integrator's
run; it is not another independently executed 127-test run. These results do
not establish complete product acceptance, production readiness, or completion
of every scenario below. A later full-suite or native-tool run needs its own
recorded result.

`TESTED` means the named finite behavior has executable evidence in its current
layer. `PARTIAL` means related behavior is tested while a material part of the
planned scenario remains uncovered. `GAP` identifies a current implementation
behavior that differs from the required outcome. `UNMOUNTED` means the requested
workflow or authority port is unavailable; neighboring negative tests may
still pass. These are coverage statuses, not proof grades.

The local shell has no settlement effect plan or external outbox. Its observable
effects are evidence files, the current pointer, and reconstructed decision
history. A file snapshot is evidence for that local profile. It does not test a
future payment, deployment, delegated-capability, or external-effect boundary.

## Test file key

Every reference below uses `KEY::exact_test_function_name`. Parameterized cases
share the named function; a function name alone does not imply independent
oracle coverage of every planned mutation.

| Key | Current test file |
| --- | --- |
| SEM | [test_zenolacuna_semantics.py](../../../tests/test_zenolacuna_semantics.py) |
| SHELL | [test_zenolacuna_shell.py](../../../tests/test_zenolacuna_shell.py) |
| REVIEW | [test_zenolacuna_shell_review.py](../../../tests/test_zenolacuna_shell_review.py) |
| FLOW | [test_zenolacuna_workflows.py](../../../tests/test_zenolacuna_workflows.py) |
| PORT | [test_zenolacuna_ports.py](../../../tests/test_zenolacuna_ports.py) |
| PROGRAM | [test_zenolacuna_program_workflow.py](../../../tests/test_zenolacuna_program_workflow.py) |
| DEMO | [test_zenolacuna_demo.py](../../../tests/test_zenolacuna_demo.py) |
| QUEUE | [test_zenolacuna_queue.py](../../../tests/test_zenolacuna_queue.py) |
| ESSO | [test_zenolacuna_esso.py](../../../tests/test_zenolacuna_esso.py) |
| CODEC | [test_zenolacuna_codec.py](../../../tests/test_zenolacuna_codec.py) |

Independent follow-up command, run from the repository root in Bash:

```bash
python3 -m pytest -q tests/test_zenolacuna_{shell,shell_review,program_workflow,ports,demo}.py
```

Result: 57 passed, 1 skipped in 5.39 seconds. The skipped test required a native
Tau binary. Source hashes were unchanged before and after this run.

## Scenario mapping

| Scenario | Status | Exact current tests | Established behavior and residual |
| --- | --- | --- | --- |
| ZL-S01 | PARTIAL | `SEM::test_s01_given_distinguishing_witness_when_checked_then_all_premises_hold`; `SEM::test_analyze_selects_a_set_difference_when_nondeterministic_rows_overlap` | Fixed finite witnesses bind the scope root and distinguish allowed observation sets. No standalone human witness-admission command or independently source-replayed acceptance receipt is tested. |
| ZL-S02 | PARTIAL | `SEM::test_s02_false_witness_premise_rejects_without_mutating_scope`; `SEM::test_witness_must_show_a_difference_in_allowed_sets_not_two_common_outcomes` | False premises produce `WITNESS_PREMISE_FAILED` and preserve the immutable scope. The planned complete shell/history/effect snapshot for witness submission is unmounted. |
| ZL-S03 | TESTED | `SEM::test_s03_complete_observation_quotient_retains_reject_and_terminal_effect`; `SEM::test_equivalent_observation_representative_cannot_change_repair_verdict` | Finite quotient equality retains rejection kind and declared terminal-effect observations. This establishes the declared observation relation, not completeness of an arbitrary runtime projection. |
| ZL-S04 | PARTIAL | `SEM::test_s04_intentional_nondeterminism_preserves_the_complete_allowed_set`; `SEM::test_nondeterministic_outcomes_do_not_witness_distinct_semantic_classes` | Both allowed outcomes remain represented; an outside outcome fails decided-requirement checking. The planned replay-order permutation experiment is not present. A singleton implementation refinement is permitted unless protected requirements require both outcomes. |
| ZL-S05 | PARTIAL | `SEM::test_s05_answer_retains_exact_subset_and_cannot_restore_eliminated_interpretations`; `SHELL::test_given_cli_lifecycle_when_scope_and_bound_answer_are_supplied_then_json_is_stable`; `REVIEW::test_given_forged_command_id_reuse_when_reopen_then_corrupt_history` | Exact subset filtering, bound simulated answers, and rejection of a forged reused command ID are exercised. Real owner approval and the complete cross-revision owner-decision workflow are unavailable. |
| ZL-S06 | TESTED | `SEM::test_s06_empty_interpretations_never_close`; `PROGRAM::test_given_empty_family_when_assessment_or_replay_runs_then_exact_empty_code_preserves_history` | Core and shell assessment/replay now preserve the exact `EMPTY_H_CONFLICT` diagnostic; rejected shell operations leave the full local file snapshot unchanged. |
| ZL-S07 | TESTED | `SEM::test_s07_outside_answer_requires_model_revision_and_is_noop`; `REVIEW::test_given_out_of_language_answer_when_submit_then_no_history_change` | Out-of-language answers raise `NEEDS_MODEL_REVISION`; the shell's complete local file snapshot remains unchanged. The subsequent model-revision workflow is separately unmounted. |
| ZL-S08 | TESTED | `SEM::test_s08_all_protected_positive_behaviors_survive_not_just_one`; `SEM::test_s08_protected_clause_violation_is_rejected_even_when_base_contract_allows_it`; `SEM::test_closure_cannot_silently_drop_required_outcome_from_approved_family` | Finite preservation checks require every declared protected positive behavior and reject lost clauses. Coverage concerns candidate preservation inside a fixed scope; owner-approved replacement of the scope is a separate unavailable workflow. |
| ZL-S09 | TESTED | `SEM::test_s09_reject_only_scope_cannot_close_without_required_positive_witness`; `SEM::test_closure_must_replay_every_context_not_just_a_positive_fixture` | Reject-only closure fails with `MISSING_POSITIVE_WITNESS`; a matching positive fixture does not excuse a failure elsewhere in the finite domain. |
| ZL-S10 | PARTIAL | `SEM::test_s10_weak_roundtrip_disagreement_is_missing_requirement_before_decision`; `PORT::test_codec_scope_has_eight_paired_xor_mutants_and_two_semantic_classes`; `PROGRAM::test_given_accepted_answer_and_assessed_candidate_when_programs_replay_then_surviving_branch_is_checked`; `PROGRAM::test_given_no_assessed_candidate_when_programs_replay_then_candidate_required_without_history_change` | Finite classification and the paired codec counterexample distinguish an undecided requirement from a violation. `Store.check_programs` now consumes the recorded simulated decision and assessed candidate in a read-only run-bound check. Real-owner approval remains unavailable, and no runtime certificate is persisted. |
| ZL-S11 | PARTIAL | `SEM::test_s11_current_contract_violation_is_code_bug_without_revising_requirement`; `PORT::test_replay_pipeline_detects_mutant_only_on_fourth_input`; `PROGRAM::test_given_runtime_program_mismatch_when_replayed_then_rejects_without_history_change` | A runtime mismatch against the recorded assessed candidate now rejects without changing the persisted run. Relation violations remain `CODE_BUG:*`; the program port uses `RUNTIME_MODEL_MISMATCH`. A unified product receipt naming the failing runtime candidate and classifying it as the planned code bug is not tested. |
| ZL-S12 | PARTIAL | `PORT::test_signal_projection_missing_auth_and_freshness_is_model_omission`; `PORT::test_signal_projection_unknown_field_is_model_omission`; `PORT::test_signal_projection_full_fixed_v1_v2_fixture_is_exhaustive`; `SEM::test_graph_closure_without_complete_graph_adapter_is_unknown` | The fixed signal fixture reports `MODEL_OMISSION` and `UNKNOWN` for missing or unexpected fields. This is not a generic runtime trace/schema adapter or mounted finite-state-graph promotion workflow. |
| ZL-S13 | TESTED | `REVIEW::test_given_source_drift_when_duplicate_or_replay_then_no_history_change`; `SHELL::test_given_source_mutates_before_pointer_then_old_revision_remains_current`; `PROGRAM::test_given_source_drifts_during_program_replay_then_completion_is_not_returned`; `PROGRAM::test_given_program_checker_drift_before_replay_then_bound_run_rejects`; `PROGRAM::test_given_program_checker_drifts_after_replay_then_completion_is_not_returned` | Source/checker drift blocks both persisted model history use and the read-only run-bound runtime report. The program port and underlying restricted interpreter are both fingerprinted. Late drift prevents returning completion while preserving the local journal; a persisted runtime certificate is not created. |
| ZL-S14 | UNMOUNTED | `SHELL::test_given_unlisted_actor_when_answer_then_unauthorized_and_no_revision`; `SHELL::test_given_profile_mismatch_or_unavailable_real_owner_then_no_decision_mutates`; `REVIEW::test_given_real_owner_forged_repair_record_when_reopen_then_corrupt_history` | Negative authorization boundaries are tested. The planned signed owner/delegated-capability lookup is unavailable. Only the exact actor `simulated-owner` is accepted in `SIMULATED`; a JSON actor never grants real-owner authority. |
| ZL-S15 | UNMOUNTED | `SHELL::test_given_cancelled_run_when_late_answer_then_stale_and_resume_requires_new_revision`; `FLOW::test_s24_all_retry_and_already_stale_delivery_orders_have_one_accepted_history` | Stale-parent rejection is tested. There is no mounted revision operation changing H, A, O, or K and carrying its owner decision and dependencies forward. Cancel/resume is a lifecycle change within the same scope. |
| ZL-S16 | TESTED | `SHELL::test_given_identical_and_conflicting_duplicates_then_one_effect_and_stable_codes`; `FLOW::test_s24_all_retry_and_already_stale_delivery_orders_have_one_accepted_history`; `REVIEW::test_given_forged_duplicate_assessment_when_reopen_then_corrupt_history`; `REVIEW::test_given_forged_replay_candidate_or_duplicate_when_reopen_then_corrupt_history` | Identical answers deduplicate; all six valid/retry/stale delivery orders retain one decision record. Forged persisted duplicate assessment/replay records also reject. Effects are local evidence history only. |
| ZL-S17 | TESTED | `SHELL::test_given_identical_and_conflicting_duplicates_then_one_effect_and_stable_codes`; `REVIEW::test_given_forged_command_id_reuse_when_reopen_then_corrupt_history` | Conflicting answers reject with `DUPLICATE_CONFLICT`, preserving the first accepted revision. Reconstructing a checksum-valid history cannot bypass command-ID uniqueness. No external outbox exists in this profile. |
| ZL-S18 | PARTIAL | `PORT::test_tau_errors_timeouts_and_malformed_results_are_unknown`; `PORT::test_tau_positive_fake_verdict_disagreement_is_unknown`; `ESSO::test_solver_fault_never_becomes_invariant_evidence`; `ESSO::test_all_named_obligations_require_two_agreeing_solvers` | Adapter classifiers fail closed on injected timeout, unknown, malformed, missing, and disagreeing results. These tests do not establish an integrated solver-backed shell commit. The native Tau test is environment-conditional; classifier fixtures alone are not native solver evidence. |
| ZL-S19 | TESTED | `SEM::test_s19_questions_without_any_separator_never_complete`; `SEM::test_minimax_matches_independent_complete_tree_enumeration` | A constant question family remains unseparable without dropping classes or claiming closure; the separate tree oracle exercises finite question families. |
| ZL-S20 | TESTED | `SEM::test_s20_partial_question_search_cannot_claim_exact_optimality`; `SEM::test_closure_without_replay_budget_is_inconclusive` | Exceeding the exact DP budget removes question/cost claims; exhausted replay cannot close. These are deterministic operation budgets, not elapsed-time guarantees. |
| ZL-S21 | PARTIAL | `SEM::test_s21_complete_finite_replay_carries_only_model_claim`; `SEM::test_s21_bounded_history_never_promotes_unbounded_evidence`; `QUEUE::test_partial_graph_search_cannot_report_complete` | Evidence labels and history bounds remain distinct, and incomplete queue search cannot claim a complete graph. Changing k changes the scope root; a generic k-to-k+1 promotion-admission workflow is not mounted or tested. |
| ZL-S22 | PARTIAL | `SHELL::test_given_fault_before_pointer_when_reopened_then_previous_revision_is_current`; `SHELL::test_given_corrupt_pointed_record_when_reopened_then_no_fallback`; `REVIEW::test_given_deeply_nested_pointed_record_when_reopen_then_typed_corrupt_record` | A fault after durable record creation preserves the old pointer; corrupt pointed records reject without fallback. Every partial-record prefix, torn write, process death, and fsync failure is not tested. Restart reports ordinary status; no explicit `RECOVERED:PREVIOUS_REVISION` result or quarantine procedure is mounted. |
| ZL-S23 | PARTIAL | `SHELL::test_given_cancelled_run_when_late_answer_then_stale_and_resume_requires_new_revision`; `QUEUE::test_given_pending_message_when_upgrade_rejected_then_drain_upgrade_retry` | Local cancellation rejects a late answer and explicit resume creates a new revision. The planned restart while cancelled plus late asynchronous repair/completion message is not exercised end to end; there is no asynchronous repair worker port. |
| ZL-S24 | TESTED | `FLOW::test_s24_all_retry_and_already_stale_delivery_orders_have_one_accepted_history` | All six permutations of a valid answer, identical retry, and already-stale answer converge after reopening to identical current revision, report, and two journal records. This is a finite delivery-order experiment, not a general concurrent scheduling proof. |
| ZL-S25 | PARTIAL | `PORT::test_restricted_program_rejects_top_level_side_effect_without_execution`; `CODEC::test_malicious_strings_remain_data` | Restricted source containing import/top-level side effects rejects without creating its marker. The current code emits `UNSUPPORTED_PROGRAM:source_shape`; there is no explicit adapter path allowlist implementing the planned `UNALLOWLISTED_SOURCE` contract. CLI path reading and AST-language restriction are different checks. |
| ZL-S26 | TESTED | `SEM::test_s26_noncongruent_question_cannot_split_equivalent_source_representatives`; `SEM::test_s26_questions_are_total_on_all_interpretations` | Question vectors must be total and congruent on semantic classes; violations have exact typed rejections. |
| ZL-S27 | TESTED | `SEM::test_s27_unseparable_child_propagates_infinity_to_root`; `SEM::test_minimax_matches_independent_complete_tree_enumeration` | An unseparable nonsingleton child makes the root unseparable; no finite optimal cost is reported. A separate exhaustive tree oracle supplies additional finite-family evidence. |
| ZL-S28 | PARTIAL | `SEM::test_s28_narrowed_assumptions_cannot_erase_protected_input`; `SEM::test_projection_cannot_collapse_different_protected_verdicts` | Protected applicability cannot be erased by a narrowed candidate assumption set or a lossy observation projection. Owner retirement/revision creating a new scope is unavailable; that positive workflow remains unmounted. |
| ZL-S29 | PARTIAL | `SEM::test_s29_complete_trace_union_excludes_cross_product_history`; `SEM::test_graph_closure_without_complete_graph_adapter_is_unknown`; `QUEUE::test_given_queued_legacy_message_when_consumer_changes_then_counterexample` | Whole trace strings retain the declared union, and the specific queue graph has its own bounded checker. The planned generic graph trace-admission port and exact `TRACE_NOT_ALLOWED` result are absent; the relation test reports `CODE_BUG:DECIDED_REQUIREMENT_VIOLATION`. |
| ZL-S30 | PARTIAL | `PORT::test_replay_pipeline_rejects_three_inputs_for_claimed_four_value_domain`; `PORT::test_replay_pipeline_detects_mutant_only_on_fourth_input`; `PORT::test_codec_source_interpreter_matches_trusted_functions_over_every_byte`; `PROGRAM::test_given_run_selector_when_cli_replays_programs_then_result_is_read_only_json` | Complete integer-domain replay and a fourth-input mutant are tested; the CLI now mounts read-only replay against an expected run revision and recorded candidate. The incomplete-domain code remains `INCOMPLETE_RUNTIME_DOMAIN`, rather than the planned `UNENUMERATED_INPUT`. This profile covers accepted integer-return observations, not arbitrary runtime outcomes or a persisted runtime certificate. |
| ZL-S31 | TESTED | `SEM::test_s31_question_order_does_not_change_exact_minimax_tie_break`; `SEM::test_minimax_matches_independent_complete_tree_enumeration` | Reversing question order preserves qA and worst-case cost 2; the independent tree oracle checks additional finite families and weighted costs. |
| ZL-S32 | PARTIAL | `SHELL::test_given_profile_mismatch_or_unavailable_real_owner_then_no_decision_mutates`; `SHELL::test_given_real_scope_in_simulated_program_check_then_profile_mismatch_is_rejected`; `REVIEW::test_given_real_owner_forged_repair_record_when_reopen_then_corrupt_history` | Initialization and program-check profile mismatch use `AUTHORIZATION_PROFILE_MISMATCH`; real-owner operations fail closed. A persisted REAL_OWNER run reopened with a substituted simulated receipt/profile and a full no-effect snapshot is not directly covered by these tests. The real-owner positive trusted port is unavailable. |

## Integration boundaries and remaining work

1. **Run-bound program replay is now mounted read-only.**
   [tools/zenolacuna.py](../../../tools/zenolacuna.py) accepts
   `check-programs --run ... --expected-revision ...`; this mode rejects a
   caller-supplied candidate. [shell.py](../../../src/zenolacuna/shell.py)
   reconstructs the recorded scope, surviving interpretations, and assessed
   candidate under the run lock. It checks the expected revision, profile,
   cancellation, and candidate readiness, then verifies program behavior and
   rechecks source/checker bindings before returning `CHECKED`. Both the
   program adapter and its restricted interpreter participate in the checker
   fingerprint. The result carries the current revision and creates no
   journal record or persisted runtime certificate. The old unmounted
   decision-to-program bridge finding is closed for this finite read-only
   workflow. `PROGRAM::test_given_stale_revision_when_programs_replay_then_stale_revision_preserves_history`,
   `PROGRAM::test_given_cancelled_run_when_programs_replay_then_cancelled_without_history_change`,
   and `PROGRAM::test_given_real_owner_run_when_programs_replay_then_unavailable_authority_rejects`
   cover the corresponding negative boundaries.

2. **Mount authority and scope evolution only with their own acceptance
   evidence.** `REAL_OWNER` deliberately has no trusted approval port. Source
   JSON, actor strings, and a caller-selected profile cannot stand in for
   owner authentication or delegated capabilities. Scope creation is present;
   owner-approved revision/retirement of H, A, O, and K is absent. These gaps
   block the corresponding positive owner workflows, while their current
   fail-closed behavior remains useful.

3. **Preserve the planned exact result contract.** The S06 shell empty-family
   code is repaired and covered by a no-history-change regression. The S22
   recovery result, S25 path-allowlist result, S29 trace-admission result, and
   S30 incomplete-domain result differ from their planned targets
   or lack a mounted operation. The design catalog must not be silently
   reinterpreted as passing because a nearby negative case is safe. Add the
   actual workflow or explicitly review a contract change, then retain exact
   rejection and no-effect regressions.

4. **Complete persistence failure and lifecycle coverage.** Current tests
   establish useful crash boundaries and corruption refusals. They do not
   exhaust partial record prefixes, torn pointers, fsync failures, concurrent
   process races, cancelled restart with a late worker result, or initial-run
   recovery after a failed genesis publication. The shell documents a
   cooperative local filesystem assumption. `flock`, `lstat`, and
   `O_NOFOLLOW` do not establish safety against a principal replacing parent
   directories. Unpointed records can remain after interrupted publication;
   semantic no-effect claims must distinguish them from accepted history.

5. **Keep runtime and solver claims tied to the executed profile.**
   [programs.py](../../../src/zenolacuna/ports/programs.py) supports complete
   one-to-eight-bit integer domains through the restricted interpreter. Its
   report names program hashes; it is not arbitrary Python execution,
   general runtime equivalence, or complete graph refinement. Source hashes
   declared by a scope are checked when present. The fixed signal projection
   fixture and queue model do not establish coverage of every runtime event
   or arbitrary migration. `PORT::test_tau_native_check_is_optional_and_source_selected_by_environment`
   requires `TAU_BIN`; injected Tau/ESSO verdict tests establish classifier
   behavior, not that a particular native solver run occurred. Native
   receipts must be assessed separately from this test inventory.

6. **The integer-outcome substitution gap is closed.** The earlier probe
   relabeled the fourth integer result as `REJECT` and obtained runtime
   evidence without an observed rejection event. The program port now requires
   every outcome to be `OutcomeKind.ACCEPT` with its exact integer name and
   observation. `PORT::test_integer_program_cannot_claim_a_runtime_rejection_from_an_outcome_label`
   kills that substitution with `RUNTIME_ENCODING_MISMATCH`.
   `PORT::test_byte_program_scope_checks_returned_sentinel_without_inventing_rejection_event`
   checks that reserved byte inputs produce the integer sentinel 255. An
   application-level rejection still requires a separate checked runtime
   projection; the integer profile makes no such claim.

7. **An unavailable Tau executable cannot publish demo completion.**
   `DEMO::test_demo_nonexecutable_tau_is_typed_rejection_without_summary`
   observes the typed `binary_not_executable` rejection, no stderr traceback,
   and no completion summary. Preparatory artifacts may already exist in the
   new output directory; they do not constitute successful native replay.

## Additional assurance outside the 32 scenario rows

The shell tests also cover exact aggregate-history-byte and admission-budget
boundaries, low declared DP work with large preprocessing, checker drift in
each extracted helper, dangling lock symlinks, and semantically forged journal
records. The codec suite checks duplicate JSON keys, malformed shapes, closed
fields, enum variants, booleans in integer slots, floats, input/depth limits,
and canonical encoding. The queue suite compares generated ESSO guards,
updates, and delivery effects with all safe Python states, and checks the
concrete codec abstraction over its finite input domain. These are additional
bounded results; they do not fill an unmounted workflow by implication.

The next acceptance step is to address the remaining named exact-result gaps
and exercise the missing lifecycle histories against a frozen subject. The
read-only program bridge is mounted; persisting or promoting its evidence
would require its own explicit contract and tests. Real-owner authorization
and owner-approved scope revision require separate trusted-port designs and
tests. No production or complete-product acceptance claim follows from this
inventory.
