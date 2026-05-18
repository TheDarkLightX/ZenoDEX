# ZenoEnergy Research Evidence Replay

```text
ok: true
check_count: 104
passed_count: 104
failed_count: 0
```

| check | result | detail |
| --- | --- | --- |
| set_aware.schema | pass | expected 'zenodex/energy/upba_v2_set_aware_comparison/v1', observed 'zenodex/energy/upba_v2_set_aware_comparison/v1' |
| set_aware.zero_invalid_accepts | pass | all modes have invalid_accept_count = 0 |
| set_aware.aggregate_top10_recall | pass | aggregate learned top_10_recall is 1.0 |
| set_aware.negative_knowledge_recorded | pass | set-aware linear ranker did not beat aggregate learned baseline |
| listwise_set.schema | pass | expected 'zenodex/energy/upba_v2_listwise_set_ranker_comparison/v1', observed 'zenodex/energy/upba_v2_listwise_set_ranker_comparison/v1' |
| listwise_set.safety | pass | zero invalid accepts and zero listwise permutation violations |
| listwise_set.top10_and_checked_stop | pass | listwise top-10 recall and checked-stop-at-winner audit remain complete |
| listwise_set.negative_knowledge | pass | listwise ranker did not beat the strongest pairwise baseline on mean calls |
| listwise_cross_seed.schema | pass | expected 'zenodex/energy/upba_v2_listwise_set_ranker_cross_seed/v1', observed 'zenodex/energy/upba_v2_listwise_set_ranker_cross_seed/v1' |
| listwise_cross_seed.safety | pass | all cross-seed listwise runs have zero invalid accepts and zero permutation violations |
| listwise_cross_seed.top10_and_checked_stop | pass | listwise top-10 recall and checked-stop-at-winner audits pass on every seed pair |
| listwise_cross_seed.negative_knowledge | pass | listwise ranker does not strictly improve over pairwise on cross-seed stress |
| gap_weighted_default.schemas | pass | gap-weighted stress, hard-case, and model-audit schemas are stable |
| gap_weighted_default.cross_seed_safety | pass | learned gap-weighted scorer has zero invalid accepts, complete top-10 recall, and low p99 calls |
| gap_weighted_default.cross_seed_beats_hand | pass | learned gap-weighted scorer improves mean verifier calls and top-1 recall over hand energy |
| gap_weighted_default.hard_case_recall | pass | hard-case mining has no top-5/top-10 misses and p99 winner position at most 2 |
| gap_weighted_default.model_audit_boundary | pass | model audit keeps the tiny linear scorer away from forbidden and reserved features |
| neighborhood.schema | pass | expected 'zenodex/energy/upba_v2_neighborhood_benchmark/v1', observed 'zenodex/energy/upba_v2_neighborhood_benchmark/v1' |
| neighborhood.safety | pass | zero invalid accepts, zero subset violations, verifier authoritative |
| neighborhood.regret_reduced | pass | neighborhood reduces mean volume regret versus limited |
| neighborhood.call_cost_negative | pass | neighborhood increases calls until full winner, negative knowledge preserved |
| repair_selector.schema | pass | expected 'zenodex/energy/upba_v2_repair_selector_benchmark/v1', observed 'zenodex/energy/upba_v2_repair_selector_benchmark/v1' |
| repair_selector.safety | pass | zero invalid accepts and verifier authoritative |
| repair_selector.compression | pass | learned selector compresses full neighborhood without higher mean volume regret |
| repair_selector.hand_baseline_negative | pass | learned selector does not strictly beat hand-selected subset on this split |
| repair_selector_cross_seed.schema | pass | expected 'zenodex/energy/upba_v2_repair_selector_cross_seed/v1', observed 'zenodex/energy/upba_v2_repair_selector_cross_seed/v1' |
| repair_selector_cross_seed.safety | pass | all cross-seed runs have zero invalid accepts and zero subset violations |
| repair_selector_cross_seed.compression_all_pairs | pass | compression passed on every seed pair |
| repair_selector_cross_seed.aggregate_regret | pass | learned selected aggregate mean regret is no worse than full neighborhood |
| repair_selector_cross_seed.hand_negative | pass | learned selector does not strictly beat hand-selected subset on every seed pair |
| formal_boundary.schema | pass | expected 'zenodex/energy/upba_v2_repair_selector_formal_boundary_receipt/v1', observed 'zenodex/energy/upba_v2_repair_selector_formal_boundary_receipt/v1' |
| formal_boundary.commands | pass | Lean target and focused formal regression are recorded as passing |
| formal_boundary.names | pass | selector-specific Lean names are present in receipt |
| formal_boundary.scope_limit | pass | receipt states base-list scope limit |
| fallback_checked_stop_formal.schema | pass | expected 'zenodex/energy/upba_v2_fallback_checked_stop_formal_receipt/v1', observed 'zenodex/energy/upba_v2_fallback_checked_stop_formal_receipt/v1' |
| fallback_checked_stop_formal.commands | pass | Lean target and focused formal regression are recorded as passing |
| fallback_checked_stop_formal.names | pass | fallback and checked-stop theorem names are present in receipt and Lean source |
| fallback_checked_stop_formal.no_placeholders | pass | Lean source has no sorry/admit/axiom/unsafe placeholders |
| fallback_checked_stop_formal.scope_limit | pass | receipt states online early-stop suffix-bound limit |
| fallback_checked_stop_formal.objective_equivalence_limit | pass | receipt states objective-equivalent verifier-acceptance limit |
| fallback_permutation_audit.schema | pass | expected 'zenodex/energy/upba_v2_benchmark_report/v1', observed 'zenodex/energy/upba_v2_benchmark_report/v1' |
| fallback_permutation_audit.zero_invalid_accepts | pass | all fallback audit modes have zero invalid accepts |
| fallback_permutation_audit.permutation_premise | pass | all audit modes preserve the full-fallback permutation premise |
| fallback_permutation_audit.learned_recovery | pass | learned and hybrid orderings recover every exact winner by top-k or fallback |
| fallback_permutation_audit.checked_stop_offline | pass | checked-stop audit succeeds for learned top-k and remains nontrivial versus random |
| fallback_permutation_audit.objective_equivalence_metrics | pass | fallback audit reports objective-equivalent recall and call position |
| topk_sweep.schema | pass | expected 'zenodex/energy/upba_v2_topk_sweep/v1', observed 'zenodex/energy/upba_v2_topk_sweep/v1' |
| topk_sweep.permutation_premise | pass | all top-k sweep modes preserve hash-permutation ordering |
| topk_sweep.learned_checked_stop_k2 | pass | learned and hybrid checked-stop audits reach 100% by k=2 on holdout |
| topk_sweep.checked_stop_at_winner | pass | checked-stop certificate holds at the exact winner for every mode |
| topk_sweep.objective_equivalence_metrics | pass | top-k sweep reports objective-equivalent recall and call position |
| topk_sweep.random_top10_negative | pass | random top-10 misses many winners, so the sweep is not vacuous |
| objective_equiv_training_hygiene.schema | pass | expected 'zenodex/energy/upba_v2_objective_equiv_training_hygiene_receipt/v1', observed 'zenodex/energy/upba_v2_objective_equiv_training_hygiene_receipt/v1' |
| objective_equiv_training_hygiene.modes | pass | receipt records replay default and objective-equivalent research mode |
| objective_equiv_training_hygiene.source_hooks | pass | trainer and focused tests expose objective-equivalent positive-class hooks |
| objective_equiv_training_hygiene.safety_boundary | pass | receipt and doc keep the change on the advisory training boundary |
| objective_equiv_training_hygiene.no_metric_claim | pass | receipt records this as label hygiene rather than performance evidence |
| sota_decision_map.schema | pass | expected 'zenodex/energy/upba_v2_sota_decision_map_receipt/v1', observed 'zenodex/energy/upba_v2_sota_decision_map_receipt/v1' |
| sota_decision_map.sources_and_boundary | pass | decision map records all required sources and verifier/fallback boundary |
| sota_decision_map.decisions | pass | all required model-direction decisions are recorded in receipt and doc |
| sota_decision_map.next_experiments | pass | all next experiments are recorded in receipt and doc |
| sota_decision_map.negative_knowledge | pass | negative knowledge and guidance-only limit are preserved |
| autotrader_energy_hard_cross_seed.schema | pass | expected 'zenodex/energy/autotrader_cross_seed_report/v1', observed 'zenodex/energy/autotrader_cross_seed_report/v1' |
| autotrader_energy_hard_cross_seed.safety | pass | zero invalid accepts and deterministic AutoTrader policy guards remain authoritative |
| autotrader_energy_hard_cross_seed.learned_beats_hand_all | pass | learned AutoTraderEnergy ordering reduces mean guard calls versus hand and random on every seed pair |
| autotrader_energy_hard_cross_seed.profile_nonvacuous | pass | hard profile exercises nontrivial guard ordering |
| autotrader_energy_hard_cross_seed.doc_and_recall | pass | receipt records high top-5 recall plus the synthetic-to-shadow evidence boundary |
| autotrader_energy_shadow_bridge.schema | pass | expected 'zenodex/energy/autotrader_shadow_bridge_report/v1', observed 'zenodex/energy/autotrader_shadow_bridge_report/v1' |
| autotrader_energy_shadow_bridge.safety | pass | zero invalid accepts and deterministic AutoTrader policy guards remain authoritative |
| autotrader_energy_shadow_bridge.nonvacuous_fixture | pass | shadow fixture has multiple candidates per context plus valid and invalid outcomes |
| autotrader_energy_shadow_bridge.learned_ties_hand_negative | pass | learned ordering ties hand energy, beats random mean calls, and records top-1 miss knowledge |
| autotrader_energy_shadow_bridge.objective_equiv_argmax | pass | objective-equivalent argmax recall separates tied maxima from hash-selected exact winner misses |
| autotrader_energy_shadow_bridge.doc_boundary | pass | shadow bridge doc records fixture scope and argmax-equivalence boundary |
| popperpad.status.H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517 | pass | H_ZENOENERGY_SET_AWARE_COMPARE_SAFETY_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517 | pass | H_ZENOENERGY_SET_AWARE_LINEAR_STRICTLY_IMPROVES_AGGREGATE_20260517 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2 | pass | H_ZENOENERGY_NEIGHBORHOOD_SAFETY_SUBSET_20260517_V2 is recorded as supported |
| popperpad.status.H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2 | pass | H_ZENOENERGY_NEIGHBORHOOD_REDUCES_REGRET_20260517_V2 is recorded as supported |
| popperpad.status.H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2 | pass | H_ZENOENERGY_NEIGHBORHOOD_REDUCES_VERIFIER_CALLS_20260517_V2 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_SAFETY_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_COMPRESSES_FULL_NEIGHBORHOOD_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_STRICTLY_BEATS_HAND_SELECTED_20260517 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_SAFETY_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_COMPRESSES_FULL_NEIGHBORHOOD_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_CROSS_SEED_STRICTLY_BEATS_HAND_SELECTED_20260517 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517 | pass | H_ZENOENERGY_REPAIR_SELECTOR_FORMAL_BOUNDARY_RECEIPT_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517 | pass | H_ZENOENERGY_FALLBACK_CHECKED_STOP_FORMAL_RECEIPT_20260517 is recorded as supported |
| popperpad.status.H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518 | pass | H_ZENOENERGY_SOTA_DECISION_MAP_RECEIPT_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518 | pass | H_ZENOENERGY_LISTWISE_SET_RANKER_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518 | pass | H_ZENOENERGY_LISTWISE_SET_RANKER_STRICTLY_IMPROVES_PAIRWISE_20260518 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518 | pass | H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518 | pass | H_ZENOENERGY_LISTWISE_SET_RANKER_CROSS_SEED_STRICTLY_IMPROVES_PAIRWISE_20260518 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518 | pass | H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518 | pass | H_ZENOENERGY_GAP_WEIGHTED_DEFAULT_BEATS_HAND_ENERGY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_FORMAL_BOUNDARY_RECEIPT_20260518 | pass | H_ZENOENERGY_OBJECTIVE_EQUIV_FORMAL_BOUNDARY_RECEIPT_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_RUNTIME_TELEMETRY_20260518 | pass | H_ZENOENERGY_OBJECTIVE_EQUIV_RUNTIME_TELEMETRY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE_20260518 | pass | H_ZENOENERGY_OBJECTIVE_EQUIV_TRAINING_HYGIENE_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518 is recorded as falsified |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518 is recorded as supported |
| popperpad.doctor | pass | PopperPad doctor ok |

## Summary

```json
{
  "autotrader_energy_hard_cross_seed": {
    "hand_mean_guard_calls": 4.312,
    "invalid_accept_count_total": 0,
    "learned_beats_hand_count": 3,
    "learned_mean_guard_calls": 1.0103333333333333,
    "learned_top_5_recall_min": 1.0,
    "positive_knowledge": "The hard synthetic AutoTraderEnergy scorer reduced guard calls on every evaluated seed pair while preserving deterministic guard authority.",
    "random_mean_guard_calls": 8.393333333333333,
    "run_count": 3,
    "safety_pass_count": 3
  },
  "autotrader_energy_shadow_bridge": {
    "argmax_equivalence_note": "Exact top-1 recall uses a hash-selected winner among tied valid objective maxima. Objective-equivalent recall treats any valid candidate with the same maximal objective as an acceptable argmax representative.",
    "context_count": 4,
    "hand_mean_guard_calls": 2,
    "invalid_accept_count_total": 0,
    "invalid_count": 8,
    "learned_mean_guard_calls": 2,
    "learned_mean_guard_calls_to_objective_winner": 1,
    "learned_top_1_objective_recall": 1.0,
    "learned_top_1_recall": 0.0,
    "learned_top_5_recall": 1.0,
    "negative_knowledge": "The built-in shadow bridge is a deterministic fixture derived from accepted ZenoGraph store exports. It is useful for schema and boundary replay, but it is not live production distribution evidence.",
    "objective_tie_batch_count": 4,
    "random_mean_guard_calls": 3.25,
    "row_count": 20,
    "source": "built-in-zenograph-baseline",
    "valid_count": 12
  },
  "fallback_checked_stop_claim": "Full deterministic fallback is order-equivalent when the ranked order is a permutation of the exact finite candidate list. Checked early stop is safe only with a verifier-facing certificate that the checked winner dominates the checked prefix and the unchecked suffix, plus exact coverage of the full candidate list. A verifier-accepted candidate with the same volume and surplus as a certified representative is an objective-equivalent global weak optimum over the same exact finite family.",
  "fallback_permutation_audit": {
    "batches": 200,
    "invalid_accept_count": 0,
    "learned_checked_stop_top_k_rate": 1.0,
    "learned_mean_calls_to_objective_winner": 1.01,
    "learned_permutation_violation_count": 0,
    "learned_top_10_objective_recall": 1.0,
    "learned_top_10_recall": 1.0
  },
  "formal_boundary_claim": "The repair selector has a Lean-checked base-preservation boundary: selected repair sets preserve weak optimality over the base list when the deterministic verifier supplies an upper-bound certificate over the selected set.",
  "gap_weighted_default": {
    "cross_seed_configs": 9,
    "hand_mean_verifier_calls": 1.3260782880941833,
    "hard_case_batches_with_winner": 4466,
    "hard_case_top10_miss_count": 0,
    "hard_case_top_10_recall": 1.0,
    "learned_invalid_accept_count_total": 0,
    "learned_mean_verifier_calls": 1.0175080393875215,
    "learned_top_10_recall_min": 1.0,
    "model_parameter_count": 97,
    "model_reserved_nonzero_count": 0
  },
  "listwise_cross_seed": {
    "checked_stop_at_winner_pass_count": 3,
    "invalid_accept_count": 0,
    "listwise_top10_pass_count": 3,
    "negative_knowledge": "The listwise set ranker did not strictly improve over the best pairwise baseline on every seed pair.",
    "permutation_violation_count": 0,
    "run_count": 3,
    "strict_improvement_count": 0
  },
  "listwise_set": {
    "aggregate_pairwise_mean_verifier_calls": 1.0263157894736843,
    "listwise_improved_over_best_pairwise": false,
    "listwise_mean_verifier_calls": 1.0657894736842106,
    "listwise_permutation_violation_count": 0,
    "listwise_top_10_recall": 1.0,
    "negative_knowledge": "The first listwise set-context ranker did not improve mean verifier calls against the strongest pairwise baseline on this bounded synthetic split."
  },
  "neighborhood_regret_delta": -273.6375,
  "objective_equiv_training_hygiene": {
    "claim": "ZenoEnergy pairwise training can weight every verifier-accepted tied maximum-objective candidate as a positive example, avoiding extra pressure toward the arbitrary hash-selected representative.",
    "default_positive_class": "hash-winner",
    "positive_class_modes": [
      "hash-winner",
      "objective-equivalent"
    ],
    "recommended_research_positive_class": "objective-equivalent"
  },
  "repair_selector_cross_seed": {
    "compression_pass_count": 3,
    "invalid_accept_count": 0,
    "original_subset_violation_count": 0,
    "run_count": 3,
    "strict_hand_win_count": 1
  },
  "set_aware_negative_knowledge": "Extra set-aware moment features did not improve the linear ranker on this comparison run. Keep the aggregate gap-weighted checkpoint as the measured default until cross-seed evidence supports a change.",
  "sota_decision_map": {
    "claim": "Current solver-learning and energy-model guidance supports listwise/set-aware ranker and outcome-level repair-selector experiments while preserving verifier-authoritative fallback or certificates.",
    "negative_knowledge_count": 3,
    "next_experiment_count": 4,
    "required_decision_count": 7,
    "source_count": 10
  },
  "topk_sweep": {
    "batches": 1983,
    "learned_k2_checked_stop_rate": 1.0,
    "learned_k2_false_exclusion_rate": 0.0,
    "learned_k2_objective_false_exclusion_rate": 0.0,
    "learned_mean_objective_winner_position": 1.0166414523449319,
    "objective_tie_batch_count": 1,
    "random_k10_false_exclusion_rate": 0.4931921331316188
  }
}
```
