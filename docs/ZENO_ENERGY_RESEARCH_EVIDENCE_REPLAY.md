# ZenoEnergy Research Evidence Replay

```text
ok: true
check_count: 177
passed_count: 177
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
| production_promotion_gate.schema | pass | expected 'zenodex/energy/production_promotion_gate/v1', observed 'zenodex/energy/production_promotion_gate/v1' |
| production_promotion_gate.blocks_current_research | pass | gate blocks current synthetic/fixture-only evidence |
| production_promotion_gate.research_replay_clean | pass | clean research replay is necessary but insufficient for promotion |
| production_promotion_gate.safety_contract | pass | gate preserves verifier/policy authority and fallback boundary |
| production_promotion_gate.doc_and_source | pass | doc and source record real replay thresholds and ranking-only scope |
| replay_source_manifest.schema | pass | expected 'zenodex/energy/replay_source_manifest_receipt/v1', observed 'zenodex/energy/replay_source_manifest_receipt/v1' |
| replay_source_manifest.schemas_and_artifacts | pass | receipt and doc record source manifest schemas and artifacts |
| replay_source_manifest.source_hygiene_hooks | pass | checker validates fixture markers, secret scan, and source report hashes |
| replay_source_manifest.production_gate_hook | pass | production gate requires a passing source manifest check on real reports |
| replay_source_manifest.negative_knowledge | pass | receipt preserves advisory boundary and source-custody limits |
| replay_source_manifest_builder.schema | pass | expected 'zenodex/energy/replay_source_manifest_builder_receipt/v1', observed 'zenodex/energy/replay_source_manifest_builder_receipt/v1' |
| replay_source_manifest_builder.artifacts_and_schemas | pass | receipt, source, and doc record the manifest builder schema and artifacts |
| replay_source_manifest_builder.fail_closed_hooks | pass | builder computes source hashes, requires attestations, and fails closed on dirty secret scans |
| replay_source_manifest_builder.safety_and_limits | pass | builder preserves advisory boundary and records custody limits |
| replay_secret_scan.schema | pass | expected 'zenodex/energy/replay_secret_scan_receipt/v1', observed 'zenodex/energy/replay_secret_scan_receipt/v1' |
| replay_secret_scan.schemas_rules_and_artifacts | pass | receipt and doc record scanner schema, artifacts, and detector rules |
| replay_secret_scan.source_hooks | pass | scanner source, tests, and manifest builder integration are present |
| replay_secret_scan.safety_and_limits | pass | receipt preserves advisory boundary and scanner limits |
| replay_coverage_profile.schema | pass | expected 'zenodex/energy/replay_coverage_profile_receipt/v1', observed 'zenodex/energy/replay_coverage_profile_receipt/v1' |
| replay_coverage_profile.schemas_thresholds_and_artifacts | pass | receipt and doc record coverage profile schemas, thresholds, and artifacts |
| replay_coverage_profile.source_hooks | pass | checker validates breadth thresholds, source matching, and summary export |
| replay_coverage_profile.production_hooks | pass | production gate requires a passing coverage profile on real reports |
| replay_coverage_profile.safety_and_limits | pass | receipt preserves advisory boundary and representativeness limits |
| real_replay_report_builder.schema | pass | expected 'zenodex/energy/real_replay_report_builder_receipt/v1', observed 'zenodex/energy/real_replay_report_builder_receipt/v1' |
| real_replay_report_builder.targets_and_artifacts | pass | receipt and doc record both production-gate report schemas |
| real_replay_report_builder.source_hygiene_hooks | pass | builder rejects fixture markers and records source hashes, replay/secret attestations, and source manifest checks |
| real_replay_report_builder.safety_boundary | pass | builder preserves verifier/policy authority and records provenance limits |
| production_evidence_bundle.schema | pass | expected 'zenodex/energy/production_evidence_bundle_receipt/v1', observed 'zenodex/energy/production_evidence_bundle_receipt/v1' |
| production_evidence_bundle.artifacts_and_schemas | pass | receipt and doc record bundle schema, output schemas, and artifacts |
| production_evidence_bundle.source_hooks | pass | bundle composes real report builders, source manifest checks, and production gate |
| production_evidence_bundle.safety_and_limits | pass | bundle preserves advisory boundary, fail-closed manifest behavior, and custody limits |
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
| dominance_cover.schema | pass | dominance-cover benchmark and certificate schemas are stable |
| dominance_cover.winner_only_passes | pass | winner-only certificates pass over the verified full list |
| dominance_cover.weak_pruned_rejected | pass | weak pruned negative controls are rejected when better verified candidates are uncovered |
| dominance_cover.hand_top1_nonvacuous | pass | hand-energy top-1 pruning is a mixed baseline rather than a vacuous pass |
| dominance_cover.safety_and_hooks | pass | runtime checker preserves verifier authority and states finite-list scope |
| wes_dominance_search.schema | pass | WES bridge schema and pinned external WES commit are recorded |
| wes_dominance_search.candidate_corpus | pass | bounded WES candidate corpus and external source reference are stable |
| wes_dominance_search.useful_ordering | pass | WES-ranked policies find useful dominance-cover checks early under the static budget |
| wes_dominance_search.safety | pass | WES ranks checker calls only and records zero invalid accepts |
| wes_dominance_search.source_hooks | pass | bridge source, tests, and docs preserve WES as an advisory search layer |
| dominance_prefix.schema | pass | dominance-prefix benchmark and audit schemas are stable |
| dominance_prefix.safety | pass | prefix audit preserves verifier authority and records zero invalid accepts |
| dominance_prefix.learned_and_hybrid_cover_first | pass | learned and hybrid prefixes obtain dominance-cover certificates at the first checked candidate |
| dominance_prefix.beats_controls | pass | learned prefix cover beats hand and random controls on checked-call count |
| dominance_prefix.boundary_and_hooks | pass | source, tests, and docs preserve offline-prefix and suffix-bound limits |
| suffix_bound.schema | pass | suffix-bound benchmark and certificate schemas are stable |
| suffix_bound.safety | pass | suffix-bound early stop preserves verifier authority and records zero invalid accepts |
| suffix_bound.learned_and_hybrid_stop_first | pass | learned and hybrid suffix-bound certificates stop after roughly one verifier call |
| suffix_bound.beats_controls | pass | learned suffix-bound early stop beats hand and random controls on verifier calls |
| suffix_bound.boundary_and_hooks | pass | source, tests, Lean theorem, and docs preserve deterministic suffix-bound limits |
| suffix_bound_cross_seed.schema | pass | suffix-bound cross-seed stress schema and parameter grid are stable |
| suffix_bound_cross_seed.safety | pass | cross-seed suffix-bound stress has zero invalid accepts and keeps verifier authority |
| suffix_bound_cross_seed.learned_and_hybrid_hold | pass | learned and hybrid keep complete objective-equivalent acceptance and suffix stops |
| suffix_bound_cross_seed.beats_controls | pass | learned and hybrid beat hand and random on verifier-call stress metrics |
| suffix_bound_cross_seed.boundary_and_hooks | pass | tool, test, and doc preserve bounded synthetic and coverage limits |
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
| popperpad.status.H_ZENOENERGY_PRODUCTION_GATE_BLOCKS_WITHOUT_REAL_REPLAY_20260518 | pass | H_ZENOENERGY_PRODUCTION_GATE_BLOCKS_WITHOUT_REAL_REPLAY_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_CHECKER_20260518 | pass | H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_CHECKER_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_BUILDER_20260518 | pass | H_ZENOENERGY_REPLAY_SOURCE_MANIFEST_BUILDER_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPLAY_SECRET_SCAN_20260518 | pass | H_ZENOENERGY_REPLAY_SECRET_SCAN_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REPLAY_COVERAGE_PROFILE_20260518 | pass | H_ZENOENERGY_REPLAY_COVERAGE_PROFILE_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_REAL_REPLAY_REPORT_BUILDER_20260518 | pass | H_ZENOENERGY_REAL_REPLAY_REPORT_BUILDER_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_PRODUCTION_EVIDENCE_BUNDLE_20260518 | pass | H_ZENOENERGY_PRODUCTION_EVIDENCE_BUNDLE_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_BEATS_HAND_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518 | pass | H_AUTOTRADER_ENERGY_HARD_CROSS_SEED_PROFILE_NONVACUOUS_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_SAFETY_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_NONVACUOUS_20260518 is recorded as supported |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_LEARNED_BEATS_HAND_20260518 is recorded as falsified |
| popperpad.status.H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518 | pass | H_AUTOTRADER_ENERGY_SHADOW_BRIDGE_OBJECTIVE_EQUIV_TOP1_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_DOMINANCE_COVER_RUNTIME_20260518 | pass | H_ZENOENERGY_DOMINANCE_COVER_RUNTIME_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_WEAK_PRUNED_DOMINANCE_ALWAYS_PASSES_20260518 | pass | H_ZENOENERGY_WEAK_PRUNED_DOMINANCE_ALWAYS_PASSES_20260518 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_WES_DOMINANCE_SEARCH_BRIDGE_20260518 | pass | H_ZENOENERGY_WES_DOMINANCE_SEARCH_BRIDGE_20260518 is recorded as supported |
| popperpad.status.H_ZENOENERGY_WES_REMOVES_FULL_LIST_COMPLETENESS_20260518 | pass | H_ZENOENERGY_WES_REMOVES_FULL_LIST_COMPLETENESS_20260518 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_DOMINANCE_PREFIX_AUDIT_20260519 | pass | H_ZENOENERGY_DOMINANCE_PREFIX_AUDIT_20260519 is recorded as supported |
| popperpad.status.H_ZENOENERGY_DOMINANCE_PREFIX_AUTHORIZES_LIVE_EARLY_STOP_20260519 | pass | H_ZENOENERGY_DOMINANCE_PREFIX_AUTHORIZES_LIVE_EARLY_STOP_20260519 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_EARLY_STOP_20260519 | pass | H_ZENOENERGY_SUFFIX_BOUND_EARLY_STOP_20260519 is recorded as supported |
| popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_REMOVES_COVERAGE_OBLIGATION_20260519 | pass | H_ZENOENERGY_SUFFIX_BOUND_REMOVES_COVERAGE_OBLIGATION_20260519 is recorded as falsified |
| popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_STRESS_20260519 | pass | H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_STRESS_20260519 is recorded as supported |
| popperpad.status.H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_REMOVES_REAL_REPLAY_NEED_20260519 | pass | H_ZENOENERGY_SUFFIX_BOUND_CROSS_SEED_REMOVES_REAL_REPLAY_NEED_20260519 is recorded as falsified |
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
  "dominance_cover": {
    "evaluated_batches": 79,
    "hand_top1_failed_count": 23,
    "hand_top1_ok_count": 56,
    "invalid_accept_count": 0,
    "negative_knowledge": [
      "A weak pruned set with an uncovered better verified candidate fails the dominance-cover check.",
      "Dominance-cover certificates are about pruning correctness, not about model accuracy."
    ],
    "schema": "zenodex/energy/upba_v2_dominance_cover_benchmark/v1",
    "weak_pruned_count": 75,
    "weak_pruned_failed_count": 75,
    "winner_only_count": 79,
    "winner_only_ok_count": 79
  },
  "dominance_prefix": {
    "evaluated_batches": 119,
    "hand_mean_prefix_checked_count": 1.4453781512605042,
    "hybrid_mean_prefix_checked_count": 1,
    "invalid_accept_count": 0,
    "learned_mean_prefix_checked_count": 1,
    "learned_p99_prefix_checked_count": 1.0,
    "model_path": "data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json",
    "negative_knowledge": [
      "Dominance-prefix certificates measure ranked search cost; they do not make model scores authoritative.",
      "If a ranked prefix reaches the full candidate list, the certificate gives no verifier-call savings over full fallback."
    ],
    "random_full_fallback_count": 5,
    "random_mean_prefix_checked_count": 12.882352941176471,
    "schema": "zenodex/energy/upba_v2_dominance_prefix_benchmark/v1"
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
  "production_evidence_bundle": {
    "bundle_schema": "zenodex/energy/production_evidence_bundle/v1",
    "claim": "ZenoEnergy production-adjacent review now has a single fail-closed evidence bundle command that assembles source-manifested and coverage-profiled UPBA and AutoTrader real replay reports, then runs the production promotion gate.",
    "negative_knowledge": [
      "Synthetic and built-in fixture evidence remains research evidence even when the bundle command can parse it.",
      "Without passing replay source manifests, coverage profiles, and real replay coverage, the production promotion gate remains blocked.",
      "A passing bundle is not a settlement authorization path."
    ],
    "supported_status": "supported"
  },
  "production_promotion_gate": {
    "blocked_reasons": [
      "operator must explicitly enable advisory ranking-only promotion",
      "missing real UPBA replay report",
      "missing real AutoTrader shadow report"
    ],
    "decision": "blocked",
    "negative_knowledge": "Current ZenoEnergy evidence remains research-grade until real UPBA replay and real AutoTrader shadow reports satisfy this gate.",
    "promotion_allowed": false,
    "scope": "advisory_ranking_only"
  },
  "real_replay_report_builder": {
    "claim": "ZenoEnergy has a deterministic builder for the real UPBA replay and AutoTrader shadow report schemas consumed by the production promotion gate.",
    "negative_knowledge": [
      "Synthetic and built-in fixture reports remain research evidence.",
      "A real-report JSON without passing replay source manifest and coverage profile checks, replay provenance, and secret-scrubbing custody is insufficient for production promotion."
    ],
    "supported_status": "supported",
    "target_schemas": [
      "zenodex/energy/upba_real_replay_report/v1",
      "zenodex/energy/autotrader_real_shadow_report/v1"
    ]
  },
  "repair_selector_cross_seed": {
    "compression_pass_count": 3,
    "invalid_accept_count": 0,
    "original_subset_violation_count": 0,
    "run_count": 3,
    "strict_hand_win_count": 1
  },
  "replay_coverage_profile": {
    "claim": "ZenoEnergy has a deterministic coverage-profile checker that rejects narrow real replay evidence before advisory ranking promotion.",
    "negative_knowledge": [
      "Aggregate batch, candidate, context, or row counts are insufficient when coverage is concentrated in one narrow source family.",
      "A passing coverage profile is not a production authorization path.",
      "Coverage breadth remains separate from deterministic verifier and policy-guard authority."
    ],
    "profile_check_schema": "zenodex/energy/replay_coverage_profile_check/v1",
    "profile_schema": "zenodex/energy/replay_coverage_profile/v1",
    "thresholds": {
      "autotrader": {
        "min_contexts_per_market_day": 20,
        "min_decision_family_count": 3,
        "min_guard_family_count": 4,
        "min_strategy_family_count": 3
      },
      "upba": {
        "min_batches_per_market_day": 50,
        "min_candidate_family_count": 4,
        "min_hard_negative_family_count": 4,
        "min_intent_size_bucket_count": 3,
        "min_pool_count": 3
      }
    }
  },
  "replay_secret_scan": {
    "claim": "ZenoEnergy has a deterministic replay secret-scan tool that catches obvious key material and sensitive JSON keys before real replay reports are packaged into source manifests.",
    "negative_knowledge": [
      "A clean scanner report is weaker than a full privacy audit.",
      "The scanner is a deterministic guardrail for replay packaging, not a production promotion decision.",
      "Source manifests still require operator no-live-secrets attestation and production gate review."
    ],
    "scanner_rules": [
      "private_key_pem",
      "aws_access_key_id",
      "openai_api_key",
      "github_token",
      "sensitive_json_key"
    ],
    "secret_scan_schema": "zenodex/energy/replay_secret_scan/v1"
  },
  "replay_source_manifest": {
    "claim": "ZenoEnergy has a fail-closed replay source manifest checker that binds real replay reports to source kind, descriptor, market-day coverage, source hashes, deterministic replay, and secret-scan status.",
    "negative_knowledge": [
      "A real-report JSON without a passing replay source manifest check is insufficient for production promotion.",
      "A passing manifest check is still weaker than an audited custody chain."
    ],
    "source_manifest_check_schema": "zenodex/energy/replay_source_manifest_check/v1",
    "source_manifest_schema": "zenodex/energy/replay_source_manifest/v1",
    "supported_status": "supported"
  },
  "replay_source_manifest_builder": {
    "builder_schema": "zenodex/energy/replay_source_manifest_builder/v1",
    "check_schema": "zenodex/energy/replay_source_manifest_check/v1",
    "claim": "ZenoEnergy has a fail-closed replay source manifest builder that computes canonical source report hashes, records replay and secret-scan attestations, and validates the manifest before writing it.",
    "negative_knowledge": [
      "A generated manifest is necessary packaging for real replay, not sufficient production evidence.",
      "A clean secret-scan attestation is weaker than a complete privacy audit.",
      "The builder intentionally refuses synthetic, fixture-like, built-in, or generated descriptors."
    ],
    "output_schema": "zenodex/energy/replay_source_manifest/v1"
  },
  "set_aware_negative_knowledge": "Extra set-aware moment features did not improve the linear ranker on this comparison run. Keep the aggregate gap-weighted checkpoint as the measured default until cross-seed evidence supports a change.",
  "sota_decision_map": {
    "claim": "Current solver-learning and energy-model guidance supports listwise/set-aware ranker and outcome-level repair-selector experiments while preserving verifier-authoritative fallback or certificates.",
    "negative_knowledge_count": 3,
    "next_experiment_count": 4,
    "required_decision_count": 7,
    "source_count": 10
  },
  "suffix_bound": {
    "evaluated_batches": 119,
    "hand_mean_verifier_calls": 1.4201680672268908,
    "hybrid_mean_verifier_calls": 1.0084033613445378,
    "invalid_accept_count": 0,
    "learned_mean_verifier_calls": 1.0084033613445378,
    "learned_p99_verifier_calls": 1.0,
    "limits": [
      "This benchmark uses bounded synthetic finite candidate lists.",
      "The suffix bound is deterministic, but a production bounded-grid claim still needs candidate-family coverage.",
      "Attractive invalid unchecked candidates can force more verifier calls because their declared outputs remain upper bounds until checked."
    ],
    "model_path": "data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json",
    "random_full_fallback_count": 2,
    "random_mean_verifier_calls": 13.184873949579831,
    "schema": "zenodex/energy/upba_v2_suffix_bound_benchmark/v1"
  },
  "suffix_bound_cross_seed": {
    "batches_per_config": 60,
    "candidate_counts": [
      20,
      32,
      50
    ],
    "hand_mean_verifier_calls": 1.393488128073935,
    "hybrid_mean_verifier_calls": 1.0132173084832348,
    "invalid_accept_count_total": 0,
    "learned_mean_verifier_calls": 1.0132173084832348,
    "learned_p99_verifier_calls_max": 4.0,
    "negative_knowledge": [
      "Cross-seed suffix-bound stress remains bounded synthetic evidence.",
      "A stable suffix-bound stress result still does not prove candidate-family coverage."
    ],
    "random_full_fallback_count": 16,
    "random_mean_verifier_calls": 17.100984969404482,
    "schema": "zenodex/energy/upba_v2_suffix_bound_cross_seed/v1",
    "seeds": [
      20260541,
      20260542,
      20260543
    ],
    "synthetic_batches_requested": 540,
    "synthetic_candidates_requested": 18360
  },
  "topk_sweep": {
    "batches": 1983,
    "learned_k2_checked_stop_rate": 1.0,
    "learned_k2_false_exclusion_rate": 0.0,
    "learned_k2_objective_false_exclusion_rate": 0.0,
    "learned_mean_objective_winner_position": 1.0166414523449319,
    "objective_tie_batch_count": 1,
    "random_k10_false_exclusion_rate": 0.4931921331316188
  },
  "wes_dominance_search": {
    "budget": 60,
    "checker_invalid_accept_count": 0,
    "declared_priority_useful_at_k": 24,
    "input_candidates": 120,
    "model_frozen_useful_at_k": 24,
    "model_online_useful_at_k": 24,
    "negative_knowledge": [
      "Weak pruned sets remain useful negative controls because the checker rejects uncovered better verified candidates.",
      "A passing WES search report does not remove the full-list completeness obligation for bounded-grid claims."
    ],
    "random_seeded_useful_at_k": 23,
    "schema": "zenodex/energy/zenoenergy_wes_dominance_search/v1",
    "top_k": 25,
    "wes_commit": "5a26bcc1d97c90503bb66e67c7c2a2cf40d41bb6"
  }
}
```
