# ZenoEnergy Research Evidence Replay

```text
ok: true
check_count: 34
passed_count: 34
failed_count: 0
```

| check | result | detail |
| --- | --- | --- |
| set_aware.schema | pass | expected 'zenodex/energy/upba_v2_set_aware_comparison/v1', observed 'zenodex/energy/upba_v2_set_aware_comparison/v1' |
| set_aware.zero_invalid_accepts | pass | all modes have invalid_accept_count = 0 |
| set_aware.aggregate_top10_recall | pass | aggregate learned top_10_recall is 1.0 |
| set_aware.negative_knowledge_recorded | pass | set-aware linear ranker did not beat aggregate learned baseline |
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
| popperpad.doctor | pass | PopperPad doctor ok |

## Summary

```json
{
  "formal_boundary_claim": "The repair selector has a Lean-checked base-preservation boundary: selected repair sets preserve weak optimality over the base list when the deterministic verifier supplies an upper-bound certificate over the selected set.",
  "neighborhood_regret_delta": -273.6375,
  "repair_selector_cross_seed": {
    "compression_pass_count": 3,
    "invalid_accept_count": 0,
    "original_subset_violation_count": 0,
    "run_count": 3,
    "strict_hand_win_count": 1
  },
  "set_aware_negative_knowledge": "Extra set-aware moment features did not improve the linear ranker on this comparison run. Keep the aggregate gap-weighted checkpoint as the measured default until cross-seed evidence supports a change."
}
```
