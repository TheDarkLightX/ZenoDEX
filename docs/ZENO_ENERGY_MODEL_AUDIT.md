# ZenoEnergy Model Audit

```text
model: data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json
parameters: 97
feature_dim: 96
nonzero_weight_count: 38
reserved_nonzero_count: 0
forbidden_feature_names: none
```

Negative weights lower energy and move a candidate earlier. Positive weights raise energy and move a candidate later.

## Largest Positive Weights

| feature | weight |
| --- | ---: |
| candidate_negative_reserve_flag | 1e+06 |
| candidate_invariant_violation_flag | 1e+06 |
| candidate_limit_violation_count_norm | 1e+06 |
| candidate_balance_violation_count_norm | 1e+06 |
| candidate_noncanonical_fill_vector_flag | 100000 |
| candidate_price_objective_violation_flag | 100000 |
| candidate_output_mismatch_count_norm | 100000 |
| candidate_schema_policy_mismatch_flag | 100000 |
| candidate_fill_coverage_violation_flag | 100000 |
| candidate_duplicate_fill_id_flag | 100000 |
| candidate_unknown_fill_id_count_norm | 100000 |
| candidate_executed_input_over_amount_count_norm | 100000 |

## Largest Negative Weights

| feature | weight |
| --- | ---: |
| candidate_normalized_executed_volume | -58.0118 |
| candidate_normalized_surplus | -28.778 |
| candidate_volume_log1p | -9.74208 |
| candidate_surplus_signed | -7.63167 |
| candidate_executed_quote_out_log1p | -5.82504 |
| candidate_net_base_in_log1p | -5.62421 |
| candidate_executed_base_in_log1p | -5.56477 |
| candidate_net_quote_in_log1p | -5.17666 |
| candidate_executed_quote_in_log1p | -5.11413 |
| candidate_executed_base_out_log1p | -4.87426 |
| candidate_total_fee_log1p | -2.7272 |
| candidate_price_num_log1p | -2.31218 |

## Largest Changes From Hand Initialization

| feature | weight | hand_init | delta |
| --- | ---: | ---: | ---: |
| candidate_dust_penalty_norm | 48.9776 | 100 | -51.0224 |
| candidate_normalized_executed_volume | -58.0118 | -10 | -48.0118 |
| candidate_normalized_surplus | -28.778 | -1 | -27.778 |
| candidate_imbalance_penalty | -0.856459 | 10 | -10.8565 |
| candidate_volume_log1p | -9.74208 | 0 | -9.74208 |
| candidate_surplus_signed | -7.63167 | 0 | -7.63167 |
| candidate_executed_quote_out_log1p | -5.82504 | 0 | -5.82504 |
| candidate_net_base_in_log1p | -5.62421 | 0 | -5.62421 |
| candidate_executed_base_in_log1p | -5.56477 | 0 | -5.56477 |
| candidate_net_quote_in_log1p | -5.17666 | 0 | -5.17666 |
| candidate_executed_quote_in_log1p | -5.11413 | 0 | -5.11413 |
| candidate_executed_base_out_log1p | -4.87426 | 0 | -4.87426 |
