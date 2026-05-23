# ZenoEnergy Ensemble

schema: `zenodex/energy/upba_v2_ensemble_report/v1`
member_count: 6
total_parameter_count: 582

| mode | top-1 | top-10 | mean calls | p95 | p99 | miss AUC | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| current_gap_weighted | 0.9834 | 1.0000 | 1.0166 | 1 | 2 | n/a | 0 |
| ensemble_mean_energy | 0.9813 | 1.0000 | 1.0237 | 1 | 2 | 0.6814 | 0 |
| ensemble_mean_rank | 0.9813 | 1.0000 | 1.0237 | 1 | 2 | 0.6819 | 0 |
| ensemble_rank_std_penalty_0_25 | 0.9813 | 1.0000 | 1.0237 | 1 | 2 | 0.6819 | 0 |
| ensemble_rank_std_penalty_0_5 | 0.9813 | 1.0000 | 1.0237 | 1 | 2 | 0.6819 | 0 |
| ensemble_rank_std_penalty_1_0 | 0.9813 | 1.0000 | 1.0247 | 1 | 2 | 0.6819 | 0 |
| ensemble_rank_std_penalty_2_0 | 0.9813 | 1.0000 | 1.0277 | 1 | 2 | 0.6819 | 0 |

## Interpretation

The ensemble lane tests rank consensus and disagreement as an advisory uncertainty signal while deterministic verification and fallback remain authoritative.

If the best ensemble mode does not beat the current gap-weighted checkpoint, keep the single retained UPBA model as the default and use ensemble disagreement only as diagnostic coverage evidence.

best_ensemble_mode: `ensemble_mean_energy`
best_ensemble_beats_current_gap_weighted: False
best_uncertainty_auc: 0.6819

## Safety

`invalid_accept_count_total = 0`; the ensemble ranks candidates only.
Deterministic UPBA verification and fallback remain the authority.
