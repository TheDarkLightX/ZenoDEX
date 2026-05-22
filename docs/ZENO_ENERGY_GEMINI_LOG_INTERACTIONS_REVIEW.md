# UPBA v2 Energy Candidate Promotion Review

- Candidate: `gemini_log_interactions_seed20260517`
- Baseline: `upba_v2_gap_weighted_default_seed20260517`
- Decision: `hold_candidate`
- Promotion allowed: `False`
- Candidate model sha256: `sha256:eb7a3f4802e661b4f56ae4a94ec044fb099c11f066e0c68140ee950f3eeae535`

## Key Metrics

| lane | metric | baseline | candidate | delta |
| --- | --- | ---: | ---: | ---: |
| `holdout` | `top_1_recall` | `0.983358547655` | `0.987897125567` | `0.00453857791225` |
| `holdout` | `top_10_recall` | `1` | `1` | `0` |
| `holdout` | `mean_verifier_calls` | `1.01664145234` | `1.01260716087` | `-0.00403429147756` |
| `holdout` | `invalid_accept_count` | `0` | `0` | `` |
| `cross_seed` | `top_1_recall_mean` | `0.982491960612` | `0.983393578486` | `0.000901617873338` |
| `cross_seed` | `top_1_recall_min` | `0.967741935484` | `0.963709677419` | `-0.00403225806452` |
| `cross_seed` | `top_10_recall_min` | `1` | `1` | `0` |
| `cross_seed` | `mean_verifier_calls_mean` | `1.01750803939` | `1.01660642151` | `-0.000901617873338` |
| `cross_seed` | `mean_verifier_calls_max` | `1.03225806452` | `1.03629032258` | `0.00403225806452` |
| `cross_seed` | `invalid_accept_count_total` | `0` | `0` | `` |
| `cross_seed` | `permutation_violation_count_total` | `0` | `0` | `` |
| `hard_cases` | `top_1_recall` | `0.985445588894` | `0.980519480519` | `-0.00492610837438` |
| `hard_cases` | `top_5_recall` | `1` | `1` | `0` |
| `hard_cases` | `top_10_recall` | `1` | `1` | `0` |
| `hard_cases` | `top1_miss_count` | `65` | `87` | `22` |
| `hard_cases` | `top5_miss_count` | `0` | `0` | `` |
| `hard_cases` | `top10_miss_count` | `0` | `0` | `` |
| `hard_cases` | `mean_winner_position_mean` | `1.01701662749` | `1.01970664074` | `0.00269001325276` |
| `hard_cases` | `max_mean_winner_position` | `1.03232323232` | `1.03212851406` | `-0.000194718267007` |

## Obligations

- `pass` `holdout_beats_gap_weighted_mean_calls`
- `pass` `holdout_preserves_top10`
- `pass` `cross_seed_beats_mean_calls`
- `fail` `cross_seed_preserves_worst_top1`
- `fail` `hard_cases_preserve_top1`
- `pass` `safety_counts_clean`

Blocked reasons:
- `cross_seed_preserves_worst_top1`
- `hard_cases_preserve_top1`
