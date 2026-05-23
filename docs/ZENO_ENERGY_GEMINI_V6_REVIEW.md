# UPBA v2 Energy Candidate Promotion Review

- Candidate: `gemini_mlp_v6_seed20260519`
- Baseline: `gemini_highwinner_seed20260517`
- Decision: `promote_candidate`
- Promotion allowed: `True`
- Scope: `advisory_ranking_only`
- Candidate model sha256: `sha256:859035159df61ecd7eab548e628b971840bdc96995b41547176e4a8cf205cb64`

The candidate passes the configured advisory-ranking promotion obligations against `gemini_highwinner_seed20260517`.

## Safety Contract

- `deterministic_verifier_authoritative`: `True`
- `model_authorizes_settlement`: `False`
- `model_output_in_state_root`: `False`
- `deterministic_fallback_required`: `True`

## Evidence Sources

- `baseline_cross_seed`: `data/upba_energy/upba_v2_energy_gemini_highwinner_cross_seed_250x3x3.json`
- `baseline_hard_cases`: `data/upba_energy/upba_v2_energy_gemini_highwinner_hard_cases_500x3x3.json`
- `candidate_cross_seed`: `data/upba_energy/upba_v2_energy_gemini_v6_cross_seed_250x3x3.json`
- `candidate_hard_cases`: `data/upba_energy/upba_v2_energy_gemini_v6_hard_cases_500x3x3.json`
- `candidate_model`: `internal/Gemini/gemini_mlp_v6_final.json`
- `holdout_compare`: `data/upba_energy/upba_v2_energy_gemini_v6_vs_highwinner_holdout_compare.json`

## Key Metrics

| lane | metric | baseline | candidate | delta |
| --- | --- | ---: | ---: | ---: |
| `holdout` | `top_1_recall` | `0.993444276349` | `0.997478567827` | `0.00403429147756` |
| `holdout` | `top_10_recall` | `1` | `1` | `0` |
| `holdout` | `mean_verifier_calls` | `1.00655572365` | `1.00252143217` | `-0.00403429147756` |
| `holdout` | `invalid_accept_count` | `0` | `0` | `n/a` |
| `cross_seed` | `top_1_recall_mean` | `0.992377923781` | `0.996413942159` | `0.0040360183782` |
| `cross_seed` | `top_1_recall_min` | `0.983870967742` | `0.983870967742` | `0` |
| `cross_seed` | `top_10_recall_min` | `1` | `1` | `0` |
| `cross_seed` | `mean_verifier_calls_mean` | `1.00762207622` | `1.00358605784` | `-0.0040360183782` |
| `cross_seed` | `mean_verifier_calls_max` | `1.01612903226` | `1.01612903226` | `0` |
| `cross_seed` | `invalid_accept_count_total` | `0` | `0` | `n/a` |
| `cross_seed` | `permutation_violation_count_total` | `0` | `0` | `n/a` |
| `hard_cases` | `top_1_recall` | `0.991940899933` | `0.99395567495` | `0.00201477501679` |
| `hard_cases` | `top_5_recall` | `1` | `1` | `0` |
| `hard_cases` | `top_10_recall` | `1` | `1` | `0` |
| `hard_cases` | `top1_miss_count` | `12` | `9` | `-3` |
| `hard_cases` | `top5_miss_count` | `0` | `0` | `n/a` |
| `hard_cases` | `top10_miss_count` | `0` | `0` | `n/a` |
| `hard_cases` | `mean_winner_position_mean` | `1.00872849495` | `1.00603894889` | `-0.00268954606304` |
| `hard_cases` | `max_mean_winner_position` | `1.01004016064` | `1.00806451613` | `-0.00197564451354` |

## Obligations

- `pass` `holdout_beats_baseline_mean_calls`
- `pass` `holdout_preserves_top10`
- `pass` `cross_seed_beats_mean_calls`
- `pass` `cross_seed_preserves_worst_top1`
- `pass` `hard_cases_preserve_top1`
- `pass` `safety_counts_clean`
