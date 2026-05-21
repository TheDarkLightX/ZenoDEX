# UPBA v2 Energy Candidate Promotion Review

- Candidate: `gemini_highwinner_seed20260517`
- Baseline: `upba_v2_gap_weighted_default_seed20260517`
- Decision: `promote_candidate`
- Promotion allowed: `True`
- Scope: `advisory_ranking_only`
- Candidate model sha256: `sha256:8bb29ba3129fccfa763bec4f0582a10ddde05eb8c58b854dd645f299e2e4ac90`

The candidate passes the configured advisory-ranking promotion obligations against `upba_v2_gap_weighted_default_seed20260517`.

## Safety Contract

- `deterministic_verifier_authoritative`: `True`
- `model_authorizes_settlement`: `False`
- `model_output_in_state_root`: `False`
- `deterministic_fallback_required`: `True`

## Evidence Sources

- `baseline_cross_seed`: `data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json`
- `baseline_hard_cases`: `data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json`
- `candidate_cross_seed`: `data/upba_energy/upba_v2_energy_gemini_highwinner_cross_seed_250x3x3.json`
- `candidate_hard_cases`: `data/upba_energy/upba_v2_energy_gemini_highwinner_hard_cases_500x3x3.json`
- `candidate_model`: `data/upba_energy/upba_v2_energy_gemini_highwinner_seed20260517.json`
- `holdout_compare`: `data/upba_energy/upba_v2_energy_gemini_highwinner_holdout_compare.json`

## Key Metrics

| lane | metric | baseline | candidate | delta |
| --- | --- | ---: | ---: | ---: |
| `holdout` | `top_1_recall` | `0.983358547655` | `0.993444276349` | `0.0100857286939` |
| `holdout` | `top_10_recall` | `1` | `1` | `0` |
| `holdout` | `mean_verifier_calls` | `1.01664145234` | `1.00655572365` | `-0.0100857286939` |
| `holdout` | `invalid_accept_count` | `0` | `0` | `n/a` |
| `cross_seed` | `top_1_recall_mean` | `0.982491960612` | `0.992377923781` | `0.00988596316804` |
| `cross_seed` | `top_1_recall_min` | `0.967741935484` | `0.983870967742` | `0.0161290322581` |
| `cross_seed` | `top_10_recall_min` | `1` | `1` | `0` |
| `cross_seed` | `mean_verifier_calls_mean` | `1.01750803939` | `1.00762207622` | `-0.00988596316804` |
| `cross_seed` | `mean_verifier_calls_max` | `1.03225806452` | `1.01612903226` | `-0.0161290322581` |
| `cross_seed` | `invalid_accept_count_total` | `0` | `0` | `n/a` |
| `cross_seed` | `permutation_violation_count_total` | `0` | `0` | `n/a` |
| `hard_cases` | `top_1_recall` | `0.985445588894` | `0.991940899933` | `0.00649531103898` |
| `hard_cases` | `top_5_recall` | `1` | `1` | `0` |
| `hard_cases` | `top_10_recall` | `1` | `1` | `0` |
| `hard_cases` | `top1_miss_count` | `65` | `12` | `-53` |
| `hard_cases` | `top5_miss_count` | `0` | `0` | `n/a` |
| `hard_cases` | `top10_miss_count` | `0` | `0` | `n/a` |
| `hard_cases` | `mean_winner_position_mean` | `1.01701662749` | `1.00872849495` | `-0.00828813253543` |
| `hard_cases` | `max_mean_winner_position` | `1.03232323232` | `1.01004016064` | `-0.0222830716807` |

## Obligations

- `pass` `holdout_beats_baseline_mean_calls`
- `pass` `holdout_preserves_top10`
- `pass` `cross_seed_beats_mean_calls`
- `pass` `cross_seed_preserves_worst_top1`
- `pass` `hard_cases_preserve_top1`
- `pass` `safety_counts_clean`
