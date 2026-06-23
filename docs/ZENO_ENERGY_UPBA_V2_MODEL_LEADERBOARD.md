# UPBA v2 Energy Model Leaderboard

- Decision: `promote_v6_research_candidate`
- Promoted model: `gemini_mlp_v6_seed20260519`
- Compared models: `7`
- Full three-lane models: `6`

## Holdout

| model | mean calls | p99 calls | top-1 | top-10 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: |
| gemini_mlp_v6_seed20260519 | 1.00252143217 | 1 | 0.997478567827 | 1 | 0 |
| gemini_highwinner_seed20260517 | 1.00655572365 | 1 | 0.993444276349 | 1 | 0 |
| gemini_objective8_seed20260517 | 1.01059001513 | 1 | 0.989914271306 | 1 | 0 |
| gemini_log_interactions_seed20260517 | 1.01260716087 | 2 | 0.987897125567 | 1 | 0 |
| upba_v2_gap_weighted_default_seed20260517 | 1.01664145234 | 2 | 0.983358547655 | 1 | 0 |
| gemini_handinit_seed20260517 | 1.01966717095 | 2 | 0.980332829047 | 1 | 0 |
| gemini_linear_v5_seed20260519 | 1.02168431669 | 2 | 0.978819969743 | 1 | 0 |

## Cross-Seed And Hard Cases

| model | cross mean calls | cross worst top-1 | hard top-1 | hard top-1 misses |
| --- | ---: | ---: | ---: | ---: |
| gemini_mlp_v6_seed20260519 | 1.00358605784 | 0.983870967742 | 0.99395567495 | 9 |
| gemini_highwinner_seed20260517 | 1.00762207622 | 0.983870967742 | 0.991940899933 | 12 |
| gemini_objective8_seed20260517 | 1.0103121206 | 0.983870967742 | 0.989926124916 | 15 |
| gemini_log_interactions_seed20260517 | 1.01300218008 | 0.975903614458 | 0.987239758227 | 19 |
| upba_v2_gap_weighted_default_seed20260517 | 1.01750803939 | 0.967741935484 | 0.985445588894 | 65 |
| gemini_linear_v5_seed20260519 | 1.02017074156 | 0.963709677419 | 0.983881799866 | 24 |

## Obligations

- `pass` `holdout_best_mean_calls`
- `pass` `holdout_best_top1`
- `pass` `cross_seed_best_mean_calls`
- `pass` `cross_seed_best_worst_top1`
- `pass` `hard_case_best_top1`
- `pass` `hard_case_fewest_top1_misses`
- `pass` `safety_counts_clean`

## Non-Claims

- The leaderboard compares advisory rankers only.
- It does not authorize settlement, replace deterministic verification, or establish production replay coverage.
- Holdout-only rows are not used for cross-seed or hard-case dominance claims.
