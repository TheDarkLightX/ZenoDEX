# ZenoEnergy Negative-Curriculum Ranker

```text
train_rows: 19981
train_rows_available: 199860
max_train_batches: 1000
holdout_rows: 39979
baseline_model: data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json
curriculum_model: data/upba_energy/upba_v2_energy_linear_curriculum_seed20260517.json
promotion_decision: keep_default
```

## Holdout

| mode | top1 | top5 | top10 | mean_calls | p99 | invalid_accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| hand | 0.763 | 0.996 | 1.000 | 1.362 | 4 | 0 |
| baseline | 0.983 | 1.000 | 1.000 | 1.017 | 2 | 0 |
| curriculum | 0.978 | 0.999 | 1.000 | 1.032 | 2 | 0 |

## Cross-Seed Stress

| mode | configs | top1_mean | top5_min | top10_min | mean_calls | p99_max | invalid_accepts | perm_violations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline_learned | 9 | 0.989 | 1.000 | 1.000 | 1.011 | 2 | 0 | 0 |
| curriculum_learned | 9 | 0.980 | 1.000 | 1.000 | 1.025 | 4 | 0 | 0 |
| baseline_hybrid | 9 | 0.989 | 1.000 | 1.000 | 1.011 | 2 | 0 | 0 |
| curriculum_hybrid | 9 | 0.980 | 1.000 | 1.000 | 1.025 | 4 | 0 | 0 |

The rare-disqualifier curriculum did not beat the gap-weighted default on cross-seed learned mean verifier calls.
