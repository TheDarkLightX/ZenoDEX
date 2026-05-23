# ZenoEnergy Compositional Energy Probe

```text
train_batches: 200
train_rows: 7998
train_seed: 20260564
holdout_batches: 100
holdout_rows: 3995
holdout_seed: 20260565
candidates_per_batch: 40
composition_rule: sum_local_energy_models
```

| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 100 | 0.0200 | 0.1200 | 0.2400 | 19.8000 | 37 | 39 | 0 |
| hand | 100 | 0.8100 | 0.9900 | 1.0000 | 1.3400 | 3 | 5 | 0 |
| aggregate_pairwise | 100 | 1.0000 | 1.0000 | 1.0000 | 1.0000 | 1 | 1 | 0 |
| set_aware_pairwise | 100 | 0.9400 | 1.0000 | 1.0000 | 1.0600 | 2 | 2 | 0 |
| obligation_formula_sum | 100 | 0.8500 | 1.0000 | 1.0000 | 1.2100 | 2 | 4 | 0 |
| obligation_formula_calibrated | 100 | 0.9800 | 1.0000 | 1.0000 | 1.0200 | 1 | 2 | 0 |
| compositional_sum | 100 | 0.5700 | 0.9700 | 1.0000 | 1.8500 | 4 | 6 | 0 |
| compositional_hybrid | 100 | 0.5900 | 0.9700 | 1.0000 | 1.7700 | 4 | 6 | 0 |
| local_target_sum | 100 | 0.7200 | 0.9400 | 0.9900 | 2.0900 | 6 | 9 | 0 |
| local_target_calibrated | 100 | 0.7200 | 0.9700 | 1.0000 | 1.6000 | 4 | 8 | 0 |
| local_target_hybrid | 100 | 0.7200 | 0.9800 | 1.0000 | 1.6400 | 4 | 6 | 0 |

## Interpretation

best_pairwise_baseline: `aggregate_pairwise`
best_compositional_mode: `obligation_formula_calibrated`
compositional_helped: False
invalid_accept_count_total: 0

Do not promote these compositional local-energy variants on this run; keep the best monolithic pairwise baseline as the measured checkpoint.

The tested local-energy decompositions did not reduce mean verifier calls against the strongest monolithic pairwise baseline on this bounded synthetic split.

This is bounded synthetic evidence for advisory search ordering only. The deterministic verifier remains authoritative.
