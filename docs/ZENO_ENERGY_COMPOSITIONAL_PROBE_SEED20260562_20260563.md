# ZenoEnergy Compositional Energy Probe

```text
train_batches: 200
train_rows: 4797
train_seed: 20260562
holdout_batches: 100
holdout_rows: 2400
holdout_seed: 20260563
candidates_per_batch: 24
composition_rule: sum_local_energy_models
```

| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 100 | 0.0500 | 0.2000 | 0.4400 | 12.8500 | 24 | 24 | 0 |
| hand | 100 | 0.7000 | 1.0000 | 1.0000 | 1.4000 | 3 | 4 | 0 |
| aggregate_pairwise | 100 | 0.9700 | 1.0000 | 1.0000 | 1.0300 | 1 | 2 | 0 |
| set_aware_pairwise | 100 | 0.9300 | 1.0000 | 1.0000 | 1.0700 | 2 | 2 | 0 |
| obligation_formula_sum | 100 | 0.8900 | 1.0000 | 1.0000 | 1.1200 | 2 | 2 | 0 |
| obligation_formula_calibrated | 100 | 0.9600 | 1.0000 | 1.0000 | 1.0400 | 1 | 2 | 0 |
| compositional_sum | 100 | 0.6800 | 1.0000 | 1.0000 | 1.4800 | 3 | 5 | 0 |
| compositional_hybrid | 100 | 0.6800 | 1.0000 | 1.0000 | 1.4400 | 3 | 4 | 0 |
| local_target_sum | 100 | 0.7300 | 0.9700 | 1.0000 | 1.5800 | 4 | 6 | 0 |
| local_target_calibrated | 100 | 0.7600 | 1.0000 | 1.0000 | 1.3300 | 3 | 4 | 0 |
| local_target_hybrid | 100 | 0.7300 | 0.9900 | 1.0000 | 1.4500 | 3 | 4 | 0 |

## Interpretation

best_pairwise_baseline: `aggregate_pairwise`
best_compositional_mode: `obligation_formula_calibrated`
compositional_helped: False
invalid_accept_count_total: 0

Do not promote these compositional local-energy variants on this run; keep the best monolithic pairwise baseline as the measured checkpoint.

The tested local-energy decompositions did not reduce mean verifier calls against the strongest monolithic pairwise baseline on this bounded synthetic split.

This is bounded synthetic evidence for advisory search ordering only. The deterministic verifier remains authoritative.
