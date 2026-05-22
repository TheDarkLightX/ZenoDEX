# ZenoEnergy Compositional Energy Probe

```text
train_batches: 200
train_rows: 4798
train_seed: 20260560
holdout_batches: 100
holdout_rows: 2396
holdout_seed: 20260561
candidates_per_batch: 24
composition_rule: sum_local_energy_models
```

| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 97 | 0.0722 | 0.2268 | 0.4021 | 12.5670 | 23 | 24 | 0 |
| hand | 97 | 0.8247 | 0.9897 | 1.0000 | 1.2784 | 3 | 3 | 0 |
| aggregate_pairwise | 97 | 0.9588 | 1.0000 | 1.0000 | 1.0412 | 1 | 2 | 0 |
| set_aware_pairwise | 97 | 0.9588 | 1.0000 | 1.0000 | 1.0412 | 1 | 2 | 0 |
| obligation_formula_sum | 97 | 0.9381 | 1.0000 | 1.0000 | 1.0722 | 2 | 2 | 0 |
| obligation_formula_calibrated | 97 | 0.9588 | 1.0000 | 1.0000 | 1.0412 | 1 | 2 | 0 |
| compositional_sum | 97 | 0.8454 | 0.9897 | 1.0000 | 1.2268 | 2 | 4 | 0 |
| compositional_hybrid | 97 | 0.8454 | 0.9897 | 1.0000 | 1.2062 | 2 | 3 | 0 |
| local_target_sum | 97 | 0.8144 | 0.9381 | 1.0000 | 1.5361 | 6 | 7 | 0 |
| local_target_calibrated | 97 | 0.8454 | 0.9897 | 1.0000 | 1.3093 | 3 | 5 | 0 |
| local_target_hybrid | 97 | 0.8144 | 0.9897 | 1.0000 | 1.3608 | 3 | 4 | 0 |

## Interpretation

best_pairwise_baseline: `aggregate_pairwise`
best_compositional_mode: `obligation_formula_calibrated`
compositional_helped: False
invalid_accept_count_total: 0

Do not promote these compositional local-energy variants on this run; keep the best monolithic pairwise baseline as the measured checkpoint.

The tested local-energy decompositions did not reduce mean verifier calls against the strongest monolithic pairwise baseline on this bounded synthetic split.

This is bounded synthetic evidence for advisory search ordering only. The deterministic verifier remains authoritative.
