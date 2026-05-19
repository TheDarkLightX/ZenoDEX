# ZenoEnergy Synthetic Data Scaling

schema: `zenodex/energy/upba_v2_data_scaling_report/v1`
train_rows_available: 199860
holdout_rows: 39979
epochs: 4

| train batches | train rows | top-1 | top-10 | mean calls | p95 | p99 | invalid accepts |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 50 | 999 | 0.9390 | 1.0000 | 1.0736 | 2 | 2 | 0 |
| 100 | 1999 | 0.9370 | 1.0000 | 1.0731 | 2 | 2 | 0 |
| 250 | 4996 | 0.9576 | 1.0000 | 1.0524 | 1 | 2 | 0 |
| 500 | 9996 | 0.9677 | 1.0000 | 1.0424 | 1 | 2 | 0 |
| 1000 | 19990 | 0.9768 | 1.0000 | 1.0308 | 1 | 2 | 0 |
| 2500 | 49969 | 0.9808 | 1.0000 | 1.0242 | 1 | 2 | 0 |
| 5000 | 99940 | 0.9808 | 1.0000 | 1.0202 | 1 | 2 | 0 |
| 10000 | 199860 | 0.9823 | 1.0000 | 1.0177 | 1 | 2 | 0 |

## Current Gap-Weighted Baseline

top_1_recall: 0.9834
top_10_recall: 1.0000
mean_verifier_calls: 1.0166
p99_verifier_calls: 2

## Interpretation

Extra i.i.d. synthetic examples help only if the added batches expose new ranking errors or rare verifier-shaped families; raw volume alone is not a correctness or production-readiness certificate.

More synthetic examples are useful when they add coverage over rare verifier
failure families or live-like candidate distributions. Repeating the same
bounded generator eventually saturates the tiny linear ranker.
