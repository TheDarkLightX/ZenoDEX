# ZenoEnergy Listwise Set Ranker

```text
train_batches: 120
train_rows: 2875
train_seed: 20260532
holdout_batches: 80
holdout_rows: 1916
holdout_seed: 20260533
candidates_per_batch: 24
loss: top_one_listwise_softmax
```

| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 76 | 0.026 | 0.197 | 0.447 | 12.632 | 23 | 24 | 0 |
| hand | 76 | 0.855 | 0.974 | 1.000 | 1.342 | 3 | 6 | 0 |
| aggregate_pairwise | 76 | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 1 | 0 |
| set_aware_pairwise | 76 | 0.987 | 1.000 | 1.000 | 1.026 | 1 | 1 | 0 |
| listwise_set | 76 | 0.947 | 1.000 | 1.000 | 1.066 | 1 | 2 | 0 |

## Deltas

Negative mean-call deltas are better.

```json
{
  "listwise_vs_aggregate_pairwise": {
    "mean_verifier_calls_delta": 0.03947368421052633,
    "p99_verifier_calls_delta": 1.0,
    "top_10_recall_delta": 0.0,
    "top_1_recall_delta": -0.03947368421052633,
    "top_5_recall_delta": 0.0
  },
  "listwise_vs_set_aware_pairwise": {
    "mean_verifier_calls_delta": 0.03947368421052633,
    "p99_verifier_calls_delta": 1.0,
    "top_10_recall_delta": 0.0,
    "top_1_recall_delta": -0.03947368421052633,
    "top_5_recall_delta": 0.0
  }
}
```

## Interpretation

Best pairwise baseline: `aggregate_pairwise`.

Listwise improved over best pairwise: `false`.

Keep the aggregate gap-weighted baseline as the measured default and treat the current listwise context as unpromoted.

The first listwise set-context ranker did not improve mean verifier calls against the strongest pairwise baseline on this bounded synthetic split.

The model only changes candidate order. Deterministic verification, full fallback, and checked-stop certificate obligations remain unchanged.
