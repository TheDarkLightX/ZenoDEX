# ZenoEnergy Set-Aware Comparison

```text
train_batches: 120
train_rows: 2400
train_seed: 20260523
holdout_batches: 80
holdout_rows: 1599
holdout_seed: 20260524
candidates_per_batch: 20
```

| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| random | 80 | 0.050 | 0.212 | 0.475 | 10.963 | 20 | 20 | 0 |
| hand | 80 | 0.812 | 1.000 | 1.000 | 1.250 | 2 | 4 | 0 |
| aggregate_learned | 80 | 0.963 | 1.000 | 1.000 | 1.038 | 1 | 2 | 0 |
| aggregate_hybrid | 80 | 0.963 | 1.000 | 1.000 | 1.038 | 1 | 2 | 0 |
| set_aware_learned | 80 | 0.950 | 1.000 | 1.000 | 1.062 | 1 | 2 | 0 |
| set_aware_hybrid | 80 | 0.950 | 1.000 | 1.000 | 1.062 | 1 | 2 | 0 |

## Deltas

Negative mean-call deltas are better.

```json
{
  "set_aware_hybrid_vs_aggregate_hybrid": {
    "mean_verifier_calls_delta": 0.02499999999999991,
    "p99_verifier_calls_delta": 0.0,
    "top_10_recall_delta": 0.0,
    "top_1_recall_delta": -0.012500000000000067,
    "top_5_recall_delta": 0.0
  },
  "set_aware_vs_aggregate_learned": {
    "mean_verifier_calls_delta": 0.02499999999999991,
    "p99_verifier_calls_delta": 0.0,
    "top_10_recall_delta": 0.0,
    "top_1_recall_delta": -0.012500000000000067,
    "top_5_recall_delta": 0.0
  }
}
```

## Interpretation

Preferred measured checkpoint: `aggregate_learned`.

Extra set-aware moment features did not improve the linear ranker on this comparison run. Keep the aggregate gap-weighted checkpoint as the measured default until cross-seed evidence supports a change.

This is bounded synthetic evidence. It is useful for scorer selection inside the verifier-backed research harness, and it does not certify production readiness or v2 bounded-grid optimality.
