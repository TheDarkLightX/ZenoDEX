# ZenoEnergy Benchmark Receipt

```text
batches: 200
candidates_per_batch: 20
seed: 20260518
top_k: 10
learned_model_present: True
wall_clock_ms: 19281.461
```

| mode | batches | top1 | top5 | top10 | stop_top_k | stop_at_winner | mean_calls | p95 | p99 | invalid_accepts | perm_violations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 198 | 0.000 | 0.000 | 0.000 | 1.000 | 1.000 | 19.995 | 20 | 20 | 0 | 0 |
| random | 198 | 0.040 | 0.237 | 0.480 | 0.480 | 1.000 | 10.621 | 20 | 20 | 0 | 0 |
| hand | 198 | 0.778 | 0.990 | 1.000 | 1.000 | 1.000 | 1.359 | 3 | 5 | 0 | 0 |
| learned | 198 | 0.960 | 1.000 | 1.000 | 1.000 | 1.000 | 1.040 | 1 | 2 | 0 | 0 |
| hybrid | 198 | 0.960 | 1.000 | 1.000 | 1.000 | 1.000 | 1.040 | 1 | 2 | 0 | 0 |

`perm_violations = 0` is the runtime evidence for the full-fallback permutation premise.
`stop_top_k` is an offline checked-stop audit after the suffix has also been verified.
