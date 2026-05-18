# ZenoEnergy Benchmark Receipt

```text
batches: 200
candidates_per_batch: 24
seed: 20260518
top_k: 10
learned_model_present: True
wall_clock_ms: 23552.485
```

| mode | batches | top1 | obj_top1 | top10 | stop_top_k | stop_at_winner | mean_calls | obj_calls | p99 | invalid_accepts | perm_violations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 200 | 0.000 | 0.140 | 0.000 | 1.000 | 1.000 | 23.990 | 2.375 | 24 | 0 | 0 |
| random | 200 | 0.025 | 0.025 | 0.425 | 0.425 | 1.000 | 12.495 | 12.495 | 24 | 0 | 0 |
| hand | 200 | 0.770 | 0.770 | 1.000 | 1.000 | 1.000 | 1.375 | 1.375 | 5 | 0 | 0 |
| learned | 200 | 0.995 | 0.995 | 1.000 | 1.000 | 1.000 | 1.010 | 1.010 | 1 | 0 | 0 |
| hybrid | 200 | 0.995 | 0.995 | 1.000 | 1.000 | 1.000 | 1.010 | 1.010 | 1 | 0 | 0 |

`perm_violations = 0` is the runtime evidence for the full-fallback permutation premise.
`stop_top_k` is an offline checked-stop audit after the suffix has also been verified.
`obj_top1` and `obj_calls` treat tied valid volume/surplus maxima as one objective class.
