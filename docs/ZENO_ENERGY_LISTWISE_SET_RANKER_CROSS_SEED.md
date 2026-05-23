# ZenoEnergy Listwise Set Ranker Cross-Seed Stress

```text
run_count: 3
train_batches: 80
holdout_batches: 60
candidates_per_batch: 24
pairwise_epochs: 6
listwise_epochs: 10
wall_clock_ms: 28912.6697
```

| seeds | mode | top1 | top5 | top10 | mean calls | p99 | invalid accepts |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 20260532->20260533 | random | 0.0179 | 0.1964 | 0.4286 | 12.8750 | 24.0000 | 0 |
| 20260532->20260533 | hand | 0.8571 | 0.9821 | 1.0000 | 1.3393 | 5.0000 | 0 |
| 20260532->20260533 | aggregate_pairwise | 0.9821 | 1.0000 | 1.0000 | 1.0179 | 1.0000 | 0 |
| 20260532->20260533 | set_aware_pairwise | 0.9286 | 1.0000 | 1.0000 | 1.0714 | 2.0000 | 0 |
| 20260532->20260533 | listwise_set | 0.9464 | 1.0000 | 1.0000 | 1.0536 | 2.0000 | 0 |
| 20260534->20260535 | random | 0.0678 | 0.2373 | 0.4576 | 11.6271 | 23.0000 | 0 |
| 20260534->20260535 | hand | 0.7966 | 1.0000 | 1.0000 | 1.2712 | 3.0000 | 0 |
| 20260534->20260535 | aggregate_pairwise | 0.9831 | 1.0000 | 1.0000 | 1.0169 | 1.0000 | 0 |
| 20260534->20260535 | set_aware_pairwise | 0.9492 | 1.0000 | 1.0000 | 1.0508 | 2.0000 | 0 |
| 20260534->20260535 | listwise_set | 0.9492 | 1.0000 | 1.0000 | 1.0508 | 2.0000 | 0 |
| 20260536->20260537 | random | 0.0333 | 0.2000 | 0.3667 | 12.6167 | 22.0000 | 0 |
| 20260536->20260537 | hand | 0.8167 | 1.0000 | 1.0000 | 1.2500 | 3.0000 | 0 |
| 20260536->20260537 | aggregate_pairwise | 0.9833 | 1.0000 | 1.0000 | 1.0167 | 1.0000 | 0 |
| 20260536->20260537 | set_aware_pairwise | 0.9000 | 1.0000 | 1.0000 | 1.1000 | 2.0000 | 0 |
| 20260536->20260537 | listwise_set | 0.9000 | 1.0000 | 1.0000 | 1.1000 | 2.0000 | 0 |

## Aggregate

```json
{
  "all_safety_passed": true,
  "checked_stop_at_winner_fail_count": 0,
  "checked_stop_at_winner_pass_count": 3,
  "listwise_top10_fail_count": 0,
  "listwise_top10_pass_count": 3,
  "modes": {
    "aggregate_pairwise": {
      "mean_verifier_calls": {
        "max": 1.0178571428571428,
        "mean": 1.0171576540220608,
        "min": 1.0166666666666666
      },
      "p99_verifier_calls": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      },
      "top_10_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      },
      "top_1_recall": {
        "max": 0.9833333333333333,
        "mean": 0.9828423459779392,
        "min": 0.9821428571428571
      },
      "top_5_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      }
    },
    "hand": {
      "mean_verifier_calls": {
        "max": 1.3392857142857142,
        "mean": 1.2868240516545602,
        "min": 1.25
      },
      "p99_verifier_calls": {
        "max": 5.0,
        "mean": 3.6666666666666665,
        "min": 3.0
      },
      "top_10_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      },
      "top_1_recall": {
        "max": 0.8571428571428571,
        "mean": 0.8234732311003498,
        "min": 0.7966101694915254
      },
      "top_5_recall": {
        "max": 1.0,
        "mean": 0.9940476190476191,
        "min": 0.9821428571428571
      }
    },
    "listwise_set": {
      "mean_verifier_calls": {
        "max": 1.1,
        "mean": 1.068139628732849,
        "min": 1.0508474576271187
      },
      "p99_verifier_calls": {
        "max": 2.0,
        "mean": 2.0,
        "min": 2.0
      },
      "top_10_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      },
      "top_1_recall": {
        "max": 0.9491525423728814,
        "mean": 0.9318603712671509,
        "min": 0.9
      },
      "top_5_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      }
    },
    "random": {
      "mean_verifier_calls": {
        "max": 12.875,
        "mean": 12.372928436911488,
        "min": 11.627118644067796
      },
      "p99_verifier_calls": {
        "max": 24.0,
        "mean": 23.0,
        "min": 22.0
      },
      "top_10_recall": {
        "max": 0.4576271186440678,
        "mean": 0.417621737960721,
        "min": 0.36666666666666664
      },
      "top_1_recall": {
        "max": 0.06779661016949153,
        "mean": 0.03966236211998924,
        "min": 0.017857142857142856
      },
      "top_5_recall": {
        "max": 0.23728813559322035,
        "mean": 0.21123890234059725,
        "min": 0.19642857142857142
      }
    },
    "set_aware_pairwise": {
      "mean_verifier_calls": {
        "max": 1.1,
        "mean": 1.07409200968523,
        "min": 1.0508474576271187
      },
      "p99_verifier_calls": {
        "max": 2.0,
        "mean": 2.0,
        "min": 2.0
      },
      "top_10_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      },
      "top_1_recall": {
        "max": 0.9491525423728814,
        "mean": 0.92590799031477,
        "min": 0.9
      },
      "top_5_recall": {
        "max": 1.0,
        "mean": 1.0,
        "min": 1.0
      }
    }
  },
  "strict_improvement_count": 0,
  "strict_improvement_fail_count": 3
}
```

## Interpretation

The listwise set ranker preserved top-10 recall and checked-stop-at-winner audits on every seed pair.

The listwise set ranker did not strictly improve over the best pairwise baseline on every seed pair.

All runs reported zero invalid accepts and zero permutation violations.
