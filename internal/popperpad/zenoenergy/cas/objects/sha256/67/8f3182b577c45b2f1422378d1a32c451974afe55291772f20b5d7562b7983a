# ZenoEnergy Repair Selector Cross-Seed Stress

```text
run_count: 3
train_batches: 80
holdout_batches: 60
candidates_per_batch: 24
candidate_budget: 6
proposal_budget: 2
repair_seed_count: 4
max_proposals_per_seed: 6
epochs: 8
wall_clock_ms: 24699.3800
```

| seeds | mode | candidates | added | best dominates full winner | calls to dominance | calls to full winner | volume regret | invalid accepts | subset violations |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20260526->20260527 | limited | 6.0000 | 0.0000 | 0.2167 | 4.9167 | 4.9167 | 279.8000 | 0 | 0 |
| 20260526->20260527 | full_neighborhood | 16.3333 | 10.3333 | 0.9500 | 1.8333 | 12.8833 | 4.2667 | 0 | 0 |
| 20260526->20260527 | hand_selected | 8.0000 | 2.0000 | 0.9500 | 1.4000 | 6.5500 | 4.2667 | 0 | 0 |
| 20260526->20260527 | learned_selected | 8.0000 | 2.0000 | 0.9500 | 1.3833 | 6.6333 | 4.2667 | 0 | 0 |
| 20260528->20260529 | limited | 6.0000 | 0.0000 | 0.2931 | 4.5517 | 4.5517 | 315.2586 | 0 | 0 |
| 20260528->20260529 | full_neighborhood | 16.1724 | 10.1724 | 0.9310 | 2.1724 | 11.7241 | 12.1034 | 0 | 0 |
| 20260528->20260529 | hand_selected | 8.0000 | 2.0000 | 0.9310 | 1.6034 | 6.2931 | 12.1034 | 0 | 0 |
| 20260528->20260529 | learned_selected | 8.0000 | 2.0000 | 0.9310 | 1.5517 | 6.2414 | 12.1034 | 0 | 0 |
| 20260530->20260531 | limited | 6.0000 | 0.0000 | 0.2542 | 4.7458 | 4.7458 | 261.1864 | 0 | 0 |
| 20260530->20260531 | full_neighborhood | 16.4576 | 10.4576 | 0.9492 | 1.9661 | 12.1525 | 1.4407 | 0 | 0 |
| 20260530->20260531 | hand_selected | 8.0000 | 2.0000 | 0.9492 | 1.4407 | 6.4068 | 2.3729 | 0 | 0 |
| 20260530->20260531 | learned_selected | 8.0000 | 2.0000 | 0.9492 | 1.3898 | 6.3559 | 1.4407 | 0 | 0 |

## Aggregate

```json
{
  "all_safety_passed": true,
  "compression_fail_count": 0,
  "compression_pass_count": 3,
  "modes": {
    "full_neighborhood": {
      "best_weakly_dominates_full_winner_rate": {
        "max": 0.95,
        "mean": 0.943395675043834,
        "min": 0.9310344827586207
      },
      "candidate_count_mean": {
        "max": 16.45762711864407,
        "mean": 16.321124748360283,
        "min": 16.17241379310345
      },
      "mean_added_count": {
        "max": 10.457627118644067,
        "mean": 10.321124748360283,
        "min": 10.172413793103448
      },
      "mean_calls_until_dominating_candidate_or_exhausted": {
        "max": 2.1724137931034484,
        "mean": 1.990616273784012,
        "min": 1.8333333333333333
      },
      "mean_calls_until_full_winner_or_exhausted": {
        "max": 12.883333333333333,
        "mean": 12.253337879083057,
        "min": 11.724137931034482
      },
      "mean_volume_regret": {
        "max": 12.10344827586207,
        "mean": 5.936930969543477,
        "min": 1.4406779661016949
      }
    },
    "hand_selected": {
      "best_weakly_dominates_full_winner_rate": {
        "max": 0.95,
        "mean": 0.943395675043834,
        "min": 0.9310344827586207
      },
      "candidate_count_mean": {
        "max": 8.0,
        "mean": 8.0,
        "min": 8.0
      },
      "mean_added_count": {
        "max": 2.0,
        "mean": 2.0,
        "min": 2.0
      },
      "mean_calls_until_dominating_candidate_or_exhausted": {
        "max": 1.603448275862069,
        "mean": 1.4813754139879212,
        "min": 1.4
      },
      "mean_calls_until_full_winner_or_exhausted": {
        "max": 6.55,
        "mean": 6.416627703097603,
        "min": 6.293103448275862
      },
      "mean_volume_regret": {
        "max": 12.10344827586207,
        "mean": 6.247665432820313,
        "min": 2.3728813559322033
      }
    },
    "learned_selected": {
      "best_weakly_dominates_full_winner_rate": {
        "max": 0.95,
        "mean": 0.943395675043834,
        "min": 0.9310344827586207
      },
      "candidate_count_mean": {
        "max": 8.0,
        "mean": 8.0,
        "min": 8.0
      },
      "mean_added_count": {
        "max": 2.0,
        "mean": 2.0,
        "min": 2.0
      },
      "mean_calls_until_dominating_candidate_or_exhausted": {
        "max": 1.5517241379310345,
        "mean": 1.441629326579648,
        "min": 1.3833333333333333
      },
      "mean_calls_until_full_winner_or_exhausted": {
        "max": 6.633333333333334,
        "mean": 6.410214949022664,
        "min": 6.241379310344827
      },
      "mean_volume_regret": {
        "max": 12.10344827586207,
        "mean": 5.936930969543477,
        "min": 1.4406779661016949
      }
    },
    "limited": {
      "best_weakly_dominates_full_winner_rate": {
        "max": 0.29310344827586204,
        "mean": 0.254669134359374,
        "min": 0.21666666666666667
      },
      "candidate_count_mean": {
        "max": 6.0,
        "mean": 6.0,
        "min": 6.0
      },
      "mean_added_count": {
        "max": 0.0,
        "mean": 0.0,
        "min": 0.0
      },
      "mean_calls_until_dominating_candidate_or_exhausted": {
        "max": 4.916666666666667,
        "mean": 4.738051172154036,
        "min": 4.551724137931035
      },
      "mean_calls_until_full_winner_or_exhausted": {
        "max": 4.916666666666667,
        "mean": 4.738051172154036,
        "min": 4.551724137931035
      },
      "mean_volume_regret": {
        "max": 315.2586206896552,
        "mean": 285.4150204558738,
        "min": 261.1864406779661
      }
    }
  },
  "strict_hand_win_count": 1,
  "strict_hand_win_fail_count": 2
}
```

## Interpretation

The learned selector compressed full neighborhood expansion on every seed pair while preserving regret and weak-dominance metrics.

The learned selector did not strictly beat the hand-selected subset on every seed pair.

All runs reported zero invalid accepts and zero original-subset violations.
