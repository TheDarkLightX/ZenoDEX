# ZenoEnergy Repair Selector Benchmark

```text
train_batches: 120
holdout_batches: 80
evaluated_batches: 80
candidates_per_batch: 24
candidate_budget: 6
proposal_budget: 2
repair_seed_count: 4
max_proposals_per_seed: 6
feature_dim: 34
parameter_count: 35
train_seed: 20260526
holdout_seed: 20260527
wall_clock_ms: 9763.1751
```

| mode | batches | candidates | added | full winner present | best dominates full winner | mean calls to dominance | mean calls to full winner | mean volume regret | invalid accepts | subset violations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 80 | 6.0000 | 0.0000 | 0.2250 | 0.2250 | 4.8750 | 4.8750 | 271.4750 | 0 | 0 |
| full_neighborhood | 80 | 16.2750 | 10.2750 | 0.2625 | 0.9625 | 1.6750 | 12.8750 | 3.2000 | 0 | 0 |
| hand_selected | 80 | 8.0000 | 2.0000 | 0.2625 | 0.9625 | 1.3500 | 6.5875 | 3.2000 | 0 | 0 |
| learned_selected | 80 | 8.0000 | 2.0000 | 0.2500 | 0.9625 | 1.3125 | 6.6500 | 3.2000 | 0 | 0 |

## Deltas

Negative candidate-count and call deltas are better. Negative regret deltas are better.

```json
{
  "learned_minus_full_neighborhood": {
    "best_weakly_dominates_full_winner_rate": 0.0,
    "candidate_count_mean": -8.274999999999999,
    "mean_added_count": -8.275,
    "mean_calls_until_dominating_candidate_or_exhausted": -0.36250000000000004,
    "mean_calls_until_full_winner_or_exhausted": -6.225,
    "mean_volume_regret": 0.0
  },
  "learned_minus_hand_selected": {
    "best_weakly_dominates_full_winner_rate": 0.0,
    "candidate_count_mean": 0.0,
    "mean_added_count": 0.0,
    "mean_calls_until_dominating_candidate_or_exhausted": -0.03750000000000009,
    "mean_calls_until_full_winner_or_exhausted": 0.0625,
    "mean_volume_regret": 0.0
  },
  "learned_minus_limited": {
    "best_weakly_dominates_full_winner_rate": 0.7375,
    "candidate_count_mean": 2.0,
    "mean_added_count": 2.0,
    "mean_calls_until_dominating_candidate_or_exhausted": -3.5625,
    "mean_calls_until_full_winner_or_exhausted": 1.7750000000000004,
    "mean_volume_regret": -268.27500000000003
  }
}
```

## Interpretation

The learned selector reduced proposal count while preserving most of the full-neighborhood regret reduction.

The learned selector did not beat the hand-selected proposal subset on mean volume regret.

Keep the selector as a bounded research candidate and test cross-seed before promotion.

Cross-seed receipt:
[ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md](./ZENO_ENERGY_REPAIR_SELECTOR_CROSS_SEED.md)

The three-seed stress run supported the compression claim on all three seed
pairs. Learned-selected mean candidate count was 8.000 versus 16.321 for full
neighborhood, with the same aggregate mean volume regret as full neighborhood.
The learned selector strictly beat the hand-selected subset on one of three seed
pairs and tied on the other two by mean volume regret.

## Safety Caveat

The selector is trained and evaluated on synthetic bounded candidates. It is a proposal filter only. Deterministic verifier fallback remains required for exactness.
