# ZenoEnergy Neighborhood Repair Benchmark

```text
batches: 80
evaluated_batches: 80
candidates_per_batch: 24
candidate_budget: 6
repair_seed_count: 4
max_proposals_per_seed: 6
seed: 20260525
order_mode: hand
wall_clock_ms: 3741.973
```

| mode | batches | candidates | added | winner present | best is full winner | best dominates full winner | mean calls | mean volume regret | invalid accepts | subset violations |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 80 | 6.000 | 0.000 | 0.212 | 0.212 | 0.212 | 4.950 | 278.337 | 0 | 0 |
| neighborhood | 80 | 15.900 | 9.900 | 0.275 | 0.037 | 0.950 | 12.613 | 4.700 | 0 | 0 |

## Deltas

Positive winner-present and best-match deltas are better. Negative regret deltas are better.

```json
{
  "best_matches_full_winner_rate_delta": -0.175,
  "best_weakly_dominates_full_winner_rate_delta": 0.7374999999999999,
  "full_winner_present_rate_delta": 0.06250000000000003,
  "mean_calls_until_full_winner_or_exhausted_delta": 7.6625000000000005,
  "mean_volume_regret_delta": -273.6375
}
```

## Interpretation

Deterministic neighborhood proposals reduced best-valid volume regret and improved weak dominance over the full synthetic-list winner.

The neighborhood baseline increased verifier work in this benchmark.

Train or hand-design a repair selector that proposes fewer repairs while preserving most of the regret reduction.

## Safety Caveat

Neighborhood proposals expand a limited candidate set. They are not a bounded-grid optimality certificate unless paired with full fallback over an exact candidate family or a dominance-cover proof.
