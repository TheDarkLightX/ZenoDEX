# AutoTraderEnergy Hard Cross-Seed Receipt

profile: hard
run_count: 3
train_contexts: 2500
holdout_contexts: 1000
candidates_per_context: 16
epochs: 6
learning_rate: 0.001
init: hand

## Aggregate

learned_beats_hand_count: 3
learned_beats_random_count: 3
profile_nonvacuous_count: 3
safety_pass_count: 3
invalid_accept_count_total: 0

| mode | mean guard calls | top-1 recall | top-5 recall | invalid top-1 max |
| --- | ---: | ---: | ---: | ---: |
| random | 8.393 | 0.066 | 0.318 | 0.221 |
| hand | 4.312 | 0.217 | 0.694 | 0.000 |
| learned | 1.010 | 0.990 | 1.000 | 0.000 |

The learned scorer beat the hand-coded scorer on every evaluated seed pair.
The receipt remains synthetic evidence. Production-shadow observations are still required.
