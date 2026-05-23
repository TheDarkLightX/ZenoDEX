# ZenoEnergy Particle Search Probe

```text
batches: 100
evaluated_batches: 98
candidates_per_batch: 40
candidate_budget: 4
particle_count: 4
iterations: 3
max_proposals_per_particle: 6
score_mode: hand
```

| mode | batches | candidates | winner present | best is full winner | best dominates full winner | mean calls | volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 98 | 4.0000 | 0.1020 | 0.1020 | 0.1020 | 3.6939 | 429.6224 | 0 |
| one_shot_neighborhood | 98 | 15.5612 | 0.1224 | 0.0102 | 0.8776 | 14.3265 | 18.3469 | 0 |
| particle_resample | 98 | 26.0612 | 0.1939 | 0.0102 | 0.9388 | 23.3265 | 12.3061 | 0 |

## Interpretation

particle_helped_quality: True
particle_helped_full_winner_match: False
particle_increased_verifier_work: True

Keep PEM-style particle search as a constructive candidate-generation branch.

Every generated candidate remains advisory and is checked by the deterministic verifier.
