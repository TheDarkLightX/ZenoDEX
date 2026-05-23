# ZenoEnergy Particle Search Probe

```text
batches: 100
evaluated_batches: 100
candidates_per_batch: 40
candidate_budget: 4
particle_count: 3
iterations: 2
max_proposals_per_particle: 4
score_mode: obligation
```

| mode | batches | candidates | winner present | best is full winner | best dominates full winner | mean calls | volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 100 | 4.0000 | 0.0800 | 0.0800 | 0.0800 | 3.7600 | 430.9000 | 0 |
| one_shot_neighborhood | 100 | 8.5600 | 0.1000 | 0.0100 | 0.8300 | 8.0900 | 33.7200 | 0 |
| particle_resample | 100 | 11.8500 | 0.1700 | 0.0100 | 0.8500 | 10.6700 | 24.6500 | 0 |

## Interpretation

particle_helped_quality: True
particle_helped_full_winner_match: False
particle_increased_verifier_work: True

Keep PEM-style particle search as a constructive candidate-generation branch.

Every generated candidate remains advisory and is checked by the deterministic verifier.
