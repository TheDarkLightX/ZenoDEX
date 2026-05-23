# ZenoEnergy Particle Search Probe

```text
batches: 100
evaluated_batches: 100
candidates_per_batch: 40
candidate_budget: 4
particle_count: 4
iterations: 3
max_proposals_per_particle: 6
score_mode: obligation
```

| mode | batches | candidates | winner present | best is full winner | best dominates full winner | mean calls | volume regret | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| limited | 100 | 4.0000 | 0.0900 | 0.0900 | 0.0900 | 3.7300 | 466.7700 | 0 |
| one_shot_neighborhood | 100 | 15.6700 | 0.1200 | 0.0000 | 0.9200 | 14.5300 | 13.4500 | 0 |
| particle_resample | 100 | 26.6500 | 0.1900 | 0.0100 | 0.9600 | 24.1300 | 6.0800 | 0 |

## Interpretation

particle_helped_quality: True
particle_helped_full_winner_match: False
particle_increased_verifier_work: True

Keep PEM-style particle search as a constructive candidate-generation branch.

Every generated candidate remains advisory and is checked by the deterministic verifier.
