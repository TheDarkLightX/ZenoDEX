# ZenoEnergy Suffix-Bound Cross-Seed Stress

```text
batches_per_config: 60
seeds: 20260541, 20260542, 20260543
candidate_counts: 20, 32, 50
synthetic_batches_requested: 540
synthetic_candidates_requested: 18360
model: data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json
```

| mode | configs | mean calls | max mean calls | p95 max | p99 max | max calls | objective-equiv min | suffix-stop min | full fallbacks | invalid accepts |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| exhaustive | 9 | 2.3631 | 2.4833 | 5.0000 | 7.0000 | 7.0000 | 1.0000 | 1.0000 | 0 | 0 |
| hand | 9 | 1.3935 | 1.6102 | 4.0000 | 6.0000 | 6.0000 | 1.0000 | 1.0000 | 0 | 0 |
| hybrid | 9 | 1.0132 | 1.0517 | 1.0000 | 4.0000 | 4.0000 | 1.0000 | 1.0000 | 0 | 0 |
| learned | 9 | 1.0132 | 1.0517 | 1.0000 | 4.0000 | 4.0000 | 1.0000 | 1.0000 | 0 | 0 |
| random | 9 | 17.1010 | 27.8333 | 48.0000 | 50.0000 | 50.0000 | 1.0000 | 0.8833 | 16 | 0 |

## Negative Knowledge

- Cross-seed suffix-bound stress remains bounded synthetic evidence.
- A stable suffix-bound stress result still does not prove candidate-family coverage.
