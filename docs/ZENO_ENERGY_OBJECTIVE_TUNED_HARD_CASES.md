# ZenoEnergy Hard-Case Mining Receipt

```text
batches_per_config: 500
seeds: 20260521, 20260522, 20260523
candidate_counts: 50, 75, 100
synthetic_batches_requested: 4500
synthetic_candidates_requested: 337500
model: data/upba_energy/upba_v2_energy_linear_objective_tuned_seed20260517.json
```

| metric | value |
| --- | ---: |
| batches_with_winner | 4466 |
| top_1_recall | 0.984 |
| top_5_recall | 1.000 |
| top_10_recall | 1.000 |
| mean_winner_position_mean | 1.021 |
| max_mean_winner_position | 1.038 |
| max_p99_winner_position | 2 |
| top1_miss_count | 70 |
| top5_miss_count | 1 |
| top10_miss_count | 0 |

## Top-1 Misses

`candidate_type` records generator provenance. The deterministic verifier result
is authoritative; a mutation-family label can still produce a valid candidate in
edge cases.

Top ranked candidate type on top-1 misses:

```text
valid: 69
invalid_balance: 1
```

Winner type on top-1 misses:

```text
valid: 70
```

Top ranked verifier error on top-1 misses:

```text
None: 70
```

Primary hand-energy failure on top-1 misses:

```text
imbalance: 70
```

Per-configuration examples are stored in the JSON receipt.
