# ZenoEnergy Hard-Case Mining Receipt

```text
batches_per_config: 1000
seeds: 20260521, 20260522, 20260523
candidate_counts: 50, 75, 100
synthetic_batches_requested: 9000
synthetic_candidates_requested: 675000
model: data/upba_energy/upba_v2_energy_linear_seed20260517.json
```

| metric | value |
| --- | ---: |
| batches_with_winner | 8920 |
| top_1_recall | 0.983 |
| top_5_recall | 0.999 |
| top_10_recall | 1.000 |
| mean_winner_position_mean | 1.028 |
| max_mean_winner_position | 1.045 |
| max_p99_winner_position | 2 |
| top1_miss_count | 150 |
| top5_miss_count | 12 |
| top10_miss_count | 0 |

## Top-1 Misses

`candidate_type` records generator provenance. The deterministic verifier result
is authoritative; a mutation-family label can still produce a valid candidate in
edge cases.

Top ranked candidate type on top-1 misses:

```text
valid: 148
invalid_balance: 2
```

Winner type on top-1 misses:

```text
valid: 150
```

Top ranked verifier error on top-1 misses:

```text
None: 150
```

Primary hand-energy failure on top-1 misses:

```text
imbalance: 149
dust: 1
```

Per-configuration examples are stored in the JSON receipt.
