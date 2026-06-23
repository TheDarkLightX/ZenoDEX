# ZenoEnergy Synthetic Candidate Coverage

```text
coverage_ok: true
seed: 20260540
batches: 100
candidate_count_total: 3196
winner_batch_rate: 0.9700
hard_negative_rate: 0.1248
synthetic_only: true
duplicate_hash_batches: 0
```

## Candidate Types

| type | count |
| --- | ---: |
| hard_attractive_output_mismatch | 100 |
| hard_schema_policy_mismatch | 100 |
| hard_unreduced_price | 100 |
| invalid_all_zero | 100 |
| invalid_balance | 97 |
| invalid_limit_price | 100 |
| invalid_negative_reserve | 100 |
| invalid_noncanonical_fill_vector | 100 |
| near_miss_adversarial | 99 |
| random_noisy | 1850 |
| valid | 447 |
| valid_seed | 3 |

## Verifier Errors

| error | count |
| --- | ---: |
| certificate fill exceeds intent amount_in | 1295 |
| certificate fill net input is zero | 21 |
| certificate fill output does not match uniform price | 395 |
| certificate fill violates intent limit price | 3 |
| certificate fills must be sorted by intent_id | 100 |
| certificate price does not match canonical UPBA objective | 512 |
| certificate price ratio must be reduced | 223 |
| uniform batch certificate schema does not match policy_id | 100 |
| uniform batch v2 requires at least one positive fill | 100 |

## Interpretation

Rows are generated from fixed seeded synthetic pools, intents, balances, and candidate mutations; this is distributional coverage evidence, not live-order evidence.

A production-shadow audit should rerun the same coverage checks on real candidate distributions after removing user identifiers and secrets.
