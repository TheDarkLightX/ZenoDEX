# ZenoDEX AB Strict Zero-Min Observed Frontier n=7 Randomized

## Summary

A deterministic host checker validates observed child-frontier obligations for the committed n=7 strict zero-min randomized corpus.

Research-only observed-frontier evidence; no settlement, state-root, production, routing, matching, or governance authority.

## Metrics

- Deterministic seed: `2026062907`
- Cases checked: `4`
- Valid observed-frontier packets: `4`
- Children per packet: `5040`
- Total observed children: `20160`
- Packet mutations checked: `52`
- Mutation accepts: `0`
- Total canonical packet bytes replayed: `28151362`
- Max canonical packet bytes: `7104239`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reject reason classes: `['base_witness_packet_invalid', 'child_all_records_digest_mismatch', 'child_local_pruning_processed_reserve_in_mismatch', 'child_local_pruning_reserve_out_not_min', 'child_local_pruning_selected_not_record', 'child_missing_full_mask_coverage', 'observed_economic_key_mismatch', 'observed_empty_suffix_not_executable', 'observed_winner_not_in_children', 'observed_winner_not_selected_family_dominator']`

## First Packet Summary

```json
{
  "amounts": [
    100,
    101,
    102,
    103,
    104,
    105,
    106
  ],
  "authority_boundary": "research_only_no_settlement_or_state_authority",
  "bit_count": 7,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "children_count": 5040,
  "economic_keys": {
    "brute_force": [
      721,
      7
    ],
    "compressed": [
      721,
      7
    ],
    "full_subset_dp": [
      721,
      7
    ]
  },
  "first_child_digest": "27a615fe4f6a0edb236a73f5ebeb98528f2199b642160f1dd30b7e10e2274264",
  "full_mask": 127,
  "last_child_digest": "3c697b9620dcf4967687fc516ca416310bc1c00cfd9de1418236113f3710f568",
  "min_amount_out": [
    0,
    0,
    0,
    0,
    0,
    0,
    0
  ],
  "packet_canonical_bytes": 6991872,
  "packet_digest": "c1e94df2ababe37e8511d56a2923e54a506733c8f9544edbf2696a352e87bdf6",
  "packet_hash": "4f1336049b1ad344ca4563b584045a9ec4641f0ae2c050dab0f4a65dd6796d17",
  "pool": {
    "fee_bps": 9000,
    "reserve_in": 10000,
    "reserve_out": 1100
  },
  "scope": "n7_randomized_same_pool_same_direction_exact_in_zero_min_strict_executable_observed_frontier",
  "stress": {
    "case_count": 4,
    "pattern": "thin_positive_boundary/high_fee9000",
    "seed": 2026062907
  },
  "winner": {
    "order_ids": [
      "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c1",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c2",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c3",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c4",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c5",
      "0x00000000000000000000000000000000000000000000000000000000006cf5c6"
    ],
    "order_short": [
      "f5c0",
      "f5c1",
      "f5c2",
      "f5c3",
      "f5c4",
      "f5c5",
      "f5c6"
    ],
    "processed_reserve_in": 10721,
    "reserve_out": 1093
  }
}
```

## Case Summary

| case | ok | fee | children | packet bytes | key |
| --- | --- | ---: | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `9000` | `5040` | `6991872` | `[721, 7]` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `1` | `5040` | `7032729` | `[313, 2922]` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `100` | `5040` | `7022522` | `[411, 17320]` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `100` | `5040` | `7104239` | `[735, 652]` |

## Mutation Summary

| mutation | accepted count |
| --- | ---: |
| `authority_effect_present` | `0` |
| `bad_packet_hash` | `0` |
| `child_mask_missing_bit` | `0` |
| `child_processed_reserve_in_mismatch` | `0` |
| `child_selected_family_beats_winner` | `0` |
| `child_selected_not_local_min` | `0` |
| `child_selected_not_record` | `0` |
| `economic_key_mismatch` | `0` |
| `executed_input_mismatch` | `0` |
| `selected_no_longer_dominates` | `0` |
| `winner_empty_suffix` | `0` |
| `winner_missing_full_mask_bit` | `0` |
| `winner_removed_from_children` | `0` |

## Non-Claims

- This checker is bounded to the committed four-case n=7 randomized corpus.
- This checker does not prove generation of the full child frontier in Lean.
- This checker does not prove recursive subset-mask induction.
- This checker does not prove Lean-to-Python refinement.
- This checker does not define canonical tie order or preserve order-id history.
- Nonzero min_amount_out batches are outside this artifact.
- This checker does not cover n=8 observed-frontier packets.
- No settlement, state-root, production, routing, matching, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_observed_frontier_n7_randomized_20260629.py
```
