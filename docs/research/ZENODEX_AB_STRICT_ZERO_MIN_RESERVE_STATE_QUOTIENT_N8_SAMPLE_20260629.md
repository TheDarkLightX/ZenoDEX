# ZenoDEX AB Strict Zero-Min Reserve-State Quotient n=8 Sample

## Summary

A deterministic n=8 sample extends the reserve-state quotient replay beyond the n=7 certificate by generating full reachable records for all masks and checking sampled suffix obligations.

Research-only quotient replay evidence; no settlement, state-root, production, routing, matching, or governance authority.

## Metrics

- Cases checked: `3`
- Valid cases: `3`
- Full records across all masks: `328803`
- Quotient states across all masks: `1683`
- All-mask record compression ratio: `195.367201`
- Sampled masks: `54`
- Sampled suffix obligations: `1227`
- Lean observed-summary rows: `1227`
- Sampled suffix universe: `242499`
- Quotient dominance checks: `1862`
- Dominance check compression ratio: `72.734694`
- Negative controls: `12`
- Negative control accepts: `0`
- Deterministic replay ok: `True`
- Lean observed-summary digest: `eab4ae228e9ff9fe78393f55d8ec0fce3435600f8555cedfe7908f780402bd9b`

## Lean Projection Shape

```json
{
  "host_table": "ReserveStateQuotientHostTable",
  "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
  "projection_shape": "one_digest_row_per_sampled_mask_sampled_suffix",
  "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
  "summary_structure": "ReserveStateQuotientObservedSummary",
  "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid"
}
```

Each sampled digest row binds the observed summary fields used by
`reserveStateQuotientObservedSummary_validates`: quotient-state count, selected
reserve-in, selected reserve-out, completed gross input, initial output reserve,
selected-state digest, quotient-state digest, and one sampled completion suffix.

## Sample Plan

```json
{
  "bit_count": 8,
  "full_dp_generated_all_masks": true,
  "mask_ids": [
    0,
    1,
    2,
    4,
    8,
    15,
    16,
    32,
    51,
    60,
    64,
    85,
    128,
    170,
    195,
    204,
    240,
    255
  ],
  "seed": 2026062908,
  "suffix_sample_limit": 24,
  "suffix_sampling": "all suffixes up to limit; otherwise first, last, and deterministic random indexes"
}
```

## First Case

```json
{
  "amounts": [
    100,
    101,
    102,
    103,
    104,
    105,
    106,
    107
  ],
  "baseline_full_dominance_check_count": 45144,
  "bit_count": 8,
  "case_id": "n8_sample_000_thin_fee9000_stair",
  "dominance_check_compression_saved": 44735,
  "executed_input": 828,
  "fee_bps": 9000,
  "first_failure": null,
  "first_obligation": {
    "mask_id": 0,
    "quotient_digest": "def37c5bc34f6776c10da1a4ba66aef1c4a1031129bd81de8bae8909a73ed586",
    "quotient_state_count": 1,
    "selected_state": {
      "processed_reserve_in": 10000,
      "reserve_out": 1600
    },
    "suffix_short": [
      "f5c0",
      "f5c1",
      "f5c2",
      "f5c3",
      "f5c4",
      "f5c5",
      "f5c6",
      "f5c7"
    ]
  },
  "full_mask": 255,
  "full_mask_selected_state": {
    "processed_reserve_in": 10828,
    "reserve_out": 1592
  },
  "full_record_count_all": 109601,
  "initial_reserve_in": 10000,
  "initial_reserve_out": 1600,
  "lean_observed_summary": {
    "contract": {
      "host_table": "ReserveStateQuotientHostTable",
      "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
      "projection_shape": "one_digest_row_per_sampled_mask_sampled_suffix",
      "summary_endpoint": "reserveStateQuotientObservedSummary_validates",
      "summary_structure": "ReserveStateQuotientObservedSummary",
      "summary_valid_predicate": "reserveStateQuotientObservedSummaryValid"
    },
    "digest": "13f6ae624e4cf4d3086e69c3f4530f4733346f15fba22636e84787e764e4a95b",
    "first_row": {
      "lean_endpoint": "reserveStateQuotientObservedSummary_validates",
      "lean_structure": "ReserveStateQuotientObservedSummary",
      "mask_id": 0,
      "observed_executed_input": 828,
      "observed_initial_reserve_out": 1600,
      "observed_selected_reserve_in": 10000,
      "observed_selected_reserve_out": 1600,
      "observed_state_count": 1,
      "selected_state_digest": "04599cb8fbe86d40a4749171f9837cdde73cfa4f248b55f7a700c5f1207190b9",
      "suffix_order_ids": [
        "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c1",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c2",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c3",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c4",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c5",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c6",
        "0x00000000000000000000000000000000000000000000000000000000006cf5c7"
      ],
      "suffix_short": [
        "f5c0",
        "f5c1",
        "f5c2",
        "f5c3",
        "f5c4",
        "f5c5",
        "f5c6",
        "f5c7"
      ],
      "table_state_digest": "def37c5bc34f6776c10da1a4ba66aef1c4a1031129bd81de8bae8909a73ed586"
    },
    "row_count": 409
  },
  "mask_count_all": 256,
  "max_full_records_per_sampled_mask": 40320,
  "max_quotient_states_per_sampled_mask": 1,
  "max_suffix_sample_per_mask": 24,
  "max_suffix_universe_per_mask": 40320,
  "min_amount_out": [
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0
  ],
  "ok": true,
  "packet_hash": "a006ea563f0a9436fae7564684979af063e532544ea9be5a8bf8fe9c09744037",
  "pattern": "n8_thin_high_fee/stair",
  "pool": {
    "fee_bps": 9000,
    "reserve_in": 10000,
    "reserve_out": 1600
  },
  "quotient_dominance_check_count": 409,
  "quotient_obligation_digest": "9283ccebe07c0d905f41b56bd821eb068af5d013a5ae3bb21d810513131e8e3e",
  "quotient_runtime_completion_count": 409,
  "quotient_state_count_all": 256,
  "reasons": [],
  "sampled_full_record_count": 40521,
  "sampled_mask_count": 18,
  "sampled_quotient_state_count": 18,
  "sampled_record_compression_saved": 40503,
  "sampled_remaining_counts": [
    8,
    7,
    7,
    7,
    7,
    4,
    7,
    7,
    4,
    4,
    7,
    4,
    7,
    4,
    4,
    4,
    4,
    0
  ],
  "sampled_suffix_count": 409,
  "scope": "n8_same_pool_same_direction_exact_in_zero_min_strict_executable_reserve_state_quotient_sample",
  "selected_suffix_executable_count": 409,
  "stress": {
    "case_count": 3,
    "pattern": "n8_thin_high_fee/stair",
    "seed": 2026062908
  },
  "suffix_universe_count": 80833
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | --- | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `quotient_family_bound_missing` | `False` | `quotient_family_bound_missing` |
| `reserve_state_only_bound_missing` | `False` | `reserve_state_only_bound_missing` |
| `sampled_n8_bound_missing` | `False` | `sampled_n8_bound_missing` |
| `packet_sample_plan_mismatch` | `False` | `packet_sample_plan_mismatch` |
| `packet_lean_contract_mismatch` | `False` | `packet_lean_contract_mismatch` |
| `packet_lean_observed_summary_mismatch` | `False` | `packet_lean_observed_summary_mismatch` |
| `compressed_record_missing` | `False` | `compressed_record_missing` |
| `selected_state_not_in_quotient_family` | `False` | `selected_state_not_in_quotient_family` |
| `selected_reserve_out_not_min` | `False` | `selected_reserve_out_not_min` |
| `selected_suffix_not_executable` | `False` | `selected_suffix_not_executable` |

## Case Summary

| case | ok | all records | all quotient states | sampled suffixes | quotient checks |
| --- | --- | ---: | ---: | ---: | ---: |
| `n8_sample_000_thin_fee9000_stair` | `True` | `109601` | `256` | `409` | `409` |
| `n8_sample_001_deep_fee30_tie` | `True` | `109601` | `682` | `409` | `702` |
| `n8_sample_002_burst_fee2500` | `True` | `109601` | `745` | `409` | `751` |

## Non-Claims

- This is a bounded deterministic n=8 sample, not exhaustive n=8 coverage.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove JSON canonicalization or packet-hash computation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- This checker is restricted to strict executable same-pool, same-direction, exact-in, zero-min batches.
- This checker does not cover nonzero min_amount_out behavior.
- This checker has no settlement, state-root, production, routing, matching, or governance authority.

## Replay

```bash
python3 tools/check_ab_strict_zero_min_reserve_state_quotient_n8_sample_20260629.py
```
