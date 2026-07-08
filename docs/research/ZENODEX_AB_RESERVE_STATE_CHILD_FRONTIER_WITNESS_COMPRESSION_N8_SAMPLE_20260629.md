# ZenoDEX AB Reserve-State Child-Frontier Witness Compression n=8 Sample - 2026-06-29

## Executive Result

A bounded deterministic n=8 sample supports a compressed child-frontier proof-object shape: one predecessor witness covers each sampled child quotient state.

Research-only certificate-compression evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Evidence Summary

- Cases checked: `3`
- Valid cases: `3`
- Sampled child masks checked: `51`
- Expected sampled child states: `88`
- Witness rows: `88`
- Covered sampled child states: `88`
- Missing sampled witnesses: `0`
- Extra sampled witnesses: `0`
- Invalid witness count: `0`
- Duplicate witness count: `0`
- Baseline sampled predecessor transitions: `268`
- Witness compression ratio: `3.045455`
- Transition checks saved: `180`
- Witness digest: `4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd`
- Negative controls: `9`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked n=8 Frontier Equality Report

```json
{
  "available": true,
  "extra_generated_state_count": 0,
  "frontier_rows_digest": "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919",
  "generated_state_count": 88,
  "missing_child_state_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_n8_sample_20260629/report.json",
  "sampled_child_mask_count": 51,
  "sampled_child_state_count": 88,
  "schema": "zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1"
}
```

## Coverage

- `n` histogram: `{'8': 3}`
- Fee histogram: `{'2500': 1, '30': 1, '9000': 1}`
- Regime/pattern histogram: `{'n8_deep_low_fee/tie': 1, 'n8_deep_mid_fee/front_burst': 1, 'n8_thin_high_fee/stair': 1}`
- Reason classes: `['authority_effect_present', 'duplicate_witness_row', 'extra_sampled_child_state_witness', 'linked_frontier_extra_generated_state', 'linked_frontier_summary_mismatch', 'missing_sampled_child_state_witness', 'packet_hash_mismatch', 'packet_witness_summary_mismatch', 'sampled_n8_bound_missing', 'witness_afterstep_mismatch', 'witness_child_state_not_in_sampled_child_frontier', 'witness_parent_state_not_in_parent_frontier', 'witness_step_bit_out_of_range']`

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
  "bit_count": 8,
  "case_id": "n8_sample_000_thin_fee9000_stair",
  "covered_sampled_child_state_count": 17,
  "duplicate_witness_count": 0,
  "expected_sampled_child_state_count": 17,
  "extra_sampled_child_state_witness_count": 0,
  "fee_bps": 9000,
  "first_failure": null,
  "frontier_witness_compression_ratio": 2.823529,
  "invalid_witness_count": 0,
  "missing_sampled_child_state_witness_count": 0,
  "ok": true,
  "packet_hash": "c0c5b5d10dbfa0cb144493bc909688cf55a58f61ce53a7ddb7ae2b7aa716bcd8",
  "pattern": "n8_thin_high_fee/stair",
  "predecessor_transition_count": 48,
  "reasons": [],
  "sampled_child_mask_count": 17,
  "unique_child_witness_count": 17,
  "witness_count": 17,
  "witness_rows_digest": "01b7aa20267ddaa7ee1d95f5d43665fac7b425bb55d42897114235af183dba8c"
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `missing_sampled_child_state_witness` | `False` | `missing_sampled_child_state_witness` |
| `witness_parent_state_not_in_parent_frontier` | `False` | `witness_parent_state_not_in_parent_frontier` |
| `witness_child_state_not_in_sampled_child_frontier` | `False` | `witness_child_state_not_in_sampled_child_frontier` |
| `witness_step_bit_out_of_range` | `False` | `witness_step_bit_out_of_range` |
| `duplicate_witness_row` | `False` | `duplicate_witness_row` |
| `sampled_n8_bound_missing` | `False` | `sampled_n8_bound_missing` |
| `linked_frontier_extra_generated_state` | `False` | `linked_frontier_extra_generated_state` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | witnesses | predecessor transitions | ratio | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n8_sample_000_thin_fee9000_stair` | `True` | `17` | `48` | `2.823529` | `01b7aa20267ddaa7ee1d95f5d43665fac7b425bb55d42897114235af183dba8c` |
| `n8_sample_001_deep_fee30_tie` | `True` | `34` | `104` | `3.058824` | `86e46ec5497b34f1be427434f64d4ad48966cbc4e7fff8c6ab7d3f03fd3174c1` |
| `n8_sample_002_burst_fee2500` | `True` | `37` | `116` | `3.135135` | `7f7dcc7e2ca3ec335620b1a50eb57b2778b9dc3d25a6c7544820bc399a2f5e80` |

## Non-Claims

- This witness checker is bounded to the deterministic n=8 sample, not exhaustive n=8 coverage.
- This checker covers only sampled zero-min exact-in cases and sampled child masks.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- The no-extra generated-state fact is linked to the existing n=8 child-frontier sample report, not reproved by the one-witness object alone.
- This checker does not define canonical tie order or preserve order-id history.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629.py
```
