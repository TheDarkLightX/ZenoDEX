# ZenoDEX AB Reserve-State Child-Frontier Witness Compression - 2026-06-29

## Executive Result

A bounded host checker supports a compressed child-frontier proof object for the n=7 strict zero-min reserve-state quotient: one predecessor witness covers each child quotient state.

Research-only certificate-compression evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Child masks checked: `508`
- Expected child states: `864`
- Witness rows: `864`
- Covered child states: `864`
- Missing witness count: `0`
- Extra witness count: `0`
- Invalid witness count: `0`
- Duplicate witness count: `0`
- Baseline predecessor transitions: `2777`
- Witness compression ratio: `3.21412`
- Transition checks saved: `1913`
- Witness digest: `d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3`
- Negative controls: `8`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked Frontier Equality Report

```json
{
  "available": true,
  "child_mask_count": 508,
  "child_state_count": 864,
  "extra_generated_state_count": 0,
  "frontier_rows_digest": "b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4",
  "generated_state_count": 864,
  "missing_child_state_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_generation_20260629/report.json",
  "schema": "zenodex.ab_reserve_state_child_frontier_generation_report.v1"
}
```

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reason classes: `['authority_effect_present', 'duplicate_witness_row', 'extra_child_state_witness', 'linked_frontier_extra_generated_state', 'linked_frontier_summary_mismatch', 'missing_child_state_witness', 'packet_hash_mismatch', 'packet_witness_summary_mismatch', 'witness_afterstep_mismatch', 'witness_child_state_not_in_child_frontier', 'witness_parent_state_not_in_parent_frontier', 'witness_step_bit_out_of_range']`

## First Case

```json
{
  "bit_count": 7,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "child_mask_count": 127,
  "covered_child_state_count": 127,
  "duplicate_witness_count": 0,
  "expected_child_state_count": 127,
  "extra_child_state_witness_count": 0,
  "fee_bps": 9000,
  "first_failure": null,
  "frontier_witness_compression_ratio": 3.527559,
  "invalid_witness_count": 0,
  "missing_child_state_witness_count": 0,
  "ok": true,
  "packet_hash": "6dcc34309c3e4e998f2893beaf6389165c610d2f25d3667a776987646a143747",
  "pattern": "thin_positive_boundary/high_fee9000",
  "predecessor_transition_count": 448,
  "reasons": [],
  "unique_child_witness_count": 127,
  "witness_count": 127,
  "witness_rows_digest": "50e7a607c536bb6f412b123bb273540fe96902b00f28a0f51d721f2c5cd248ce"
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `missing_child_state_witness` | `False` | `missing_child_state_witness` |
| `witness_parent_state_not_in_parent_frontier` | `False` | `witness_parent_state_not_in_parent_frontier` |
| `witness_child_state_not_in_child_frontier` | `False` | `witness_child_state_not_in_child_frontier` |
| `witness_step_bit_out_of_range` | `False` | `witness_step_bit_out_of_range` |
| `duplicate_witness_row` | `False` | `duplicate_witness_row` |
| `linked_frontier_extra_generated_state` | `False` | `linked_frontier_extra_generated_state` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | witnesses | predecessor transitions | ratio | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `127` | `448` | `3.527559` | `50e7a607c536bb6f412b123bb273540fe96902b00f28a0f51d721f2c5cd248ce` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `320` | `1004` | `3.1375` | `11e64226723ba7faaa9266eba37cbbbe93b13f2160650bdbffad32fe9758905a` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `290` | `877` | `3.024138` | `059a8d4c8307a3580c6c5231b702bfd03059cb1ba9c187ccee474f4b1d32409d` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `127` | `448` | `3.527559` | `3d8d97f2a7cf35d5d0eb251ee1634695f82ad9b96763ffe788f0511dfe682e24` |

## Non-Claims

- This witness checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- The no-extra generated-state fact is linked to the existing child-frontier equality report, not reproved by the one-witness object alone.
- This checker does not define canonical tie order or preserve order-id history.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_witness_compression_20260629.py
```
