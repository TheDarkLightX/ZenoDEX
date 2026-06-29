# ZenoDEX AB Reserve-State Child-Frontier Canonical Merkle n=8 Sample - 2026-06-29

## Executive Result

A bounded deterministic n=8 sample supports canonical-index Merkle membership for sampled reserve-state child frontiers.

Research-only certificate-compression evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Evidence Summary

- Cases checked: `3`
- Valid cases: `3`
- Sampled child masks checked: `51`
- Frontier roots: `51`
- Sampled child states: `88`
- Membership proofs: `88`
- Missing frontier rows: `0`
- Extra frontier rows: `0`
- Invalid membership proofs: `0`
- Root mismatches: `0`
- Max leaf count: `7`
- Frontier roots digest: `53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4`
- Membership rows digest: `bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2`
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
- Reason classes: `['authority_effect_present', 'canonical_leaf_index_mismatch', 'frontier_generated_state_root_mismatch', 'linked_frontier_extra_generated_state', 'linked_frontier_summary_mismatch', 'membership_proof_hash_mismatch', 'missing_membership_proof', 'packet_hash_mismatch', 'packet_sample_plan_mismatch', 'sampled_n8_bound_missing']`

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
  "duplicate_frontier_row_count": 0,
  "expected_frontier_roots_digest": "6d0dd4f4f879d8691432670cadeb62c9ab48a1eb5408781e0257e80c7ee3a6b3",
  "expected_sampled_child_mask_count": 17,
  "expected_sampled_child_state_count": 17,
  "extra_frontier_row_count": 0,
  "extra_membership_proof_count": 0,
  "fee_bps": 9000,
  "first_failure": null,
  "frontier_root_count": 17,
  "frontier_roots_digest": "6d0dd4f4f879d8691432670cadeb62c9ab48a1eb5408781e0257e80c7ee3a6b3",
  "invalid_membership_proof_count": 0,
  "max_leaf_count": 1,
  "membership_count": 17,
  "membership_rows_digest": "b7ff3e35887fa45919fb1808dbdf6ebb0f08cf4dc6f617da70375d87df64a184",
  "missing_frontier_row_count": 0,
  "missing_membership_proof_count": 0,
  "ok": true,
  "packet_hash": "959b293a66be8eeda887cf5e526036297b39d977ec070a9e5c75476dd419edfa",
  "pattern": "n8_thin_high_fee/stair",
  "reasons": [],
  "root_mismatch_count": 0,
  "sampled_child_mask_count": 17,
  "sampled_child_state_count": 17
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `sampled_n8_bound_missing` | `False` | `sampled_n8_bound_missing` |
| `packet_sample_plan_mismatch` | `False` | `packet_sample_plan_mismatch` |
| `frontier_generated_state_root_mismatch` | `False` | `frontier_generated_state_root_mismatch` |
| `canonical_leaf_index_mismatch` | `False` | `canonical_leaf_index_mismatch` |
| `missing_membership_proof` | `False` | `missing_membership_proof` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `linked_frontier_extra_generated_state` | `False` | `linked_frontier_extra_generated_state` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | roots | memberships | max leaves | membership digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n8_sample_000_thin_fee9000_stair` | `True` | `17` | `17` | `1` | `b7ff3e35887fa45919fb1808dbdf6ebb0f08cf4dc6f617da70375d87df64a184` |
| `n8_sample_001_deep_fee30_tie` | `True` | `17` | `34` | `6` | `807bbd43f61d88ad5908082696811351e15fae299d3881119dcad3a70d3060fd` |
| `n8_sample_002_burst_fee2500` | `True` | `17` | `37` | `7` | `0684e5b00deeeef7835d29e5dbcc051da86cb3d43984b4cd9b54d1f170db6489` |

## Non-Claims

- This canonical Merkle checker is bounded to the deterministic n=8 sample, not exhaustive n=8 coverage.
- This checker covers only sampled zero-min exact-in cases and sampled child masks.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not define canonical tie order beyond reserve-state leaf ordering.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629.py
```
