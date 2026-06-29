# ZenoDEX AB Reserve-State Child-Frontier Bidirectional Transition N8 Sample - 2026-06-29

## Executive Result

A bounded sampled n=8 bidirectional transition certificate supports the AB reserve-state child-frontier equality on sampled zero-min masks: linked predecessor witnesses cover sampled child states, and every sampled predecessor afterStep image is a canonical Merkle member of the sampled child frontier.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Evidence Summary

- Cases checked: `3`
- Valid cases: `3`
- Sampled child masks checked: `51`
- Transition rows: `268`
- Expected transitions: `268`
- Covered transitions: `268`
- Unique transition rows: `268`
- Unique generated child states across masks: `88`
- Missing transitions: `0`
- Extra transitions: `0`
- Invalid transition rows: `0`
- Duplicate transition rows: `0`
- Linked child coverage witnesses: `88`
- Linked canonical memberships: `88`
- Transition-to-child-witness ratio: `3.045455`
- Transition rows digest: `0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09`
- Negative controls: `11`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked Witness Report

```json
{
  "available": true,
  "case_count": 3,
  "kind": "sampled_n8_predecessor_witnesses",
  "negative_control_accept_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_witness_compression_n8_sample_20260629/report.json",
  "predecessor_transition_count": 268,
  "sampled_child_mask_count": 51,
  "schema": "zenodex.ab_reserve_state_child_frontier_witness_compression_n8_sample_report.v1",
  "valid_case_count": 3,
  "witness_count": 88,
  "witness_rows_digest": "4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd"
}
```

## Linked Canonical Merkle Report

```json
{
  "available": true,
  "case_count": 3,
  "frontier_root_count": 51,
  "frontier_roots_digest": "53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4",
  "kind": "sampled_n8_canonical_merkle",
  "membership_count": 88,
  "membership_rows_digest": "bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2",
  "negative_control_accept_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_20260629/report.json",
  "sampled_child_mask_count": 51,
  "sampled_child_state_count": 88,
  "schema": "zenodex.ab_reserve_state_child_frontier_canonical_merkle_n8_sample_report.v1",
  "valid_case_count": 3
}
```

## Coverage

- `n` histogram: `{'8': 3}`
- Fee histogram: `{'2500': 1, '30': 1, '9000': 1}`
- Regime/pattern histogram: `{'n8_deep_low_fee/tie': 1, 'n8_deep_mid_fee/front_burst': 1, 'n8_thin_high_fee/stair': 1}`
- Reason classes: `['afterstep_generated_child_mismatch', 'authority_effect_present', 'extra_predecessor_transition_row', 'generated_child_not_in_sampled_child_frontier', 'generated_state_root_mismatch', 'linked_canonical_merkle_membership_count_mismatch', 'linked_canonical_merkle_summary_mismatch', 'linked_witness_count_mismatch', 'linked_witness_summary_mismatch', 'membership_proof_hash_mismatch', 'missing_predecessor_transition_row', 'packet_hash_mismatch', 'packet_transition_summary_mismatch', 'sampled_n8_bound_missing', 'transition_parent_state_not_in_parent_frontier', 'transition_step_bit_out_of_range']`

## First Case

```json
{
  "bit_count": 8,
  "case_id": "n8_sample_000_thin_fee9000_stair",
  "covered_transition_count": 48,
  "duplicate_transition_row_count": 0,
  "expected_transition_count": 48,
  "extra_transition_count": 0,
  "fee_bps": 9000,
  "first_failure": null,
  "invalid_transition_row_count": 0,
  "missing_transition_count": 0,
  "ok": true,
  "packet_hash": "9c2f826415d129b9147773c47603894d0f7d758e2e526909531de95430766d2a",
  "pattern": "n8_thin_high_fee/stair",
  "reasons": [],
  "sampled_child_mask_count": 17,
  "transition_row_count": 48,
  "transition_rows_digest": "2a63f35abcbc298e94cafc56ce6cdfdf3b5ae0ab19bb6160ee9aee79ab9608eb",
  "unique_generated_child_count": 17,
  "unique_transition_count": 48
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `sampled_n8_bound_missing` | `False` | `sampled_n8_bound_missing` |
| `missing_predecessor_transition_row` | `False` | `missing_predecessor_transition_row` |
| `transition_parent_state_not_in_parent_frontier` | `False` | `transition_parent_state_not_in_parent_frontier` |
| `afterstep_generated_child_mismatch` | `False` | `afterstep_generated_child_mismatch` |
| `transition_step_bit_out_of_range` | `False` | `transition_step_bit_out_of_range` |
| `generated_state_root_mismatch` | `False` | `generated_state_root_mismatch` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `linked_witness_count_mismatch` | `False` | `linked_witness_count_mismatch` |
| `linked_canonical_merkle_membership_count_mismatch` | `False` | `linked_canonical_merkle_membership_count_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | transitions | sampled child masks | unique generated children | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n8_sample_000_thin_fee9000_stair` | `True` | `48` | `17` | `17` | `2a63f35abcbc298e94cafc56ce6cdfdf3b5ae0ab19bb6160ee9aee79ab9608eb` |
| `n8_sample_001_deep_fee30_tie` | `True` | `104` | `17` | `34` | `94c699f544cd4b6b998483d449b7d9aa660e95f61df18d8b791585a51d778514` |
| `n8_sample_002_burst_fee2500` | `True` | `116` | `17` | `37` | `1255b42eb0ac23db74412c95d136c934e1654417799c0bcde48123ca0148fdde` |

## Non-Claims

- This checker is bounded to the deterministic sampled n=8 corpus, not exhaustive n=8 coverage.
- This checker covers only sampled zero-min exact-in cases and sampled child masks.
- This checker links child coverage to the existing sampled n=8 predecessor-witness report.
- This checker links canonical membership to the existing sampled n=8 canonical-Merkle report.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.
