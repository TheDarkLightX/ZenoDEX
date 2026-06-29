# ZenoDEX AB Reserve-State Child-Frontier Bidirectional Transition Certificate - 2026-06-29

## Executive Result

A bounded bidirectional transition certificate supports the n=7 strict zero-min AB reserve-state child-frontier equality: linked witness+Merkle rows cover child states, and every predecessor afterStep image is a canonical Merkle member of the child frontier.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Child masks checked: `508`
- Transition rows: `2777`
- Expected transitions: `2777`
- Covered transitions: `2777`
- Unique transition rows: `2777`
- Unique generated child states across masks: `864`
- Missing transitions: `0`
- Extra transitions: `0`
- Invalid transition rows: `0`
- Duplicate transition rows: `0`
- Linked child coverage witnesses: `864`
- Transition-to-child-witness ratio: `3.21412`
- Transition rows digest: `fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82`
- Negative controls: `9`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked Child Coverage Report

```json
{
  "available": true,
  "bound_row_count": 864,
  "bound_rows_digest": "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551",
  "case_count": 4,
  "child_mask_count": 508,
  "kind": "witness_merkle",
  "membership_count": 864,
  "negative_control_accept_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_witness_merkle_20260629/report.json",
  "schema": "zenodex.ab_reserve_state_child_frontier_witness_merkle_report.v1",
  "valid_case_count": 4,
  "witness_count": 864
}
```

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reason classes: `['afterstep_generated_child_mismatch', 'authority_effect_present', 'extra_predecessor_transition_row', 'generated_child_not_in_child_frontier', 'generated_state_root_mismatch', 'linked_witness_merkle_bound_row_count_mismatch', 'linked_witness_merkle_summary_mismatch', 'membership_proof_hash_mismatch', 'missing_predecessor_transition_row', 'packet_hash_mismatch', 'packet_transition_summary_mismatch', 'transition_parent_state_not_in_parent_frontier', 'transition_step_bit_out_of_range']`

## First Case

```json
{
  "bit_count": 7,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "child_mask_count": 127,
  "covered_transition_count": 448,
  "duplicate_transition_row_count": 0,
  "expected_transition_count": 448,
  "extra_transition_count": 0,
  "fee_bps": 9000,
  "first_failure": null,
  "invalid_transition_row_count": 0,
  "missing_transition_count": 0,
  "ok": true,
  "packet_hash": "28933a26520a6c743b1b93cd73782065bb5f18960abd8c5a302c7944300323be",
  "pattern": "thin_positive_boundary/high_fee9000",
  "reasons": [],
  "transition_row_count": 448,
  "transition_rows_digest": "ce88df5af288e0d989f47ad3739c8ca0f90ecf813c20e0d26c6014a97c44c33a",
  "unique_generated_child_count": 127,
  "unique_transition_count": 448
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `missing_predecessor_transition_row` | `False` | `missing_predecessor_transition_row` |
| `transition_parent_state_not_in_parent_frontier` | `False` | `transition_parent_state_not_in_parent_frontier` |
| `afterstep_generated_child_mismatch` | `False` | `afterstep_generated_child_mismatch` |
| `transition_step_bit_out_of_range` | `False` | `transition_step_bit_out_of_range` |
| `generated_state_root_mismatch` | `False` | `generated_state_root_mismatch` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `linked_witness_merkle_bound_row_count_mismatch` | `False` | `linked_witness_merkle_bound_row_count_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | transitions | child masks | unique generated children | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `448` | `127` | `127` | `ce88df5af288e0d989f47ad3739c8ca0f90ecf813c20e0d26c6014a97c44c33a` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `1004` | `127` | `320` | `52156b78e1b71ff93bd584ff358ce959a3a94a7fa2e8d2d4d31c21173034e36b` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `877` | `127` | `290` | `760e74560c7d8b8ae27ec73af46b4770efa976d975fa7c2e8213f57c53f4b147` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `448` | `127` | `127` | `3e0b201dcc9c017bab65e9a9cd3bc884def0b8afcbb28e05377055ec5f585118` |

## Non-Claims

- This checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker links the child coverage direction to the existing witness+Merkle report.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.
