# ZenoDEX AB Reserve-State Transition Projection - 2026-06-29

## Executive Result

A bounded host checker supports the reserve-state quotient transition projection for the committed n=7 strict zero-min corpus by replaying one-step parent-to-child rows against the Lean ReserveState.afterStep surface.

Research-only certificate-compression evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Reachable masks checked: `508`
- Transition rows checked: `1792`
- Selected child memberships: `1792`
- Candidate transitions checked: `2777`
- Candidate child memberships: `2777`
- Candidate processed-reserve matches: `2777`
- Candidate min-reserve checks: `2777`
- Max parent states per row: `5`
- Max child states per row: `5`
- Transition digest: `e0feabfd435cc7f0045831dd4d2f379b74e29dbd6a260457a519e3fd0214f32c`
- Negative controls: `7`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reason classes: `['authority_effect_present', 'candidate_transition_child_not_in_child_quotient', 'packet_hash_mismatch', 'packet_lean_contract_mismatch', 'packet_transition_summary_mismatch', 'selected_transition_child_not_in_child_quotient', 'transition_min_reserve_failure']`

## Lean Projection Shape

```json
{
  "host_projection": "bounded parent-mask one-step transition rows",
  "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
  "transition_def": "ReserveState.afterStep",
  "transition_executability_endpoint": "reserveStateQuotientInvariant_familySuffixExecutable",
  "transition_invariant_endpoint": "reserveStateQuotientInvariant_afterStep"
}
```

Each transition row binds a parent mask, child mask, step bit, selected
parent state, selected child state, parent quotient digest, child quotient
digest, and candidate-child digest. The row checks that every reachable
candidate child remains in the child quotient family and that the selected
child has no greater reserve-out than those candidates.

## First Transition

```json
{
  "candidate_child_digest": "02893c7f4ca212f272fa78a082edd04d5b29ccd44c412dc12e111cc4b628b7a4",
  "candidate_child_membership_count": 1,
  "candidate_min_reserve_check_count": 1,
  "candidate_processed_match_count": 1,
  "candidate_transition_count": 1,
  "candidate_transition_executable_count": 1,
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "child_mask_id": 1,
  "child_quotient_digest": "f4a4921b22595e51854a6a3c1df03d9960dd26e0f4fbdec3963f15d1962b3aa9",
  "child_state_count": 1,
  "lean_executability_endpoint": "reserveStateQuotientInvariant_familySuffixExecutable",
  "lean_invariant_endpoint": "reserveStateQuotientInvariant_afterStep",
  "lean_transition_def": "ReserveState.afterStep",
  "mask_id": 0,
  "parent_quotient_digest": "74bfe2d98beff0789bbfc93d60ca66d200bedcd09aac3477d1548fe912a9ed49",
  "parent_selected_state": {
    "processed_reserve_in": 10000,
    "reserve_out": 1100
  },
  "parent_selected_state_digest": "bd9d9dfd318aac5e489dbd081b4535164c8759e8bb713dacf6a3273f30544fc3",
  "parent_state_count": 1,
  "selected_child_in_child_family": true,
  "selected_child_state": {
    "processed_reserve_in": 10100,
    "reserve_out": 1099
  },
  "selected_child_state_digest": "31832c0a4146b21cf611e3208ef60f80683ee16ad4d01d068a19b14701cba3a2",
  "step_bit_index": 0,
  "step_order_id": "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
  "step_order_short": [
    "f5c0"
  ]
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `packet_lean_contract_mismatch` | `False` | `packet_lean_contract_mismatch` |
| `packet_transition_summary_mismatch` | `False` | `packet_transition_summary_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `selected_transition_child_not_in_child_quotient` | `False` | `selected_transition_child_not_in_child_quotient` |
| `candidate_transition_child_not_in_child_quotient` | `False` | `candidate_transition_child_not_in_child_quotient` |
| `transition_min_reserve_failure` | `False` | `transition_min_reserve_failure` |

## Case Summary

| case | ok | transitions | candidate transitions | digest |
| --- | --- | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `448` | `448` | `cfdc1ebf66e4f20f843ef56fdb7f024e8cd8e1019300edce40eb5511b6e19449` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `448` | `1004` | `e1c923a7c019cfae11620defaf81a4e803165b3d6ea794ae4c7f670c1fcf76e5` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `448` | `877` | `dc3bab24b57a6e9a0182d19957435fbeee7d601e9da9041486044f88d3803845` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `448` | `448` | `fb21bc939edb669a5784b0319074ca4213deec191e652a30c62a69f725efd183` |

## Non-Claims

- This transition checker is bounded to the committed n=7 randomized corpus.
- This checker samples no nonzero min_amount_out certificates.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove full child-frontier generation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- No settlement, state-root, production, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_transition_projection_20260629.py
```
