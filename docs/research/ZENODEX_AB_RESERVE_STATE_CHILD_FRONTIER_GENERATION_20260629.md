# ZenoDEX AB Reserve-State Child-Frontier Generation - 2026-06-29

## Executive Result

A bounded host checker supports child-frontier generation for the reserve-state quotient on the committed n=7 strict zero-min corpus: each child quotient family equals the union of predecessor afterStep images.

Research-only certificate-compression evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Child masks checked: `508`
- Frontier equalities: `508`
- Predecessor edges checked: `1792`
- Predecessor transitions checked: `2777`
- Child quotient states: `864`
- Generated states: `864`
- Missing child states: `0`
- Extra generated states: `0`
- Max child states per mask: `5`
- Max generated states per mask: `5`
- Frontier digest: `b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4`
- Negative controls: `7`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'7': 4}`
- Fee histogram: `{'1': 1, '100': 2, '9000': 1}`
- Regime/pattern histogram: `{'high_fee_deep_out/rand_stair': 1, 'near_domain_in/rand_burst': 1, 'near_zero_positive/rand_tie': 1, 'thin_positive_boundary/high_fee9000': 1}`
- Reason classes: `['authority_effect_present', 'generated_frontier_extra_child_state', 'generated_frontier_missing_child_state', 'packet_frontier_summary_mismatch', 'packet_hash_mismatch', 'packet_lean_contract_mismatch']`

## Lean Projection Shape

```json
{
  "host_generation_shape": "child quotient state set equals union of predecessor afterStep images",
  "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
  "transition_def": "ReserveState.afterStep",
  "transition_executability_endpoint": "reserveStateQuotientInvariant_familySuffixExecutable",
  "transition_invariant_endpoint": "reserveStateQuotientInvariant_afterStep"
}
```

The host checker computes, for each child mask, the union of every
predecessor quotient state's one-step child under the same exact-in step.
That generated state set must match the child mask's quotient state set.

## First Frontier Row

```json
{
  "case_id": "n7_randomized_boundary_000_thin_fee9000_rout1100",
  "child_mask_id": 1,
  "child_quotient_digest": "f4a4921b22595e51854a6a3c1df03d9960dd26e0f4fbdec3963f15d1962b3aa9",
  "child_state_count": 1,
  "extra_generated_state_count": 0,
  "extra_generated_states": [],
  "first_predecessor": {
    "generated_state_count": 1,
    "generated_state_digest": "b9f2a1e497c969727600f88866b5f1de57f94b281f076c2d404388b7d727e717",
    "parent_mask_id": 0,
    "parent_quotient_digest": "74bfe2d98beff0789bbfc93d60ca66d200bedcd09aac3477d1548fe912a9ed49",
    "parent_state_count": 1,
    "predecessor_transition_count": 1,
    "predecessor_transition_executable_count": 1,
    "step_bit_index": 0,
    "step_order_id": "0x00000000000000000000000000000000000000000000000000000000006cf5c0",
    "step_order_short": [
      "f5c0"
    ]
  },
  "frontier_equal": true,
  "generated_state_count": 1,
  "generated_state_digest": "b9f2a1e497c969727600f88866b5f1de57f94b281f076c2d404388b7d727e717",
  "missing_child_state_count": 0,
  "missing_child_states": [],
  "predecessor_count": 1,
  "predecessor_rows_digest": "fbd43aae07e508b566fe94080a65979d40df733613bd9f06300214f65e447ad8",
  "predecessor_transition_count": 1,
  "predecessor_transition_executable_count": 1
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `packet_lean_contract_mismatch` | `False` | `packet_lean_contract_mismatch` |
| `packet_frontier_summary_mismatch` | `False` | `packet_frontier_summary_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `generated_frontier_missing_child_state` | `False` | `generated_frontier_missing_child_state` |
| `generated_frontier_extra_child_state` | `False` | `generated_frontier_extra_child_state` |
| `stale_child_quotient_extra_generated_state` | `False` | `generated_frontier_extra_child_state` |

## Case Summary

| case | ok | child masks | child states | generated states | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `127` | `127` | `127` | `54eb4c9f2a58c5e51cd19c34c1ac7cfb371f9fea6ebbd33686e702b2e8a5ef93` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `127` | `320` | `320` | `91b737dab0b90442284b0c82628d618f098c4d013d19180f2cdba16aa28cfa0a` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `127` | `290` | `290` | `622e453b599d8b5c769628078bef4d95a1d8c8af5a8eaa68db8743b49f461354` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `127` | `127` | `127` | `bfb56c51fe16b20de441b102c7473142449cda8515d9851d3ef79813769e0cef` |

## Non-Claims

- This child-frontier checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- No settlement, state-root, production, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_generation_20260629.py
```
