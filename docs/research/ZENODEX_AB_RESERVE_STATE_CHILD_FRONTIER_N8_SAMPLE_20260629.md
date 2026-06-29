# ZenoDEX AB Reserve-State Child Frontier n=8 Sample - 2026-06-29

## Executive Result

A bounded deterministic n=8 sample supports reserve-state child-frontier generation on the sampled masks: each sampled child quotient family equals the union of predecessor afterStep images.

Research-only certificate-compression evidence; no settlement, state-root, production, or governance authority.

## Evidence Summary

- Cases checked: `3`
- Sampled child masks: `51`
- Frontier equalities: `51`
- Predecessor edges: `144`
- Predecessor transitions: `268`
- Sampled child states: `88`
- Generated states: `88`
- Missing child states: `0`
- Extra generated states: `0`
- Max child states per sampled mask: `7`
- Frontier digest: `37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919`
- Negative controls: `7`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Coverage

- `n` histogram: `{'8': 3}`
- Fee histogram: `{'2500': 1, '30': 1, '9000': 1}`
- Regime/pattern histogram: `{'n8_deep_low_fee/tie': 1, 'n8_deep_mid_fee/front_burst': 1, 'n8_thin_high_fee/stair': 1}`
- Reason classes: `['authority_effect_present', 'generated_frontier_extra_child_state', 'generated_frontier_missing_child_state', 'packet_hash_mismatch', 'packet_lean_contract_mismatch', 'packet_sample_plan_mismatch', 'sampled_n8_bound_missing']`

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

## Lean Projection Shape

```json
{
  "host_generation_shape": "sampled child quotient state set equals union of predecessor afterStep images",
  "lean_file": "lean-mathlib/Proofs/ABReserveStateQuotient.lean",
  "transition_def": "ReserveState.afterStep",
  "transition_executability_endpoint": "reserveStateQuotientInvariant_familySuffixExecutable",
  "transition_invariant_endpoint": "reserveStateQuotientInvariant_afterStep"
}
```

The host checker computes, for each sampled child mask, the union of every
predecessor quotient state's one-step child under the same exact-in step.
That generated set must match the sampled child mask's quotient state set.

## First Frontier Row

```json
{
  "case_id": "n8_sample_000_thin_fee9000_stair",
  "child_mask_id": 1,
  "child_quotient_digest": "2d5ec3c17eca227b2bc1c71e7efe8ac0e4b7f7ac687986327f7a18a789a5d816",
  "child_state_count": 1,
  "extra_generated_state_count": 0,
  "extra_generated_states": [],
  "first_predecessor": {
    "generated_state_count": 1,
    "generated_state_digest": "59877918f7dd52390d68ab195c4303e7569798b8dc1e4bca7cc5466cbbe46c7c",
    "parent_mask_id": 0,
    "parent_quotient_digest": "def37c5bc34f6776c10da1a4ba66aef1c4a1031129bd81de8bae8909a73ed586",
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
  "generated_state_digest": "59877918f7dd52390d68ab195c4303e7569798b8dc1e4bca7cc5466cbbe46c7c",
  "missing_child_state_count": 0,
  "missing_child_states": [],
  "predecessor_count": 1,
  "predecessor_rows_digest": "6aed71c042d8fae5d30fbfb41c0a97ea32596e8d2964b926b112b9d9f06c2e7b",
  "predecessor_transition_count": 1,
  "predecessor_transition_executable_count": 1
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `sampled_n8_bound_missing` | `False` | `sampled_n8_bound_missing` |
| `packet_sample_plan_mismatch` | `False` | `packet_sample_plan_mismatch` |
| `packet_lean_contract_mismatch` | `False` | `packet_lean_contract_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |
| `generated_frontier_missing_child_state` | `False` | `generated_frontier_missing_child_state` |
| `generated_frontier_extra_child_state` | `False` | `generated_frontier_extra_child_state` |

## Case Summary

| case | ok | sampled child masks | child states | generated states | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n8_sample_000_thin_fee9000_stair` | `True` | `17` | `17` | `17` | `9407ad4a9115e87cee1ab9ab04dee9325570fb0d3009d2c8e8bf65493166537c` |
| `n8_sample_001_deep_fee30_tie` | `True` | `17` | `34` | `34` | `e59508b450bdd39a089fd82316bf5beefa5ff702fff21f7a5f8ad52043b76889` |
| `n8_sample_002_burst_fee2500` | `True` | `17` | `37` | `37` | `24030620909166d67911962010ba393906c9ec7a52e1a3b5702e16a2edccf7aa` |

## Non-Claims

- This is a bounded deterministic n=8 sample, not exhaustive n=8 coverage.
- This checker covers only sampled zero-min exact-in cases and sampled child masks.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not define canonical tie order or preserve order-id history.
- No settlement, state-root, production, routing, matching, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_n8_sample_20260629.py
```
