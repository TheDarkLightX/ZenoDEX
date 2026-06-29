# ZenoDEX AB Reserve-State Child-Frontier Witness+Merkle Cross-Binding - 2026-06-29

## Executive Result

A bounded n=7 host checker supports a cross-bound child-frontier proof object: each child quotient state has both a predecessor witness and a canonical-index Merkle membership proof for the same child mask and reserve state.

research_only_no_settlement_or_state_authority

## Certificate Shape

```text
predecessor_witness(child_mask, child_state) + canonical_merkle_membership(child_mask, child_state)
  -> cross-bound child-frontier row
```

The checker accepts only when both proofs point at the same child mask and reserve-state quotient.

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Child masks checked: `508`
- Expected child states: `864`
- Cross-bound rows: `864`
- Witness rows: `864`
- Merkle memberships: `864`
- Covered child states: `864`
- Missing bound rows: `0`
- Extra bound rows: `0`
- Invalid bound rows: `0`
- Duplicate bound rows: `0`
- Baseline predecessor transitions: `2777`
- Witness/Merkle compression ratio: `3.21412`
- Transition checks saved: `1913`
- Bound rows digest: `0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551`
- Negative controls: `10`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked Reports

```json
{
  "merkle": {
    "available": true,
    "case_count": 4,
    "child_mask_count": 508,
    "child_state_count": 864,
    "digest": "84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559",
    "kind": "merkle",
    "negative_control_accept_count": 0,
    "ok": true,
    "path": "generated/zenodex_ab_reserve_state_child_frontier_canonical_merkle_20260629/report.json",
    "schema": "zenodex.ab_reserve_state_child_frontier_canonical_merkle_report.v1",
    "valid_case_count": 4
  },
  "witness": {
    "available": true,
    "case_count": 4,
    "child_mask_count": 508,
    "child_state_count": 864,
    "digest": "d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3",
    "kind": "witness",
    "negative_control_accept_count": 0,
    "ok": true,
    "path": "generated/zenodex_ab_reserve_state_child_frontier_witness_compression_20260629/report.json",
    "schema": "zenodex.ab_reserve_state_child_frontier_witness_compression_report.v1",
    "valid_case_count": 4
  }
}
```

## Coverage

```json
{
  "fee_bps_counts": {
    "1": 1,
    "100": 2,
    "9000": 1
  },
  "n_counts": {
    "7": 4
  },
  "pattern_counts": {
    "high_fee_deep_out/rand_stair": 1,
    "near_domain_in/rand_burst": 1,
    "near_zero_positive/rand_tie": 1,
    "thin_positive_boundary/high_fee9000": 1
  },
  "reason_classes": [
    "authority_effect_present",
    "bound_child_state_not_in_frontier",
    "canonical_leaf_index_mismatch",
    "cross_bound_child_state_mismatch",
    "duplicate_bound_row",
    "extra_child_bound_row",
    "generated_state_root_mismatch",
    "membership_proof_hash_mismatch",
    "membership_proof_shape_mismatch",
    "missing_child_bound_row",
    "packet_hash_mismatch",
    "packet_witness_merkle_summary_mismatch",
    "witness_afterstep_mismatch",
    "witness_child_state_not_in_child_frontier",
    "witness_parent_state_not_in_parent_frontier",
    "witness_step_bit_out_of_range"
  ]
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `missing_child_bound_row` | `False` | `missing_child_bound_row` |
| `witness_parent_state_not_in_parent_frontier` | `False` | `witness_parent_state_not_in_parent_frontier` |
| `witness_step_bit_out_of_range` | `False` | `witness_step_bit_out_of_range` |
| `generated_state_root_mismatch` | `False` | `generated_state_root_mismatch` |
| `canonical_leaf_index_mismatch` | `False` | `canonical_leaf_index_mismatch` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `cross_bound_child_state_mismatch` | `False` | `cross_bound_child_state_mismatch` |
| `duplicate_bound_row` | `False` | `duplicate_bound_row` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | ok | bound rows | predecessor transitions | ratio | digest |
| --- | --- | ---: | ---: | ---: | --- |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `True` | `127` | `448` | `3.527559` | `4720d06a30a7707eec19b08a83ff2c5802b3d8d8d12183017d479a0ec2e9f6b2` |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `True` | `320` | `1004` | `3.1375` | `e84f09be2040986a317dc98c31f967b97703c36ca2d356e286b6f9f5de4871ed` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `True` | `290` | `877` | `3.024138` | `896337c7e1edb9c4416b04d1755bb1b01ee1fa2d4eb5e3a86584052a74e150ba` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `True` | `127` | `448` | `3.527559` | `f30f66bf6fddcc14268e9e1ada910dd285f61e0663045ccf6738fc7a230f5080` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+single row shape for generation and membership",
    "execution_quality": "0",
    "perf_cost": "+Merkle proof verification per child state",
    "safety": "+rejects witness/Merkle row mismatch and root malleability"
  },
  "falsification_recipe": "Mutate witness parents, step bits, Merkle roots, leaf indexes, membership hashes, cross-bound child states, duplicate rows, packet hash, and authority rails.",
  "formal_obligations": "A production-grade theorem would need Python-to-Lean refinement or a Lean-native generated-image and canonical-Merkle checker.",
  "hypothesis_id": "H-AB-N7-WITNESS-MERKLE-CROSS-BIND-20260629",
  "mechanism_change": "Bind each predecessor witness row to a canonical Merkle membership proof for the same child mask and child state.",
  "null_hypothesis": "Composing the witness and canonical-Merkle certificates into one row shape does not add detectable constraints beyond the two independent reports.",
  "representation_shift_used": "certificate_boundary",
  "risk_modes": [
    "witness row and membership proof refer to different child states",
    "generated root is stale",
    "leaf index is noncanonical",
    "coverage witness overclaimed as no-extra generation",
    "authority leakage"
  ],
  "status": "supported_bounded",
  "support_recipe": "Verify all n=7 corpus rows, link both prior reports, assert zero missing/extra/invalid/duplicate bound rows, and assert zero accepted negative controls."
}
```

## Non-Claims

- This cross-bound checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not replace a deterministic generated-image producer.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_witness_merkle_20260629.py
```
