# ZenoDEX AB Reserve-State Child-Frontier Canonical Merkle - 2026-06-29

## Executive Result

A bounded n=7 host checker supports canonical-index Merkle roots for AB reserve-state child frontiers: 508 child-mask roots cover 864 child quotient states with zero missing, invalid, or stale membership proofs.

research_only_no_settlement_or_state_authority

## Evidence Summary

- Cases checked: `4`
- Valid cases: `4`
- Child masks checked: `508`
- Frontier roots: `508`
- Child quotient states: `864`
- Membership proofs: `864`
- Covered child states: `864`
- Missing membership proofs: `0`
- Invalid membership proofs: `0`
- Root mismatches: `0`
- Max leaves per root: `5`
- Frontier roots digest: `42f3e7f10918fa3497183812cb316955c3382f4f3b4a4bb5309e47ec5855008b`
- Membership rows digest: `84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559`
- Permutation countermodel valid: `True`
- Negative controls: `8`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Permutation Countermodel

```json
{
  "canonical_index_reject_reason": "canonical_leaf_index_mismatch",
  "canonical_root": "9cd0be237e72fe99e3d42aca275cba7000b414b91c6f5a84c0680a4bd066120f",
  "case_id": "n7_randomized_000_near_zero_positive_rand_tie_fee1",
  "child_mask_id": 3,
  "count_aware_accepts_permuted": true,
  "leaf_count": 2,
  "permuted_root": "2fd97652cbc53111628bb724095f6faa02f61816e37ea73638f64340ad5378c3",
  "roots_differ": true
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
    "canonical_leaf_index_mismatch",
    "duplicate_leaf_index",
    "frontier_generated_state_root_mismatch",
    "linked_frontier_extra_generated_state",
    "linked_frontier_summary_mismatch",
    "membership_proof_hash_mismatch",
    "membership_proof_shape_mismatch",
    "missing_membership_proof",
    "packet_canonical_merkle_summary_mismatch",
    "packet_hash_mismatch"
  ]
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `frontier_generated_state_root_mismatch` | `False` | `frontier_generated_state_root_mismatch` |
| `canonical_leaf_index_mismatch` | `False` | `canonical_leaf_index_mismatch` |
| `missing_membership_proof` | `False` | `missing_membership_proof` |
| `duplicate_leaf_index` | `False` | `duplicate_leaf_index` |
| `packet_canonical_merkle_summary_mismatch` | `False` | `packet_canonical_merkle_summary_mismatch` |
| `linked_frontier_extra_generated_state` | `False` | `linked_frontier_extra_generated_state` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Non-Claims

- This canonical Merkle checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not replace a deterministic generated-image producer.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_canonical_merkle_20260629.py
```
