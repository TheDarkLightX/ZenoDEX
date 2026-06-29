# ZenoDEX AB Count-Aware Merkle Certificate - 2026-06-29

## Executive Result

A bounded count-aware Merkle verifier rejects a hidden-extra replay that a naive membership verifier accepts when the packet lies about the generated-state count.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Certificate Shape

```text
generated_state_root + generated_state_count + count-aware membership proofs
```

The verifier checks proof shape against the claimed generated-state count before accepting membership.

## Replay Result

- Baseline packet hash: `a9b4fc00fae3e7db01c2269b33163c92e69ecb78cd32352d052129335ee8d455`
- Baseline generated-state root: `aa7ec0b30917784becf3806b06fc63fe831e14ed94eb227d958f83a08b3e0e7a`
- Lying-count generated-state root: `fc408c353cfb375a8e44404e820fc86ef75c73295f5a13c936ccd774f3667e74`
- Child-state digest: `20debc2b386b88b55708cbd5c6d18febab91b3ea22beea0f030064f40d3d7dfd`
- Membership rows digest: `442d6554f9fe8da910824cfe43d1a3197b1fbfddd4b57795bc51815bc2a1f0f8`
- Witness rows digest: `8216f62477012095592dcc45ed7551b3cadf83d84aa1a3f61f5b612f7ce60290`
- Child states: `2`
- Naive baseline accepted: `True`
- Naive honest-extra rejected: `True`
- Naive lying-count accepted: `True`
- Count-aware baseline accepted: `True`
- Count-aware lying-count rejected: `True`
- Count-aware honest-extra rejected: `True`
- Coverage-only rejected: `True`
- Negative controls: `10`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Naive Countermodel

```json
{
  "count_aware_lying_count": {
    "child_state_count": 2,
    "covered_child_state_count": 2,
    "generated_state_count": 2,
    "membership_count": 2,
    "ok": false,
    "reasons": [
      "membership_proof_shape_mismatch"
    ],
    "valid_membership_count": 0,
    "witness_count": 2
  },
  "hidden_extra_state": {
    "processed_reserve_in": 170,
    "reserve_out": 9830
  },
  "naive_lying_count": {
    "child_state_count": 2,
    "covered_child_state_count": 2,
    "generated_state_count": 2,
    "membership_count": 2,
    "ok": true,
    "reasons": [],
    "valid_membership_count": 2,
    "witness_count": 2
  }
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `generated_state_root_stale` | `False` | `membership_proof_hash_mismatch` |
| `generated_state_count_mismatch` | `False` | `generated_state_count_mismatch` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `missing_membership_proof` | `False` | `missing_membership_proof` |
| `duplicate_membership_proof` | `False` | `duplicate_membership_proof` |
| `missing_child_state_witness` | `False` | `missing_child_state_witness` |
| `generated_count_bound_missing` | `False` | `generated_count_bound_missing` |
| `count_aware_membership_bound_missing` | `False` | `count_aware_membership_bound_missing` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+explicit count-aware root contract",
    "execution_quality": "0",
    "perf_cost": "+membership proof shape checks",
    "safety": "+rejects false-count hidden-extra Merkle replay"
  },
  "falsification_recipe": "Build a root over three generated states, claim count two, and supply valid naive proofs for the two advertised child states.",
  "formal_obligations": "A formal version should prove that count-aware proof shape plus unique child states and generated_count equality imply no hidden extra leaves for the committed Merkle tree.",
  "hypothesis_id": "H-AB-COUNT-AWARE-MERKLE-CERTIFICATE-20260629",
  "mechanism_change": "Bind Merkle membership proof shape to generated_state_count before using root membership as a no-extra child-frontier certificate.",
  "null_hypothesis": "A generated-state root plus naive membership proofs is sufficient to support bounded no-extra child-frontier equality.",
  "representation_shift_used": "certificate_boundary",
  "risk_modes": [
    "naive membership verification ignores leaf_count",
    "false generated count",
    "hidden generated state",
    "stale root",
    "authority leakage"
  ],
  "status": "supported_bounded",
  "support_recipe": "Require the count-aware verifier to accept baseline, reject the false-count replay, reject honest extra count, reject coverage-only packets, and reject all negative controls."
}
```

## Design Recommendation

- Use count-aware Merkle membership verification for generated-image roots.
- Reject packets where membership proof shape does not match the claimed generated_state_count.
- Treat root-only membership as insufficient for no-extra claims unless count-aware proof shape is checked.

## Non-Claims

- Scope is limited to a bounded certificate-boundary countermodel and checker design.
- This artifact does not prove child-frontier generation in Lean.
- This artifact does not prove Python-to-Lean refinement.
- This artifact does not replace a deterministic generated-image producer.
- This artifact does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_child_frontier_count_aware_merkle_certificate_20260629.py
```
