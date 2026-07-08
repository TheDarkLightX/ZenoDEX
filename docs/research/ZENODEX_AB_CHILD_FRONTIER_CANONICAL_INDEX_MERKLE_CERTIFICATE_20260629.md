# ZenoDEX AB Canonical-Index Merkle Certificate - 2026-06-29

## Executive Result

A bounded canonical-index Merkle verifier rejects root malleability that count-aware membership verification accepts for the same child-state set.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Certificate Shape

```text
generated_state_root + generated_state_count + count-aware membership proofs + canonical leaf-index binding
```

The verifier checks that each child state's proof leaf index equals its sorted canonical index.

## Replay Result

- Canonical packet hash: `0cd0adf520ed995c0ff58421028f75144e8293de2381f3c3453414b18a949e0c`
- Canonical generated-state root: `aa7ec0b30917784becf3806b06fc63fe831e14ed94eb227d958f83a08b3e0e7a`
- Permuted packet hash: `7a8f53baaa6e9ef48aa0d5f7b33e4dd575efb6baa97a8054ee33de8f098728dd`
- Permuted generated-state root: `adf4287256b1851a33f0dc425cd194bdf429fdc39f5599ab665cf88d7d11a32c`
- Child-state digest: `20debc2b386b88b55708cbd5c6d18febab91b3ea22beea0f030064f40d3d7dfd`
- Canonical membership rows digest: `442d6554f9fe8da910824cfe43d1a3197b1fbfddd4b57795bc51815bc2a1f0f8`
- Permuted membership rows digest: `b0b57f8437fcb0fb3ca1a35af14ab8364378d06ea69a9b811d9fb9bf649a6dfe`
- Witness rows digest: `8216f62477012095592dcc45ed7551b3cadf83d84aa1a3f61f5b612f7ce60290`
- Child states: `2`
- Count-aware accepts canonical root: `True`
- Count-aware accepts permuted root: `True`
- Canonical-index accepts canonical root: `True`
- Canonical-index rejects permuted root: `True`
- Canonical-index rejects missing bound: `True`
- Negative controls: `10`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Root-Malleability Countermodel

```json
{
  "canonical_index_permuted": {
    "child_state_count": 2,
    "covered_child_state_count": 2,
    "generated_state_count": 2,
    "membership_count": 2,
    "ok": false,
    "reasons": [
      "canonical_leaf_index_mismatch"
    ],
    "valid_membership_count": 2,
    "witness_count": 2
  },
  "count_aware_permuted": {
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
| `canonical_leaf_index_mismatch` | `False` | `canonical_leaf_index_mismatch` |
| `duplicate_leaf_index` | `False` | `duplicate_leaf_index` |
| `missing_membership_proof` | `False` | `missing_membership_proof` |
| `membership_proof_hash_mismatch` | `False` | `membership_proof_hash_mismatch` |
| `missing_child_state_witness` | `False` | `missing_child_state_witness` |
| `canonical_leaf_index_bound_missing` | `False` | `canonical_leaf_index_bound_missing` |
| `count_aware_membership_bound_missing` | `False` | `count_aware_membership_bound_missing` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+single root per sorted child-state set",
    "execution_quality": "0",
    "perf_cost": "+canonical index equality checks",
    "safety": "+rejects permuted-root certificate malleability"
  },
  "falsification_recipe": "Build two packets for the same child states: one sorted, one permuted. Count-aware membership accepts both roots; canonical index verification rejects the permuted root.",
  "formal_obligations": "A formal version should prove canonical sorted leaf-index binding gives a unique Merkle root for a scoped unique child-state set.",
  "hypothesis_id": "H-AB-CANONICAL-INDEX-MERKLE-CERTIFICATE-20260629",
  "mechanism_change": "Bind each child-state membership proof to the canonical sorted leaf index before accepting a generated-image Merkle root.",
  "null_hypothesis": "Count-aware membership proofs are enough to make a generated-image root canonical for a bounded child-state set.",
  "representation_shift_used": "certificate_boundary",
  "risk_modes": [
    "permuted root malleability",
    "leaf index replay",
    "duplicate leaf index",
    "missing canonical-index rail",
    "authority leakage"
  ],
  "status": "supported_bounded",
  "support_recipe": "Accept the canonical packet, reject the permuted packet with canonical_leaf_index_mismatch, reject missing canonical-index binding, and reject all negative controls."
}
```

## Design Recommendation

- Use canonical sorted leaf-index binding with count-aware Merkle membership proofs.
- Reject permuted roots even when they contain the same child-state set.
- Treat count-aware membership alone as a no-extra check, not as a canonical-root check.

## Non-Claims

- Scope is limited to a bounded certificate-boundary countermodel and checker design.
- This artifact does not prove child-frontier generation in Lean.
- This artifact does not prove Python-to-Lean refinement.
- This artifact does not replace a deterministic generated-image producer.
- This artifact does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_child_frontier_canonical_index_merkle_certificate_20260629.py
```
