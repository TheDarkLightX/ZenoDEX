# ZenoDEX AB Reserve-State Child-Frontier Corpus Root - 2026-06-29

## Executive Result

A bounded n=7 host checker compresses 864 witness+Merkle cross-bound child-frontier row receipts into four case roots and one corpus root with fail-closed inclusion checks.

research_only_no_settlement_or_state_authority

## Certificate Shape

```text
row_receipt -> case_root -> corpus_root
```

The checker accepts only when every cross-bound row receipt is included in its case root and every case root is included in the corpus root.

## Evidence Summary

- Cases checked: `4`
- Row receipts: `864`
- Covered row receipts: `864`
- Missing row receipts: `0`
- Extra row receipts: `0`
- Invalid row receipts: `0`
- Duplicate row receipts: `0`
- Case-root mismatches: `0`
- Corpus-root mismatches: `0`
- Row membership mismatches: `0`
- Corpus root: `8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0`
- Case summaries digest: `afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28`
- Row receipts digest: `d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092`
- Max rows per case: `320`
- Negative controls: `10`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Linked Cross-Binding Report

```json
{
  "available": true,
  "bound_row_count": 864,
  "bound_rows_digest": "0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551",
  "case_count": 4,
  "child_mask_count": 508,
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

```json
{
  "case_row_count_histogram": {
    "127": 2,
    "290": 1,
    "320": 1
  },
  "n_counts": {
    "7": 4
  },
  "reason_classes": [
    "authority_effect_present",
    "case_index_out_of_range",
    "case_membership_hash_mismatch",
    "case_row_root_mismatch",
    "corpus_summary_mismatch",
    "duplicate_row_receipt",
    "extra_row_receipt",
    "linked_cross_binding_bound_row_count_mismatch",
    "linked_cross_binding_summary_mismatch",
    "missing_row_receipt",
    "packet_hash_mismatch",
    "row_hash_mismatch",
    "row_membership_hash_mismatch",
    "row_receipt_index_out_of_range"
  ]
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `row_hash_mismatch` | `False` | `row_hash_mismatch` |
| `row_membership_hash_mismatch` | `False` | `row_membership_hash_mismatch` |
| `case_row_root_mismatch` | `False` | `case_row_root_mismatch` |
| `case_membership_hash_mismatch` | `False` | `case_membership_hash_mismatch` |
| `missing_row_receipt` | `False` | `missing_row_receipt` |
| `duplicate_row_receipt` | `False` | `duplicate_row_receipt` |
| `case_index_out_of_range` | `False` | `case_index_out_of_range` |
| `linked_cross_binding_bound_row_count_mismatch` | `False` | `linked_cross_binding_bound_row_count_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Case Summary

| case | rows | row root |
| --- | ---: | --- |
| `n7_randomized_000_near_zero_positive_rand_tie_fee1` | `320` | `0e1a448b555283325f371ec0ad418bb40b7caca6307bc86040ac5e35e8a0ad1f` |
| `n7_randomized_001_high_fee_deep_out_rand_stair_fee100` | `290` | `aa5d2b22032a56aef109a471d7e504a51806133804f6e0fd9f5a1206aa53d295` |
| `n7_randomized_002_near_domain_in_rand_burst_fee100` | `127` | `f62062f1d7a38eaa896ec93b610c4c1aa4554896f11501d31045b9298bd64fad` |
| `n7_randomized_boundary_000_thin_fee9000_rout1100` | `127` | `6ab43ed0917e309ad273b99321df188a37854dd1a56c01d958c12f74f04dc829` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+canonical corpus root for replay and audit",
    "execution_quality": "0",
    "perf_cost": "+Merkle verification, -large receipt comparison surface",
    "safety": "+single corpus commitment rejects stale or missing row receipts"
  },
  "falsification_recipe": "Mutate row hashes, row proofs, case roots, case proofs, row presence, duplicate indexes, case indexes, linked-report summary, packet hash, and authority rails.",
  "formal_obligations": "A production-grade artifact would need a versioned verifier grammar and a Lean or Tau-level statement for the corpus-root membership relation.",
  "hypothesis_id": "H-AB-N7-CORPUS-ROOT-20260629",
  "mechanism_change": "Aggregate cross-bound child-frontier rows into case roots and one corpus root with row and case membership proofs.",
  "null_hypothesis": "Adding a corpus root gives no extra falsifiable constraint beyond the row-level witness+Merkle report.",
  "representation_shift_used": "certificate_boundary",
  "risk_modes": [
    "row receipt omitted from corpus root",
    "case root stale or from a different case",
    "corpus root stale",
    "duplicate row index",
    "linked cross-binding report stale",
    "authority leakage"
  ],
  "status": "supported_bounded",
  "support_recipe": "Verify all 864 row receipts through case roots and the corpus root, assert the linked cross-binding report, and reject all mutation controls."
}
```

## Non-Claims

- This corpus-root checker is bounded to the committed n=7 randomized corpus.
- This checker covers only zero-min exact-in cases in the scoped corpus.
- This checker does not prove Python-to-Lean refinement.
- This checker does not prove child-frontier generation in Lean.
- This checker does not replace a deterministic generated-image producer.
- This checker does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_corpus_root_20260629.py
```
