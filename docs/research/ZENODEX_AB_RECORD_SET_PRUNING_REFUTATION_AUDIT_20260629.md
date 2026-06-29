# ZenoDEX AB Record-Set Pruning Refutation Audit - 2026-06-29

## Executive Result

A falsify-first audit found no mismatch in the AB strict zero-min record-set pruning claim surface: the Lean theorem premises, generated reports, and public non-claims remain aligned.

Research-only proof-surface audit; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Audit Summary

- Audit ok: `True`
- Reasons: `[]`
- Negative controls: `8`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Claim Surface

- `same_processed_reserve_bound` = `True`
- `selected_min_reserve_bound` = `True`
- `selected_suffix_executable_bound` = `True`
- `economic_key_dominance_bound` = `True`
- `scope_nonclaims_bound` = `True`

## Report Bindings

```json
{
  "record_key_ok": true,
  "record_key_schema": "zenodex.ab_strict_zero_min_record_key_certificate_lean_report.v1",
  "record_key_theorem_count": 6,
  "record_set_status": "pass",
  "record_set_theorem_count": 4
}
```

## Lean Surface

```json
{
  "placeholder_free": true,
  "required_theorem_count": 8,
  "strict_record_set_certificate_decl_hash": "6645dd7981cb6fe084bb9c0abd0f8e5b67c22bc2d149c34ccfa44acc85a1cbe9",
  "strict_record_set_validates_decl_hash": "315f15cce3cffee1d80dd8cd664536afa717926f6fff3f91c1f9edee2dc81fd4"
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `lean_placeholder_token_present` | `False` | `lean_placeholder_token_present` |
| `same_processed_reserve_premise_missing` | `False` | `same_processed_reserve_premise_missing` |
| `selected_min_reserve_premise_missing` | `False` | `selected_min_reserve_premise_missing` |
| `selected_suffix_executable_premise_missing` | `False` | `selected_suffix_executable_premise_missing` |
| `forbidden_full_subset_dp_claim` | `False` | `forbidden_full_subset_dp_claim` |
| `record_key_report_not_ok` | `False` | `record_key_report_not_ok` |
| `record_key_theorem_list_incomplete` | `False` | `record_key_theorem_list_incomplete` |
| `forbidden_authority_claim` | `False` | `forbidden_authority_claim` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+single replay gate",
    "execution_quality": "0",
    "perf_cost": "-audit overhead only",
    "safety": "+scope assurance"
  },
  "falsification_recipe": "Mutate theorem premises, report status, theorem lists, and public claims; require stable reject reasons.",
  "formal_obligations": "Lean remains the authority for theorem proofs; this checker audits surface bindings and scope.",
  "hypothesis_id": "H-AB-RECORD-SET-REFUTE-20260629",
  "mechanism_change": "Refute stale or over-broad record-set pruning claims before building more reserve-state quotient layers.",
  "null_hypothesis": "The record-set certificate surface contains a missing premise, stale theorem binding, failed verification receipt, or positive overclaim.",
  "representation_shift_used": "counterexample_boundary",
  "risk_modes": [
    "stale generated JSON",
    "missing Lean premise",
    "overclaim in public docs",
    "authority leakage",
    "test coverage drift"
  ],
  "status": "supported",
  "support_recipe": "Compile Lean, run focused formal test, bind generated reports, scan non-claims, and reject negative controls."
}
```

## Non-Claims

- This audit does not prove Python-to-Lean refinement.
- This audit does not construct a subset DP table.
- This audit does not define canonical tie order.
- This audit does not cover nonzero min_amount_out behavior.
- This audit does not prove JSON canonicalization or packet hashing in Lean.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_record_set_pruning_refutation_audit_20260629.py
```
