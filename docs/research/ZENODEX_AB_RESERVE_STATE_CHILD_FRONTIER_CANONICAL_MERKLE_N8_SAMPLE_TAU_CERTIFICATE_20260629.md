# ZenoDEX AB Reserve-State Child-Frontier Canonical Merkle N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_reserve_state_child_frontier_canonical_merkle_n8_sample_scope_certificate_v1` admits the sampled n=8 canonical-Merkle research bundle only when the source report, sampled n=8 zero-min scope, linked frontier equality report, frontier-root counts, membership counts, membership proof cleanliness, digest pins, deterministic replay, negative controls, normalized source hash, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `sampled_n8_zero_min_scope_ok` = `1`
- `linked_frontier_ok` = `1`
- `frontier_counts_ok` = `1`
- `membership_counts_ok` = `1`
- `membership_proofs_clean` = `1`
- `frontier_roots_digest_pinned` = `1`
- `membership_rows_digest_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `normalized_source_hash_pinned` = `1`
- `hash_normalization_declared` = `1`

## Canonical Merkle Corpus

- Normalized source hash: `b4318b47670c43b4fce96e3cb5ed0b55cf2ad7a8dd4314ea04db95b7502b1f2a`
- Frontier roots: `51`
- Membership proofs: `88`
- Sampled child states: `88`
- Frontier roots digest: `53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4`
- Membership rows digest: `bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2`
- Deterministic replay hash: `31df88fd8d43c07cd20742854e8553e5b3ab5fef4259726f9968c8ff67293f43`
- Negative controls: `9`
- Negative control accepts: `0`
- Tau cases: `17`
- Invalid accepts: `0`

## Linked Frontier Report

```json
{
  "available": true,
  "extra_generated_state_count": 0,
  "frontier_rows_digest": "37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919",
  "generated_state_count": 88,
  "missing_child_state_count": 0,
  "ok": true,
  "path": "generated/zenodex_ab_reserve_state_child_frontier_n8_sample_20260629/report.json",
  "sampled_child_mask_count": 51,
  "sampled_child_state_count": 88,
  "schema": "zenodex.ab_reserve_state_child_frontier_n8_sample_report.v1"
}
```

## Tau Cases

| case | ok | o7 | rationale |
| --- | ---: | ---: | --- |
| `canonical_merkle_n8_sample_certificate_pass` | `True` | `1` | All scoped host facts admit the sampled n=8 canonical-Merkle certificate. |
| `missing_source_report_reject` | `True` | `0` | The `source_report_ok` host fact is required for certificate admission. |
| `wrong_scope_reject` | `True` | `0` | The `sampled_n8_zero_min_scope_ok` host fact is required for certificate admission. |
| `linked_frontier_reject` | `True` | `0` | The `linked_frontier_ok` host fact is required for certificate admission. |
| `frontier_counts_reject` | `True` | `0` | The `frontier_counts_ok` host fact is required for certificate admission. |
| `membership_counts_reject` | `True` | `0` | The `membership_counts_ok` host fact is required for certificate admission. |
| `membership_proofs_reject` | `True` | `0` | The `membership_proofs_clean` host fact is required for certificate admission. |
| `frontier_digest_reject` | `True` | `0` | The `frontier_roots_digest_pinned` host fact is required for certificate admission. |
| `membership_digest_reject` | `True` | `0` | The `membership_rows_digest_pinned` host fact is required for certificate admission. |
| `nondeterministic_replay_reject` | `True` | `0` | The `deterministic_replay_ok` host fact is required for certificate admission. |
| `negative_controls_missing_reject` | `True` | `0` | The `negative_controls_reject` host fact is required for certificate admission. |
| `authority_boundary_reject` | `True` | `0` | The `authority_boundary_ok` host fact is required for certificate admission. |
| `authority_effect_reject` | `True` | `0` | The `no_authority_effect` host fact is required for certificate admission. |
| `empty_corpus_reject` | `True` | `0` | The `corpus_nonvacuous` host fact is required for certificate admission. |
| `source_hash_reject` | `True` | `0` | The `normalized_source_hash_pinned` host fact is required for certificate admission. |
| `hash_normalization_reject` | `True` | `0` | The `hash_normalization_declared` host fact is required for certificate admission. |
| `inactive_safe` | `True` | `0` | Inactive certificates do not admit while the no-authority rail remains true. |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min canonical-Merkle report.
- This certificate uses a normalized source hash that strips elapsed_ms fields.
- This certificate links the separate sampled n=8 child-frontier equality report.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_canonical_merkle_n8_sample_tau_certificate_20260629.py
```
