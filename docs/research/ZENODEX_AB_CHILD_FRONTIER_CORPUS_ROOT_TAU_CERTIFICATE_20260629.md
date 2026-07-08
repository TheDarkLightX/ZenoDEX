# ZenoDEX AB Child-Frontier Corpus-Root Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_corpus_root_scope_certificate_v1` admits the corpus-root research bundle only when the source report, n=7 zero-min scope, pinned corpus root, case roots, row receipts, membership checks, linked cross-binding digest, deterministic replay, negative controls, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `n7_zero_min_scope_ok` = `1`
- `corpus_root_pinned` = `1`
- `case_roots_covered` = `1`
- `row_receipts_complete` = `1`
- `membership_proofs_clean` = `1`
- `negative_controls_reject` = `1`
- `deterministic_replay_ok` = `1`
- `linked_cross_binding_ok` = `1`
- `digest_pins_ok` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`

## Corpus Pins

- Corpus root: `8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0`
- Case summaries digest: `afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28`
- Row receipts digest: `d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092`
- Linked cross-binding digest: `0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551`
- Deterministic replay hash: `b857b66aa96007bda748ae9489ee10f972248eaa30af25fd5ac7dffca73f4591`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `corpus_root_certificate_pass` | `True` | `1` |
| `missing_source_report_reject` | `True` | `0` |
| `wrong_scope_reject` | `True` | `0` |
| `wrong_corpus_root_reject` | `True` | `0` |
| `missing_case_roots_reject` | `True` | `0` |
| `missing_row_receipts_reject` | `True` | `0` |
| `membership_mismatch_reject` | `True` | `0` |
| `negative_controls_missing_reject` | `True` | `0` |
| `nondeterministic_replay_reject` | `True` | `0` |
| `linked_cross_binding_reject` | `True` | `0` |
| `digest_pin_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate is bounded to the committed n=7 zero-min corpus-root report.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not replace the host Merkle verifier.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_corpus_root_tau_certificate_20260629.py
```
