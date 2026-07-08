# ZenoDEX AB Reserve-State Child-Frontier Witness-Compression N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_reserve_state_child_frontier_witness_compression_n8_sample_scope_certificate_v1` admits the sampled n=8 witness-compression research bundle only when the source report, sampled n=8 zero-min scope, witness coverage, compression metric, linked frontier summary, digest pins, deterministic replay, negative controls, normalized source hash, elapsed-ms normalization declaration, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `sampled_n8_zero_min_scope_ok` = `1`
- `witness_counts_complete` = `1`
- `compression_metrics_ok` = `1`
- `linked_frontier_ok` = `1`
- `witness_digest_pinned` = `1`
- `linked_frontier_digest_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `normalized_source_hash_pinned` = `1`
- `volatile_elapsed_ignored` = `1`

## Witness Pins

- Cases: `3`
- Sampled child masks: `51`
- Witness rows: `88`
- Covered sampled child states: `88`
- Predecessor transitions: `268`
- Checks saved: `180`
- Compression ratio: `3.045455`
- Normalized source report hash: `6196a6f82ac945218c77bdadbe5f7aade8022203756edc6779d98669cf10c91f`
- Witness digest: `4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd`
- Linked frontier digest: `37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919`
- Deterministic replay hash: `f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `witness_compression_n8_sample_certificate_pass` | `True` | `1` |
| `missing_source_report_reject` | `True` | `0` |
| `wrong_scope_reject` | `True` | `0` |
| `witness_counts_reject` | `True` | `0` |
| `compression_metrics_reject` | `True` | `0` |
| `linked_frontier_reject` | `True` | `0` |
| `witness_digest_reject` | `True` | `0` |
| `linked_frontier_digest_reject` | `True` | `0` |
| `nondeterministic_replay_reject` | `True` | `0` |
| `negative_controls_missing_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `normalized_source_hash_reject` | `True` | `0` |
| `volatile_elapsed_not_ignored_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min witness-compression report.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- The no-extra generated-state fact is linked to the sampled n=8 frontier report, not reproved by the one-witness object alone.
- This certificate does not define canonical tie order or preserve order-id history.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_witness_compression_n8_sample_tau_certificate_20260629.py
```
