# ZenoDEX AB Child-Frontier Transition-Group Compression Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_transition_group_compression_scope_certificate_v1` admits the compression research bundle only when the compression report, source bidirectional binding, n=7 zero-min scope, aggregate reductions, group coverage, digest pins, deterministic replay, negative controls, case-row pins, host-recomputation non-claim, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `compression_report_ok` = `1`
- `n7_zero_min_scope_ok` = `1`
- `source_bidirectional_binding_ok` = `1`
- `compression_counts_ok` = `1`
- `generated_group_coverage_ok` = `1`
- `compression_digests_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `case_rows_bound` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `host_recomputation_nonclaim_bound` = `1`

## Compression Pins

- Source transition rows: `2777`
- Compressed rows: `864`
- Row reduction: `1913` (`0.688873`)
- Source JSON bytes: `2296999`
- Compressed JSON bytes: `841376`
- Byte reduction: `1455623` (`0.633706`)
- Expected groups: `864`
- Covered groups: `864`
- Transition-group digest: `280c2b23775977485dd12bd7a7b8c3db1c023577881fd1580b1210912261939b`
- Compressed-row digest: `08588cdb923ad12571dc729b13ad99b2888bebe8e5d6983fabd723b32d2bb2a4`
- Deterministic replay hash: `695be84aeee82b4f61706786bd08a16c9f8b16c47b2a0e2739e6cadaffbc5f83`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `transition_group_compression_certificate_pass` | `True` | `1` |
| `missing_compression_report_reject` | `True` | `0` |
| `wrong_scope_reject` | `True` | `0` |
| `source_bidirectional_binding_reject` | `True` | `0` |
| `compression_counts_reject` | `True` | `0` |
| `generated_group_coverage_reject` | `True` | `0` |
| `compression_digest_reject` | `True` | `0` |
| `nondeterministic_replay_reject` | `True` | `0` |
| `negative_controls_missing_reject` | `True` | `0` |
| `case_rows_unbound_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `host_recomputation_nonclaim_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate is bounded to the committed n=7 zero-min transition-group compression report.
- This certificate composes host facts; it does not recompute transition groups in Tau.
- This certificate does not remove host recomputation of the transition image.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_transition_group_compression_tau_certificate_20260629.py
```
