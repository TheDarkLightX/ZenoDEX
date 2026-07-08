# ZenoDEX AB Child-Frontier Bidirectional Transition Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_bidirectional_transition_scope_certificate_v1` admits the bidirectional transition research bundle only when the source report, n=7 zero-min scope, transition-row coverage, generated-child count, linked child-coverage evidence, digest pins, deterministic replay, negative controls, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `n7_zero_min_scope_ok` = `1`
- `transition_counts_complete` = `1`
- `generated_child_count_ok` = `1`
- `linked_child_coverage_ok` = `1`
- `transition_digest_pinned` = `1`
- `linked_digest_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`

## Transition Pins

- Transition rows: `2777`
- Expected transitions: `2777`
- Covered transitions: `2777`
- Unique generated child states: `864`
- Linked child coverage witnesses: `864`
- Transition digest: `fccc26b63521b510776546e4663cecabcf58849af42bcda799484bf092a81f82`
- Linked witness+Merkle digest: `0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551`
- Deterministic replay hash: `54e80016a0c0dc4eb629d22b43265091b3b1c4dc75324320107b17dbd42668b7`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `bidirectional_transition_certificate_pass` | `True` | `1` |
| `missing_source_report_reject` | `True` | `0` |
| `wrong_scope_reject` | `True` | `0` |
| `transition_counts_reject` | `True` | `0` |
| `generated_child_count_reject` | `True` | `0` |
| `linked_child_coverage_reject` | `True` | `0` |
| `transition_digest_reject` | `True` | `0` |
| `linked_digest_reject` | `True` | `0` |
| `nondeterministic_replay_reject` | `True` | `0` |
| `negative_controls_missing_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate is bounded to the committed n=7 zero-min bidirectional transition report.
- This certificate links the child coverage direction to the existing witness+Merkle report.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not replace the host Merkle verifier or transition checker.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_bidirectional_transition_tau_certificate_20260629.py
```
