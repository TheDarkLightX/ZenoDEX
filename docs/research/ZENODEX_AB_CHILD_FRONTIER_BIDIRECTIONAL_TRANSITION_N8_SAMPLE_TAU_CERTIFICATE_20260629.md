# ZenoDEX AB Child-Frontier Bidirectional Transition N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_bidirectional_transition_n8_sample_scope_certificate_v1` admits the sampled n=8 bidirectional transition research bundle only when the source report, sampled n=8 zero-min scope, transition-row coverage, generated-child count, linked predecessor-witness evidence, linked canonical-Merkle evidence, digest pins, deterministic replay, negative controls, source hash, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `sampled_n8_zero_min_scope_ok` = `1`
- `transition_counts_complete` = `1`
- `generated_child_count_ok` = `1`
- `linked_child_coverage_ok` = `1`
- `linked_canonical_membership_ok` = `1`
- `transition_digest_pinned` = `1`
- `linked_witness_digest_pinned` = `1`
- `linked_merkle_digest_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `source_report_hash_pinned` = `1`

## Transition Pins

- Cases: `3`
- Sampled child masks: `51`
- Transition rows: `268`
- Expected transitions: `268`
- Covered transitions: `268`
- Unique generated child states: `88`
- Linked predecessor witnesses: `88`
- Linked canonical memberships: `88`
- Source report hash: `de633b40c90942b466750a24b76b6379a5a3322d54925c1801a2f5dbd8b0fd24`
- Transition digest: `0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09`
- Linked witness digest: `4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd`
- Linked Merkle membership digest: `bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2`
- Deterministic replay hash: `5757702bcda71094a7b861318efdb7d1ea1e39d119677f3324e7e05ec12d939b`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `bidirectional_transition_n8_sample_certificate_pass` | `True` | `1` |
| `missing_source_report_reject` | `True` | `0` |
| `wrong_scope_reject` | `True` | `0` |
| `transition_counts_reject` | `True` | `0` |
| `generated_child_count_reject` | `True` | `0` |
| `linked_child_coverage_reject` | `True` | `0` |
| `linked_canonical_membership_reject` | `True` | `0` |
| `transition_digest_reject` | `True` | `0` |
| `linked_witness_digest_reject` | `True` | `0` |
| `linked_merkle_digest_reject` | `True` | `0` |
| `nondeterministic_replay_reject` | `True` | `0` |
| `negative_controls_missing_reject` | `True` | `0` |
| `authority_boundary_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `source_hash_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min bidirectional transition report.
- This certificate links predecessor-witness and canonical-Merkle evidence produced by separate host checkers.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not replace the host Merkle verifier or transition checker.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_bidirectional_transition_n8_sample_tau_certificate_20260629.py
```
