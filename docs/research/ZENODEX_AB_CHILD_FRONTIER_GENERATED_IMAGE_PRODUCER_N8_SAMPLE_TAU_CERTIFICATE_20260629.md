# ZenoDEX AB Child-Frontier Generated-Image Producer N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_generated_image_producer_n8_sample_scope_certificate_v1` admits the sampled n=8 producer-manifest research bundle only when the source report, sampled n=8 zero-min scope, stage order, stage hashes, stage outputs, stage replay, cross-stage links, source seed, manifest hash, digest pins, negative controls, source hash, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `sampled_n8_zero_min_scope_ok` = `1`
- `producer_stage_order_ok` = `1`
- `stage_hashes_pinned` = `1`
- `stage_outputs_pinned` = `1`
- `stage_replay_ok` = `1`
- `cross_stage_links_ok` = `1`
- `source_seed_pinned` = `1`
- `manifest_hash_pinned` = `1`
- `generation_digest_pinned` = `1`
- `canonical_digest_pinned` = `1`
- `witness_digest_pinned` = `1`
- `transition_digest_pinned` = `1`
- `negative_controls_reject` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `source_report_hash_pinned` = `1`

## Producer Manifest

- Source report hash: `1989c0862510d5c93177c58999368bafb49542f23bd4c3c9e73cfac95b2cf73e`
- Manifest hash: `db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394`
- Source seed: `2026062908`
- Stage count: `4`
- Tau cases: `20`
- Invalid accepts: `0`
- Negative controls: `11`
- Negative control accepts: `0`

## Digest Pins

- `generation_frontier_rows_digest` = `37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919`
- `canonical_membership_rows_digest` = `bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2`
- `witness_rows_digest` = `4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd`
- `transition_rows_digest` = `0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09`

## Tau Cases

| case | ok | o7 | rationale |
| --- | ---: | ---: | --- |
| `generated_image_producer_n8_sample_certificate_pass` | `True` | `1` | All scoped host facts admit the sampled n=8 generated-image producer manifest. |
| `missing_source_report_reject` | `True` | `0` | The `source_report_ok` host fact is required for certificate admission. |
| `wrong_scope_reject` | `True` | `0` | The `sampled_n8_zero_min_scope_ok` host fact is required for certificate admission. |
| `stage_order_reject` | `True` | `0` | The `producer_stage_order_ok` host fact is required for certificate admission. |
| `stage_hashes_reject` | `True` | `0` | The `stage_hashes_pinned` host fact is required for certificate admission. |
| `stage_outputs_reject` | `True` | `0` | The `stage_outputs_pinned` host fact is required for certificate admission. |
| `stage_replay_reject` | `True` | `0` | The `stage_replay_ok` host fact is required for certificate admission. |
| `cross_stage_links_reject` | `True` | `0` | The `cross_stage_links_ok` host fact is required for certificate admission. |
| `source_seed_reject` | `True` | `0` | The `source_seed_pinned` host fact is required for certificate admission. |
| `manifest_hash_reject` | `True` | `0` | The `manifest_hash_pinned` host fact is required for certificate admission. |
| `generation_digest_reject` | `True` | `0` | The `generation_digest_pinned` host fact is required for certificate admission. |
| `canonical_digest_reject` | `True` | `0` | The `canonical_digest_pinned` host fact is required for certificate admission. |
| `witness_digest_reject` | `True` | `0` | The `witness_digest_pinned` host fact is required for certificate admission. |
| `transition_digest_reject` | `True` | `0` | The `transition_digest_pinned` host fact is required for certificate admission. |
| `negative_controls_missing_reject` | `True` | `0` | The `negative_controls_reject` host fact is required for certificate admission. |
| `authority_boundary_reject` | `True` | `0` | The `authority_boundary_ok` host fact is required for certificate admission. |
| `authority_effect_reject` | `True` | `0` | The `no_authority_effect` host fact is required for certificate admission. |
| `empty_corpus_reject` | `True` | `0` | The `corpus_nonvacuous` host fact is required for certificate admission. |
| `source_hash_reject` | `True` | `0` | The `source_report_hash_pinned` host fact is required for certificate admission. |
| `inactive_safe` | `True` | `0` | Inactive certificates do not admit while the no-authority rail remains true. |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min producer-manifest report.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not replace the host producer, Merkle verifier, witness checker, or transition checker.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_generated_image_producer_n8_sample_tau_certificate_20260629.py
```
