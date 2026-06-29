# ZenoDEX AB Child-Frontier Generated-Image Producer - 2026-06-29

## Executive Result

A bounded producer manifest now binds the n=7 child-frontier generated-image pipeline to ordered stages, script hashes, report hashes, output digests, cross-stage links, deterministic replay hashes, and a no-authority rail.

research-only producer-manifest evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority

## Producer Manifest

- Manifest hash: `5ed4c243e5c66637469f04f813301c171c44ff9e2d2d0a0b923eb8a1b7e5164f`
- Source seed: `2026062907`
- Stage order: `generation, canonical_merkle, witness_compression, witness_merkle_cross_binding, corpus_root`
- Stage replay enabled: `True`
- Stage replay ok: `True`
- Negative controls: `10`
- Negative control accepts: `0`

## Stage Outputs

| stage | script hash | deterministic hash | key outputs |
| --- | --- | --- | --- |
| `generation` | `647cc897c552253268f868c7c43885f08c01fa266c4f4487410449318fd8033b` | `8d698629548edaa62cf8e7367cb0845d8cf4efd1d5583e9997b8ec878d4b0925` | `frontier_rows_digest=b0536297bdec3e49204d98e4a52b4b43ea1467f7a32c2e184cf0bec07955fba4, child_mask_count=508, child_state_count=864, generated_state_count=864, predecessor_transition_count=2777, negative_control_count=7, negative_control_accept_count=0` |
| `canonical_merkle` | `a6ae402e0dd8d6814c6e58005ee532cffcff92a893be80b22b02c42e89a606ad` | `f86d378183d5f81c1ebd5e9d04610dc35cb0343f95ae99ba2e2df127d76c5ab5` | `frontier_roots_digest=42f3e7f10918fa3497183812cb316955c3382f4f3b4a4bb5309e47ec5855008b, membership_rows_digest=84cdbf4ebc62d758655f2ad253e541d072a7158f4c75bd939be521d613c84559, child_mask_count=508, child_state_count=864, membership_count=864, negative_control_count=8, negative_control_accept_count=0` |
| `witness_compression` | `15d83d36de5369efc5d7882e43f8e5648742a08813534699363cb1421ec0c57a` | `b6ee02a7ebb46e71229b8e75f194d712d7874f77dfc6caa2096c9dcd8fde3a62` | `witness_rows_digest=d689dd569b28abf3cb2636def322fa9d8185c2eb1fe4843bd83d07bce69138c3, child_mask_count=508, witness_count=864, covered_child_state_count=864, predecessor_transition_count=2777, witness_transition_checks_saved=1913, negative_control_count=8, negative_control_accept_count=0` |
| `witness_merkle_cross_binding` | `c9e6695fb81b1b1c8056ddb6e4e223771da5218bfe2469df8ca17e8fa6410150` | `9a94b98c560a2e191407a34e9fd1b3a7435cf2bb3cdd60c73227ece673031b31` | `bound_rows_digest=0996b976f70eeea56e4c828a9ff25abefdb8930b39896b4427291284e1e73551, child_mask_count=508, bound_row_count=864, witness_count=864, membership_count=864, negative_control_count=10, negative_control_accept_count=0` |
| `corpus_root` | `1a3d21c0e9def26ffbe7407da8f8b4825933fe550a1f235d0da3bf9436a32b80` | `b857b66aa96007bda748ae9489ee10f972248eaa30af25fd5ac7dffca73f4591` | `corpus_root=8f4a1a08cf51215cdc9fd382dd2538cc199db35b87597aa9c468358925dfd3b0, case_summaries_digest=afd7706fd7ea10cee0df44d7578dabf44fc82a26d238f814d717c5fee3b5bc28, row_receipts_digest=d52f8c24411e841ae777999d6bfd3ec3fef5bb0a26cd98887f4e0a5902c0f092, case_count=4, row_receipt_count=864, covered_row_receipt_count=864, negative_control_count=10, negative_control_accept_count=0` |

## Cross-Stage Links

- `canonical_frontier_digest_matches_generation` = `True`
- `witness_merkle_digest_matches_canonical` = `True`
- `witness_rows_digest_matches_witness_compression` = `True`
- `corpus_bound_rows_digest_matches_cross_binding` = `True`
- `corpus_row_count_matches_cross_binding` = `True`

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `manifest_hash_mismatch` | `False` | `manifest_hash_mismatch` |
| `producer_stage_order_mismatch` | `False` | `producer_stage_order_mismatch` |
| `stage_manifest_missing` | `False` | `stage_manifest_missing` |
| `source_seed_mismatch` | `False` | `generation_source_seed_mismatch` |
| `generation_script_hash_mismatch` | `False` | `generation_script_hash_mismatch` |
| `generation_report_hash_mismatch` | `False` | `generation_report_hash_mismatch` |
| `generation_output_digest_mismatch` | `False` | `generation_output_digest_mismatch` |
| `canonical_merkle_output_digest_mismatch` | `False` | `canonical_merkle_output_digest_mismatch` |
| `corpus_root_output_digest_mismatch` | `False` | `corpus_root_output_digest_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Non-Claims

- This producer manifest is bounded to the committed n=7 zero-min child-frontier corpus.
- This producer manifest does not prove Python-to-Lean refinement.
- This producer manifest does not prove child-frontier generation in Lean.
- This producer manifest does not cover nonzero min_amount_out behavior.
- This producer manifest does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_generated_image_producer_20260629.py
```
