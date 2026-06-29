# ZenoDEX AB Child-Frontier Generated-Image Producer N8 Sample - 2026-06-29

## Executive Result

A bounded producer manifest now binds the sampled n=8 child-frontier generated-image pipeline to ordered stages, script hashes, normalized report hashes, output digests, cross-stage links, deterministic replay hashes, and a no-authority rail.

research-only producer-manifest evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority

## Producer Manifest

- Manifest hash: `db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394`
- Source seed: `2026062908`
- Stage order: `generation, canonical_merkle, witness_compression, bidirectional_transition`
- Stage replay enabled: `True`
- Stage replay ok: `True`
- Negative controls: `11`
- Negative control accepts: `0`

## Stage Outputs

| stage | script hash | normalized report hash | deterministic hash | key outputs |
| --- | --- | --- | --- | --- |
| `generation` | `5ab65a27bed2258422b4e2930eefb928b2466da4e2ea814413a3709e2b989a34` | `9d486b78b9d6121f28728a7124f336f209ea9bb1517c3362897c62db1680021a` | `4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f` | `frontier_rows_digest=37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919, case_count=3, valid_case_count=3, sampled_child_mask_count=51, sampled_child_state_count=88, generated_state_count=88, missing_child_state_count=0, extra_generated_state_count=0, predecessor_transition_count=268, negative_control_count=7, negative_control_accept_count=0` |
| `canonical_merkle` | `49f61084552ab1bc74c10a5a257f37984718665e4cd6521949f6e964e62a4e0f` | `b4318b47670c43b4fce96e3cb5ed0b55cf2ad7a8dd4314ea04db95b7502b1f2a` | `31df88fd8d43c07cd20742854e8553e5b3ab5fef4259726f9968c8ff67293f43` | `frontier_roots_digest=53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4, membership_rows_digest=bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2, case_count=3, valid_case_count=3, frontier_root_count=51, sampled_child_mask_count=51, sampled_child_state_count=88, membership_count=88, covered_sampled_child_state_count=88, missing_frontier_row_count=0, missing_membership_proof_count=0, invalid_membership_proof_count=0, root_mismatch_count=0, negative_control_count=9, negative_control_accept_count=0` |
| `witness_compression` | `13e335e0a99916d01fdc9788f6bc97f30b63c0a80d66f11910985b71204c514e` | `65895d94ecd7c8c0807264e5db95a30a990ebbc1b9189777fb4192335ca790f6` | `f2946c81017d4b9102d20fd417c49fc821471606a4361a6550e4deddb4eb641d` | `witness_rows_digest=4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd, case_count=3, valid_case_count=3, sampled_child_mask_count=51, witness_count=88, covered_sampled_child_state_count=88, predecessor_transition_count=268, witness_transition_checks_saved=180, witness_compression_ratio=3.045455, missing_sampled_child_state_witness_count=0, extra_sampled_child_state_witness_count=0, invalid_witness_count=0, duplicate_witness_count=0, negative_control_count=9, negative_control_accept_count=0` |
| `bidirectional_transition` | `fd4378f8d3697a8b75e68c9f8ee8f1c25c875984472700a7ff30d7495add125d` | `91ee85516b795e953b36bb77d2b0c0bac216c42f74a4b3e01abd05a8527fd59a` | `5757702bcda71094a7b861318efdb7d1ea1e39d119677f3324e7e05ec12d939b` | `transition_rows_digest=0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09, case_count=3, valid_case_count=3, sampled_child_mask_count=51, transition_row_count=268, expected_transition_count=268, covered_transition_count=268, unique_transition_count=268, unique_generated_child_count=88, linked_child_coverage_witness_count=88, linked_canonical_membership_count=88, missing_transition_count=0, extra_transition_count=0, invalid_transition_row_count=0, duplicate_transition_row_count=0, negative_control_count=11, negative_control_accept_count=0` |

## Cross-Stage Links

- `canonical_frontier_digest_matches_generation` = `True`
- `witness_frontier_digest_matches_generation` = `True`
- `transition_witness_digest_matches_witness_compression` = `True`
- `transition_merkle_digest_matches_canonical` = `True`
- `transition_child_count_matches_generation` = `True`
- `transition_child_coverage_matches_witness` = `True`
- `transition_child_membership_matches_canonical` = `True`

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
| `witness_output_digest_mismatch` | `False` | `witness_compression_output_digest_mismatch` |
| `bidirectional_transition_output_digest_mismatch` | `False` | `bidirectional_transition_output_digest_mismatch` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Non-Claims

- This producer manifest is bounded to the deterministic sampled n=8 zero-min child-frontier corpus.
- This producer manifest does not prove exhaustive n=8 coverage.
- This producer manifest does not prove Python-to-Lean refinement.
- This producer manifest does not prove child-frontier generation in Lean.
- This producer manifest does not cover nonzero min_amount_out behavior.
- This producer manifest does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_generated_image_producer_n8_sample_20260629.py
```
