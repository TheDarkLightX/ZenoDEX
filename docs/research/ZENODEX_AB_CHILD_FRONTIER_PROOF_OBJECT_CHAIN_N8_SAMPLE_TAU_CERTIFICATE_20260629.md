# ZenoDEX AB Child-Frontier Proof-Object Chain N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_child_frontier_proof_object_chain_n8_sample_scope_certificate_v1` admits the sampled n=8 proof-object chain only when the generation, canonical-Merkle, witness-compression, bidirectional-transition, and producer Tau reports all pass; shared counts and cross-stage digests agree; the producer manifest links are intact; the deterministic chain index is hash-pinned; and the no-authority rail is present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `generation_tau_ok` = `1`
- `canonical_merkle_tau_ok` = `1`
- `witness_compression_tau_ok` = `1`
- `bidirectional_transition_tau_ok` = `1`
- `producer_tau_ok` = `1`
- `shared_scope_ok` = `1`
- `stage_counts_ok` = `1`
- `cross_stage_digests_ok` = `1`
- `producer_manifest_links_ok` = `1`
- `negative_cases_clean` = `1`
- `deterministic_replay_pinned` = `1`
- `stage_report_hashes_pinned` = `1`
- `chain_index_hash_pinned` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`

## Chain Summary

- Stage Tau reports: `5`
- Sampled child masks: `51`
- Sampled child states: `88`
- Predecessor transitions: `268`
- Chain index hash: `7f6d4c6e21fe5118485de7094b27994a5fee96bc6f2db3c4273374d64ef159bb`
- Expected chain index hash: `7f6d4c6e21fe5118485de7094b27994a5fee96bc6f2db3c4273374d64ef159bb`
- Tau cases: `18`
- Invalid accepts: `0`

## Stage Reports

| stage | tau ok | tau cases | invalid accepts | report sha256 |
| --- | ---: | ---: | ---: | --- |
| `generation` | `True` | `18` | `0` | `8367a2bbc4f51cb18553102b7c318ba843d88e4e0a1ce9566a99c4707ca42f94` |
| `canonical_merkle` | `True` | `17` | `0` | `4dde23987a628b6e1c9e20da0eed3e1f615b962cb60a25e5ac8f3e06d8e15b91` |
| `witness_compression` | `True` | `16` | `0` | `994fd65edc822e648908090e14e312b626e7eb2d9bcd1066afcc054f43f2ae3b` |
| `bidirectional_transition` | `True` | `17` | `0` | `ca27f7e99c48cd067b8a43bf8e45df4f26cfca80b25953ae4632b404a66c6989` |
| `producer` | `True` | `20` | `0` | `1953a186822cc19b205a144415c02436fbe38bb9409762b30ae48c58a0ba3a27` |

## Chain Digests

- `generation_frontier_rows_digest` = `37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919`
- `canonical_frontier_roots_digest` = `53872b495fd6af55f5192e5577f6fb75fca8bd54c26110ff88f4b11a17edf6d4`
- `canonical_membership_rows_digest` = `bf859719c54893c3975b5f28a9eda8dc58b50b1bcab8ed46cd96fd5f4d63a5d2`
- `witness_rows_digest` = `4851b651740dcfaaa5b175cccbc0907fb7449ff3c4e14db61c3cdafed72e52dd`
- `transition_rows_digest` = `0ed918d2b332430f57bf3561a5912fa50c0293c23661ff02f582a21e88f3ed09`
- `producer_manifest_hash` = `db94660eb8c859821de08b629371e3c056b2469d707b94df56854a5f41f17394`

## Tau Cases

| case | ok | o7 | rationale |
| --- | ---: | ---: | --- |
| `proof_object_chain_n8_sample_certificate_pass` | `True` | `1` | All scoped stage Tau reports and chain links admit the sampled n=8 proof-object chain certificate. |
| `generation_tau_reject` | `True` | `0` | The `generation_tau_ok` host fact is required for chain certificate admission. |
| `canonical_merkle_tau_reject` | `True` | `0` | The `canonical_merkle_tau_ok` host fact is required for chain certificate admission. |
| `witness_compression_tau_reject` | `True` | `0` | The `witness_compression_tau_ok` host fact is required for chain certificate admission. |
| `bidirectional_transition_tau_reject` | `True` | `0` | The `bidirectional_transition_tau_ok` host fact is required for chain certificate admission. |
| `producer_tau_reject` | `True` | `0` | The `producer_tau_ok` host fact is required for chain certificate admission. |
| `shared_scope_reject` | `True` | `0` | The `shared_scope_ok` host fact is required for chain certificate admission. |
| `stage_counts_reject` | `True` | `0` | The `stage_counts_ok` host fact is required for chain certificate admission. |
| `cross_stage_digest_reject` | `True` | `0` | The `cross_stage_digests_ok` host fact is required for chain certificate admission. |
| `producer_links_reject` | `True` | `0` | The `producer_manifest_links_ok` host fact is required for chain certificate admission. |
| `negative_cases_reject` | `True` | `0` | The `negative_cases_clean` host fact is required for chain certificate admission. |
| `deterministic_replay_reject` | `True` | `0` | The `deterministic_replay_pinned` host fact is required for chain certificate admission. |
| `stage_report_hash_reject` | `True` | `0` | The `stage_report_hashes_pinned` host fact is required for chain certificate admission. |
| `chain_index_hash_reject` | `True` | `0` | The `chain_index_hash_pinned` host fact is required for chain certificate admission. |
| `authority_boundary_reject` | `True` | `0` | The `authority_boundary_ok` host fact is required for chain certificate admission. |
| `authority_effect_reject` | `True` | `0` | The `no_authority_effect` host fact is required for chain certificate admission. |
| `empty_corpus_reject` | `True` | `0` | The `corpus_nonvacuous` host fact is required for chain certificate admission. |
| `inactive_safe` | `True` | `0` | Inactive certificates do not admit while the no-authority rail remains true. |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min proof-object chain reports.
- This certificate composes existing stage Tau reports and producer manifest evidence; it does not replace those host checkers.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not define canonical tie order or preserve order-id history.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_child_frontier_proof_object_chain_n8_sample_tau_certificate_20260629.py
```
