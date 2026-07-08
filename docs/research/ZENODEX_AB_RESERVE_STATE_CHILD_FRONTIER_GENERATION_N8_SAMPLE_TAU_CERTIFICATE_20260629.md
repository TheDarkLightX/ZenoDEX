# ZenoDEX AB Reserve-State Child-Frontier Generation N8 Sample Tau Certificate - 2026-06-29

## Executive Result

`ab_reserve_state_child_frontier_generation_n8_sample_scope_certificate_v1` admits the sampled n=8 child-frontier generation research bundle only when the source report, sampled n=8 zero-min scope, sample plan, frontier equality counts, predecessor transition counts, generated-state equality, digest pins, deterministic replay, negative controls, Lean projection declaration, normalized source hash, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `source_report_ok` = `1`
- `sampled_n8_zero_min_scope_ok` = `1`
- `sample_plan_pinned` = `1`
- `frontier_counts_ok` = `1`
- `predecessor_counts_ok` = `1`
- `state_counts_ok` = `1`
- `generation_clean` = `1`
- `frontier_rows_digest_pinned` = `1`
- `deterministic_replay_ok` = `1`
- `negative_controls_reject` = `1`
- `lean_contract_pinned` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `normalized_source_hash_pinned` = `1`
- `hash_normalization_declared` = `1`

## Generation Corpus

- Normalized source hash: `9d486b78b9d6121f28728a7124f336f209ea9bb1517c3362897c62db1680021a`
- Source seed: `2026062908`
- Sampled child masks: `51`
- Frontier equalities: `51`
- Predecessor edges: `144`
- Predecessor transitions: `268`
- Executable predecessor transitions: `268`
- Sampled child states: `88`
- Generated states: `88`
- Missing child states: `0`
- Extra generated states: `0`
- Frontier rows digest: `37764c62caa78be76d654ec1f2540babe2aae2f546663f6548f2d9a1da85b919`
- Deterministic replay hash: `4a601edd060a6cfe8444d7db91f1806bf8bf42b07943642de7dd299e76aa877f`
- Negative controls: `7`
- Negative control accepts: `0`
- Tau cases: `18`
- Invalid accepts: `0`

## Tau Cases

| case | ok | o7 | rationale |
| --- | ---: | ---: | --- |
| `generation_n8_sample_certificate_pass` | `True` | `1` | All scoped host facts admit the sampled n=8 generation certificate. |
| `missing_source_report_reject` | `True` | `0` | The `source_report_ok` host fact is required for certificate admission. |
| `wrong_scope_reject` | `True` | `0` | The `sampled_n8_zero_min_scope_ok` host fact is required for certificate admission. |
| `sample_plan_reject` | `True` | `0` | The `sample_plan_pinned` host fact is required for certificate admission. |
| `frontier_counts_reject` | `True` | `0` | The `frontier_counts_ok` host fact is required for certificate admission. |
| `predecessor_counts_reject` | `True` | `0` | The `predecessor_counts_ok` host fact is required for certificate admission. |
| `state_counts_reject` | `True` | `0` | The `state_counts_ok` host fact is required for certificate admission. |
| `generation_clean_reject` | `True` | `0` | The `generation_clean` host fact is required for certificate admission. |
| `frontier_digest_reject` | `True` | `0` | The `frontier_rows_digest_pinned` host fact is required for certificate admission. |
| `nondeterministic_replay_reject` | `True` | `0` | The `deterministic_replay_ok` host fact is required for certificate admission. |
| `negative_controls_missing_reject` | `True` | `0` | The `negative_controls_reject` host fact is required for certificate admission. |
| `lean_contract_reject` | `True` | `0` | The `lean_contract_pinned` host fact is required for certificate admission. |
| `authority_boundary_reject` | `True` | `0` | The `authority_boundary_ok` host fact is required for certificate admission. |
| `authority_effect_reject` | `True` | `0` | The `no_authority_effect` host fact is required for certificate admission. |
| `empty_corpus_reject` | `True` | `0` | The `corpus_nonvacuous` host fact is required for certificate admission. |
| `source_hash_reject` | `True` | `0` | The `normalized_source_hash_pinned` host fact is required for certificate admission. |
| `hash_normalization_reject` | `True` | `0` | The `hash_normalization_declared` host fact is required for certificate admission. |
| `inactive_safe` | `True` | `0` | Inactive certificates do not admit while the no-authority rail remains true. |

## Non-Claims

- This certificate is bounded to the deterministic sampled n=8 zero-min generation report.
- This certificate uses a normalized source hash that strips elapsed_ms fields.
- This certificate does not prove exhaustive n=8 coverage.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove child-frontier generation in Lean.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not define canonical tie order or preserve order-id history.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_reserve_state_child_frontier_generation_n8_sample_tau_certificate_20260629.py
```
