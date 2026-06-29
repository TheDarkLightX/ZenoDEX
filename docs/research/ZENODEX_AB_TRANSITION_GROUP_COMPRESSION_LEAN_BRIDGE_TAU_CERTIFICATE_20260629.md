# ZenoDEX AB Transition-Group Compression Lean-Bridge Tau Certificate - 2026-06-29

## Executive Result

`ab_transition_group_compression_lean_bridge_scope_certificate_v1` admits the Lean bridge research bundle only when the Lean bridge report, pinned Lean/test artifacts, theorem-surface markers, placeholder scan, Lean compile receipt, focused formal test receipt, upstream compression Tau certificate binding, replay-command surface, non-claims, and no-authority rail are all present.

Research-only evidence. No settlement, state-root, production, governance, routing, matching, or pool-mutation authority is derived from this artifact.

## Facts

- `lean_bridge_report_ok` = `1`
- `lean_file_pinned` = `1`
- `aggregator_import_bound` = `1`
- `theorem_surface_bound` = `1`
- `placeholder_scan_clean` = `1`
- `lean_compile_receipt_ok` = `1`
- `formal_test_receipt_ok` = `1`
- `upstream_compression_tau_binding_ok` = `1`
- `nonclaims_bound` = `1`
- `authority_boundary_ok` = `1`
- `no_authority_effect` = `1`
- `corpus_nonvacuous` = `1`
- `replay_commands_bound` = `1`

## Artifact Pins

- Lean bridge report hash: `ce267d142cbbf67ebcfd31580f9c12852d19f7700547db5418472a31ceaac5f1`
- Lean file: `lean-mathlib/Proofs/ABTransitionGroupCompression.lean`
- Lean SHA-256: `sha256:71b6325c1db9cde527a9c26e7b53f76d56d1b9f4cedb79079e8ade98f3c57d98`
- Required Lean markers: `14`
- Formal test SHA-256: `sha256:32244a83355331c366a0f9b6d80800a7ba48499aff190f5f923067404c733dd0`
- Upstream compression Tau report hash: `9ca5e4b8ab6f368d1fdd00347e5ca734ee6841f769891488e5fb43dfa591a7d2`
- Upstream source rows: `2777`
- Upstream compressed rows: `864`

## Receipts

- Lean compile ok: `True`
- Formal test ok: `True`
- Tau ok: `True`
- Tau invalid accepts: `0`

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `lean_bridge_scope_certificate_pass` | `True` | `1` |
| `missing_lean_bridge_report_reject` | `True` | `0` |
| `lean_file_unpinned_reject` | `True` | `0` |
| `aggregator_import_missing_reject` | `True` | `0` |
| `theorem_surface_unbound_reject` | `True` | `0` |
| `placeholder_scan_failed_reject` | `True` | `0` |
| `lean_compile_missing_reject` | `True` | `0` |
| `formal_test_missing_reject` | `True` | `0` |
| `upstream_compression_tau_unbound_reject` | `True` | `0` |
| `nonclaims_missing_reject` | `True` | `0` |
| `authority_boundary_missing_reject` | `True` | `0` |
| `authority_effect_reject` | `True` | `0` |
| `empty_corpus_reject` | `True` | `0` |
| `replay_commands_unbound_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate composes host facts; it does not run Lean inside Tau.
- This certificate does not prove Python-to-Lean refinement.
- This certificate does not prove JSON canonicalization, packet hashing, Merkle membership, or digest computation in Lean.
- This certificate does not prove host generated-image construction.
- This certificate does not cover nonzero min_amount_out behavior.
- This certificate does not authorize settlement, routing, matching, governance, pool mutation, production deployment, or state roots.

## Replay

```bash
python3 tools/check_ab_transition_group_compression_lean_bridge_tau_certificate_20260629.py
```
