# AB Transition-Group Compression Lean Bridge

Research-only proof component; no settlement, state-root, production, governance, routing, matching, pool-mutation, or transaction authority.

## Claim Scope

A Lean proof component formalizes the generic transition-group compression invariant for the AB strict zero-min research surface. If host-provided compressed groups cover every source transition, contain no extra transitions, bind representatives and group counts, and every group member shares its generated-child key, then the compressed generated-child image is exactly the source transition generated-child image. The endpoint also preserves the no-authority host-table rails.

## Checks

- `lean_file_exists`: `True`
- `aggregator_import_present`: `True`
- `test_file_exists`: `True`
- `required_lean_markers_present`: `True`
- `required_test_markers_present`: `True`
- `lean_placeholder_scan_clean`: `True`

## Artifacts

- Lean file: `lean-mathlib/Proofs/ABTransitionGroupCompression.lean`
- Lean SHA-256: `sha256:71b6325c1db9cde527a9c26e7b53f76d56d1b9f4cedb79079e8ade98f3c57d98`
- Lean line count: `259`
- Formal test: `tests/formal/test_lean_ab_transition_group_compression.py`
- Formal test SHA-256: `sha256:32244a83355331c366a0f9b6d80800a7ba48499aff190f5f923067404c733dd0`

## Replay

- `cd lean-mathlib && lake env lean Proofs/ABTransitionGroupCompression.lean`
- `cd lean-mathlib && lake build Proofs.ABTransitionGroupCompression`
- `python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABTransitionGroupCompression.lean`
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_transition_group_compression.py`
- `python3 tools/check_ab_transition_group_compression_lean_bridge_20260629.py`
- `python3 tools/check_public_claim_scope.py --root . --json`
- `python3 tools/check_claims_registry.py`

## Non-Claims

- No Python-to-Lean refinement proof is claimed.
- No JSON canonicalization, packet hashing, Merkle membership, or digest computation is proved in Lean.
- No host generated-image construction proof is claimed.
- No nonzero min_amount_out coverage is claimed.
- No settlement, state-root, production, governance, routing, matching, pool-mutation, or transaction authority is derived.
