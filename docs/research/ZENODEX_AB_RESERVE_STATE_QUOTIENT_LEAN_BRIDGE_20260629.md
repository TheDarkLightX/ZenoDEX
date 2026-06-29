# AB Reserve-State Quotient Lean Bridge

Research-only proof component; no settlement, state-root, production, governance, routing, matching, or transaction authority.

## Claim Scope

A Lean proof component formalizes the reserve-state quotient bridge for the AB strict zero-min research surface: same reserve-state quotient rows have identical fixed-suffix behavior, and a selected minimum reserve-out state dominates a finite quotient family at fixed executed input. It also proves the selected representative remains valid after one common exact-in step is applied to every family member. The observed-summary layer binds host-visible count and selected-state metadata to the validated Lean table.

## Checks

- `lean_file_exists`: `True`
- `test_file_exists`: `True`
- `required_lean_markers_present`: `True`
- `required_test_markers_present`: `True`
- `lean_placeholder_scan_clean`: `True`

## Artifacts

- Lean file: `lean-mathlib/Proofs/ABReserveStateQuotient.lean`
- Lean SHA-256: `sha256:6caad3de4b12831fe40bd234d99fcaaf0e98060c05d2079b6b04130a88dec119`
- Lean line count: `637`
- Formal test: `tests/formal/test_lean_ab_reserve_state_quotient.py`
- Formal test SHA-256: `sha256:b6333d7b4ee0db18819aaeface7098939f68339b79c1274f581a3bfc55a4f2bb`

## Replay

- `cd lean-mathlib && lake env lean Proofs/ABReserveStateQuotient.lean`
- `cd lean-mathlib && lake build Proofs.ABReserveStateQuotient`
- `python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABReserveStateQuotient.lean`
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_reserve_state_quotient.py`
- `python3 tools/check_ab_reserve_state_quotient_lean_bridge.py`
- `python3 tools/check_public_claim_scope.py --root . --json`
- `python3 tools/check_claims_registry.py`

## Non-Claims

- No Python-to-Lean refinement proof is claimed.
- No JSON canonicalization or packet-hash computation is proved in Lean.
- No canonical tie order or order-history preservation is claimed.
- No nonzero min_amount_out coverage is claimed.
- No settlement, state-root, production, governance, routing, matching, or transaction authority is derived.
