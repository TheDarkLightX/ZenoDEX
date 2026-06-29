# AB Reserve-State Quotient Lean Bridge

Research-only proof component; no settlement, state-root, production, governance, routing, matching, or transaction authority.

## Claim Scope

A Lean proof component formalizes the reserve-state quotient bridge for the AB strict zero-min research surface: same reserve-state quotient rows have identical fixed-suffix behavior, and a selected minimum reserve-out state dominates a finite quotient family at fixed executed input.

## Checks

- `lean_file_exists`: `True`
- `test_file_exists`: `True`
- `required_lean_markers_present`: `True`
- `required_test_markers_present`: `True`
- `lean_placeholder_scan_clean`: `True`

## Artifacts

- Lean file: `lean-mathlib/Proofs/ABReserveStateQuotient.lean`
- Lean SHA-256: `sha256:ef2b28779aff711e411ae27da39146c51587707658056a36ee43d74181f36225`
- Lean line count: `341`
- Formal test: `tests/formal/test_lean_ab_reserve_state_quotient.py`
- Formal test SHA-256: `sha256:7207b6d0788d76b328d413b46c8ba011569ccc5371247c9efb8d389a54f53c3a`

## Replay

- `cd lean-mathlib && lake env lean Proofs/ABReserveStateQuotient.lean`
- `python3 ~/.codex/skills/proof-engineering/scripts/scan_proof_placeholders.py lean-mathlib/Proofs/ABReserveStateQuotient.lean`
- `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/formal/test_lean_ab_reserve_state_quotient.py`
- `python3 tools/check_ab_reserve_state_quotient_lean_bridge.py`

## Non-Claims

- No Python-to-Lean refinement proof is claimed.
- No JSON canonicalization or packet-hash computation is proved in Lean.
- No canonical tie order or order-history preservation is claimed.
- No nonzero min_amount_out coverage is claimed.
- No settlement, state-root, production, governance, routing, matching, or transaction authority is derived.
