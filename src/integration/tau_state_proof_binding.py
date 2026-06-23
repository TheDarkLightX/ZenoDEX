from __future__ import annotations

from typing import Any, Mapping, Optional, Tuple


def _require_hash(value: Any, *, name: str) -> Tuple[bool, str]:
    if not isinstance(value, str):
        return False, f"{name} must be a string"
    normalized = value[2:] if value.startswith("0x") else value
    if len(normalized) != 64:
        return False, f"{name} must be 64 hex chars"
    try:
        int(normalized, 16)
    except ValueError:
        return False, f"{name} must be valid hex"
    return True, normalized.lower()


def validate_tau_state_proof_binding(
    *,
    state_proof: Mapping[str, Any],
    committed_state_hash: str,
    committed_app_hash: Optional[str],
    tau_state: Optional[Mapping[str, Any]] = None,
) -> Tuple[bool, Optional[str]]:
    """Validate that state-proof presence is bound to the committed Tau/app state.

    This helper is deliberately small so future Tau registry/snapshot loaders can
    call it before accepting a `state_proof.present` flag as authority.
    """
    if state_proof.get("present") is not True:
        return False, "state_proof.present must be true"

    ok, expected_state_hash = _require_hash(committed_state_hash, name="committed_state_hash")
    if not ok:
        return False, expected_state_hash

    proof_state_hash_raw = state_proof.get("state_hash")
    if proof_state_hash_raw is None and isinstance(state_proof.get("proof"), Mapping):
        proof_state_hash_raw = state_proof["proof"].get("state_hash")
    ok, proof_state_hash = _require_hash(proof_state_hash_raw, name="state_proof.state_hash")
    if not ok:
        return False, proof_state_hash
    if proof_state_hash != expected_state_hash:
        return False, "state_proof.state_hash does not match committed state_hash"

    if committed_app_hash is None or committed_app_hash == "":
        return True, None

    ok, expected_app_hash = _require_hash(committed_app_hash, name="committed_app_hash")
    if not ok:
        return False, expected_app_hash

    app_hash_raw = None
    if tau_state is not None:
        app_hash_raw = tau_state.get("app_hash")
    if app_hash_raw is None:
        app_hash_raw = state_proof.get("app_hash")
    if app_hash_raw is None:
        return False, "state_proof must bind committed app_hash or provide validated tau_state.app_hash"

    ok, proof_app_hash = _require_hash(app_hash_raw, name="state_proof.app_hash")
    if not ok:
        return False, proof_app_hash
    if proof_app_hash != expected_app_hash:
        return False, "state_proof app_hash does not match committed app_hash"
    return True, None
