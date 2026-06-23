from __future__ import annotations

from pathlib import Path

from src.integration.tau_state_proof_binding import validate_tau_state_proof_binding


ROOT_DIR = Path(__file__).resolve().parents[2]


def test_state_proof_presence_requires_state_hash_and_app_hash_binding() -> None:
    state_hash = "11" * 32
    app_hash = "22" * 32

    ok, err = validate_tau_state_proof_binding(
        state_proof={"present": True, "state_hash": state_hash},
        committed_state_hash=state_hash,
        committed_app_hash=app_hash,
    )
    assert ok is False
    assert err == "state_proof must bind committed app_hash or provide validated tau_state.app_hash"

    ok, err = validate_tau_state_proof_binding(
        state_proof={"present": True, "state_hash": "33" * 32, "app_hash": app_hash},
        committed_state_hash=state_hash,
        committed_app_hash=app_hash,
    )
    assert ok is False
    assert err == "state_proof.state_hash does not match committed state_hash"

    ok, err = validate_tau_state_proof_binding(
        state_proof={"present": True, "state_hash": state_hash, "app_hash": "44" * 32},
        committed_state_hash=state_hash,
        committed_app_hash=app_hash,
    )
    assert ok is False
    assert err == "state_proof app_hash does not match committed app_hash"

    ok, err = validate_tau_state_proof_binding(
        state_proof={"present": True, "state_hash": state_hash},
        committed_state_hash=state_hash,
        committed_app_hash=app_hash,
        tau_state={"app_hash": app_hash},
    )
    assert ok is True
    assert err is None


def test_tau_signer_registry_loader_is_not_reintroduced_without_binding_helper() -> None:
    loader_path = ROOT_DIR / "src" / "integration" / "settlement_signer_registry.py"
    if not loader_path.exists():
        for path in (ROOT_DIR / "src").rglob("*.py"):
            text = path.read_text(encoding="utf-8", errors="ignore")
            assert "TauNetSettlementSignerRegistrySnapshotLoader" not in text
        return

    source = loader_path.read_text(encoding="utf-8", errors="ignore")
    assert "TauNetSettlementSignerRegistrySnapshotLoader" not in source or "validate_tau_state_proof_binding" in source
