from __future__ import annotations

import pytest

from src.kernels.python.strategy_live_admission_bundle_v1_adapter import (
    check_strategy_live_admission_bundle,
)


def test_check_strategy_live_admission_bundle_accepts_all_green() -> None:
    result = check_strategy_live_admission_bundle(
        source_registry_ok=True,
        signal_provenance_ok=True,
        route_economic_sanity_ok=True,
        execution_ok=True,
        oracle_freshness_ok=True,
        budget_ok=True,
        tx_envelope_ok=True,
        session_state_ok=True,
        session_capability_binding_ok=True,
        wallet_capability_ok=True,
        nonce_ok=True,
    )
    assert result.ok is True
    assert result.error is None


@pytest.mark.parametrize(
    ("field", "error"),
    [
        ("source_registry_ok", "source_registry_rejected"),
        ("signal_provenance_ok", "signal_provenance_rejected"),
        ("route_economic_sanity_ok", "route_economic_sanity_rejected"),
        ("execution_ok", "execution_rejected"),
        ("oracle_freshness_ok", "oracle_freshness_rejected"),
        ("budget_ok", "budget_rejected"),
        ("tx_envelope_ok", "tx_envelope_rejected"),
        ("session_state_ok", "session_state_rejected"),
        ("session_capability_binding_ok", "session_capability_binding_rejected"),
        ("wallet_capability_ok", "wallet_capability_rejected"),
        ("nonce_ok", "nonce_rejected"),
    ],
)
def test_check_strategy_live_admission_bundle_rejects_first_failing_guard(
    field: str,
    error: str,
) -> None:
    kwargs = {
        "source_registry_ok": True,
        "signal_provenance_ok": True,
        "route_economic_sanity_ok": True,
        "execution_ok": True,
        "oracle_freshness_ok": True,
        "budget_ok": True,
        "tx_envelope_ok": True,
        "session_state_ok": True,
        "session_capability_binding_ok": True,
        "wallet_capability_ok": True,
        "nonce_ok": True,
    }
    kwargs[field] = False
    result = check_strategy_live_admission_bundle(**kwargs)
    assert result.ok is False
    assert result.error == error


def test_check_strategy_live_admission_bundle_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="signal_provenance_ok must be a bool"):
        check_strategy_live_admission_bundle(
            source_registry_ok=True,
            signal_provenance_ok=1,
            route_economic_sanity_ok=True,
            execution_ok=True,
            oracle_freshness_ok=True,
            budget_ok=True,
            tx_envelope_ok=True,
            session_state_ok=True,
            session_capability_binding_ok=True,
            wallet_capability_ok=True,
            nonce_ok=True,
        )
