from __future__ import annotations

from tools.check_tau_formal_contract_artifacts import validate_tau_formal_contract_artifacts


def test_check_tau_formal_contract_artifacts() -> None:
    result = validate_tau_formal_contract_artifacts()
    assert result.errors == []
    assert set(result.checked_specs) == {
        "autotrader_nonce_guard_v1",
        "autotrader_tx_envelope_guard_v1",
        "nonce_replay_guard_v1",
        "oracle_freshness_v2",
        "rate_limiter_v1",
        "sandwich_detection_v1",
    }
