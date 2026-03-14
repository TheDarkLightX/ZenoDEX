from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1,
    build_autotrader_live_admission_bundle_v1_step,
)


def test_build_autotrader_live_admission_bundle_v1_step() -> None:
    step = build_autotrader_live_admission_bundle_v1_step(
        source_registry_ok=1,
        signal_provenance_ok=1,
        route_economic_sanity_ok=1,
        execution_ok=1,
        oracle_freshness_ok=1,
        budget_ok=1,
        tx_envelope_ok=1,
        session_state_ok=1,
        session_capability_binding_ok=1,
        wallet_capability_ok=1,
        nonce_ok=1,
    )
    assert AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1.spec_id == "autotrader_live_admission_bundle_v1"
    assert step == {
        "i1": 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
        "i10": 1,
        "i11": 1,
    }


def test_build_autotrader_live_admission_bundle_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="signal_provenance_ok must be 0 or 1"):
        build_autotrader_live_admission_bundle_v1_step(
            source_registry_ok=1,
            signal_provenance_ok=2,
            route_economic_sanity_ok=1,
            execution_ok=1,
            oracle_freshness_ok=1,
            budget_ok=1,
            tx_envelope_ok=1,
            session_state_ok=1,
            session_capability_binding_ok=1,
            wallet_capability_ok=1,
            nonce_ok=1,
        )
