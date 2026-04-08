from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_SESSION_STATE_GUARD_V1,
    build_autotrader_session_state_guard_v1_step,
)


def test_build_autotrader_session_state_guard_v1_step() -> None:
    step = build_autotrader_session_state_guard_v1_step(
        enabled=1,
        session_binding_ok=1,
        owner_binding_ok=1,
        chain_binding_ok=1,
        revocation_epoch_present=1,
        current_epoch=5,
        revoked_at_epoch=7,
    )
    assert AUTOTRADER_SESSION_STATE_GUARD_V1.spec_id == "autotrader_session_state_guard_v1"
    assert step["i6"] == 5
    assert step["i7"] == 7


def test_build_autotrader_session_state_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="enabled must be 0 or 1"):
        build_autotrader_session_state_guard_v1_step(
            enabled=2,
            session_binding_ok=1,
            owner_binding_ok=1,
            chain_binding_ok=1,
            revocation_epoch_present=0,
            current_epoch=5,
            revoked_at_epoch=0,
        )
