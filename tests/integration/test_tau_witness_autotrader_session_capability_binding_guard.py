from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1,
    build_autotrader_session_capability_binding_guard_v1_step,
)


def test_build_autotrader_session_capability_binding_guard_v1_step() -> None:
    step = build_autotrader_session_capability_binding_guard_v1_step(
        session_present=1,
        owner_binding_ok=1,
        chain_binding_ok=1,
        asset_scope_ok=1,
        action_scope_ok=1,
        capability_valid_from_epoch=2,
        capability_valid_until_epoch=9,
        strategy_valid_from_epoch=1,
        strategy_valid_until_epoch=10,
    )
    assert (
        AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1.spec_id
        == "autotrader_session_capability_binding_guard_v1"
    )
    assert step["i9"] == 10


def test_build_autotrader_session_capability_binding_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="session_present must be 0 or 1"):
        build_autotrader_session_capability_binding_guard_v1_step(
            session_present=2,
            owner_binding_ok=1,
            chain_binding_ok=1,
            asset_scope_ok=1,
            action_scope_ok=1,
            capability_valid_from_epoch=2,
            capability_valid_until_epoch=9,
            strategy_valid_from_epoch=1,
            strategy_valid_until_epoch=10,
        )
