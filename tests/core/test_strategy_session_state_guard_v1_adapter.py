from __future__ import annotations

import pytest

from src.agents.strategy_ir import StrategyAction
from src.integration.autotrader_signals import AutoTraderSessionState, AutoTraderWalletCapability
from src.kernels.python.strategy_session_state_guard_v1_adapter import (
    check_strategy_session_state,
)


def _capability(**overrides: object) -> AutoTraderWalletCapability:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "valid_from_epoch": 1,
        "valid_until_epoch": 10,
        "notional_remaining": 500,
        "allowed_assets": ("A", "B"),
        "allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN,),
        "enabled": True,
    }
    data.update(overrides)
    return AutoTraderWalletCapability(**data)


def _session_state(**overrides: object) -> AutoTraderSessionState:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "enabled": True,
        "revoked_at_epoch": None,
    }
    data.update(overrides)
    return AutoTraderSessionState(**data)


def test_check_strategy_session_state_accepts_matching_enabled_unrevoked_state() -> None:
    result = check_strategy_session_state(
        session_state=_session_state(),
        capability=_capability(),
        chain_id="tau-net-alpha",
        current_epoch=5,
    )
    assert result.ok is True
    assert result.error is None


@pytest.mark.parametrize(
    ("session_overrides", "chain_id", "current_epoch", "error"),
    [
        ({"enabled": False}, "tau-net-alpha", 5, "session_state_disabled"),
        (
            {"session_id": "session.2"},
            "tau-net-alpha",
            5,
            "session_state_session_id_mismatch:session.2!=session.1",
        ),
        ({"owner_pubkey": "owner.pubkey.2"}, "tau-net-alpha", 5, "session_state_owner_mismatch"),
        (
            {"chain_id": "tau-net-beta"},
            "tau-net-alpha",
            5,
            "session_state_chain_mismatch:tau-net-beta!=tau-net-alpha",
        ),
        ({"revoked_at_epoch": 5}, "tau-net-alpha", 5, "session_state_revoked:5>=5"),
    ],
)
def test_check_strategy_session_state_rejects_invalid_state(
    session_overrides: dict[str, object],
    chain_id: str,
    current_epoch: int,
    error: str,
) -> None:
    result = check_strategy_session_state(
        session_state=_session_state(**session_overrides),
        capability=_capability(),
        chain_id=chain_id,
        current_epoch=current_epoch,
    )
    assert result.ok is False
    assert result.error == error


def test_check_strategy_session_state_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="session_state must be an AutoTraderSessionState"):
        check_strategy_session_state(
            session_state="bad",
            capability=_capability(),
            chain_id="tau-net-alpha",
            current_epoch=5,
        )
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        check_strategy_session_state(
            session_state=_session_state(),
            capability="bad",
            chain_id="tau-net-alpha",
            current_epoch=5,
        )
    with pytest.raises(TypeError, match="chain_id must be a string"):
        check_strategy_session_state(
            session_state=_session_state(),
            capability=_capability(),
            chain_id=1,
            current_epoch=5,
        )
    with pytest.raises(TypeError, match="current_epoch must be an int"):
        check_strategy_session_state(
            session_state=_session_state(),
            capability=_capability(),
            chain_id="tau-net-alpha",
            current_epoch="bad",
        )
    with pytest.raises(ValueError, match="chain_id must be non-empty"):
        check_strategy_session_state(
            session_state=_session_state(),
            capability=_capability(),
            chain_id="   ",
            current_epoch=5,
        )
    with pytest.raises(ValueError, match="current_epoch out of u32 range"):
        check_strategy_session_state(
            session_state=_session_state(),
            capability=_capability(),
            chain_id="tau-net-alpha",
            current_epoch=-1,
        )
