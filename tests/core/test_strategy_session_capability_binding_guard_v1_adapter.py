from __future__ import annotations

import pytest

from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.integration.autotrader_signals import AutoTraderWalletCapability
from src.kernels.python.strategy_session_capability_binding_guard_v1_adapter import (
    check_strategy_session_capability_binding,
)


def _strategy(**overrides: object) -> StrategyIR:
    data = {
        "strategy_id": "strat.1",
        "owner_pubkey": "owner.pubkey.1",
        "policy_backend": PolicyBackend.LOCAL,
        "template": StrategyTemplate.DCA,
        "asset_universe": ("A", "B"),
        "allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN,),
        "notional_caps": NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        "risk_limits": RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        "strategy_window": StrategyWindow(valid_from_epoch=1, valid_until_epoch=10),
        "template_params": {
            "fixed_order_size": 100,
            "cadence_epochs": 1,
            "asset_in": "A",
            "asset_out": "B",
        },
    }
    data.update(overrides)
    return StrategyIR(**data)


def _capability(**overrides: object) -> AutoTraderWalletCapability:
    data = {
        "session_id": "session.1",
        "owner_pubkey": "owner.pubkey.1",
        "chain_id": "tau-net-alpha",
        "valid_from_epoch": 2,
        "valid_until_epoch": 9,
        "notional_remaining": 500,
        "allowed_assets": ("A", "B"),
        "allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN,),
        "enabled": True,
    }
    data.update(overrides)
    return AutoTraderWalletCapability(**data)


def test_check_strategy_session_capability_binding_accepts_in_scope_capability() -> None:
    result = check_strategy_session_capability_binding(
        strategy=_strategy(),
        capability=_capability(),
        chain_id="tau-net-alpha",
    )
    assert result.ok is True
    assert result.error is None


@pytest.mark.parametrize(
    ("capability_overrides", "chain_id", "error"),
    [
        ({"owner_pubkey": "other.pubkey"}, "tau-net-alpha", "session_capability_owner_mismatch"),
        (
            {"chain_id": "tau-net-beta"},
            "tau-net-alpha",
            "session_capability_chain_mismatch:tau-net-beta!=tau-net-alpha",
        ),
        (
            {"allowed_assets": ("A", "B", "C")},
            "tau-net-alpha",
            "session_capability_asset_scope_exceeds_strategy",
        ),
        (
            {"allowed_actions": (StrategyAction.PLACE_SWAP_EXACT_IN, StrategyAction.PLACE_ORDER_INTENT)},
            "tau-net-alpha",
            "session_capability_action_scope_exceeds_strategy",
        ),
        (
            {"valid_from_epoch": 0, "valid_until_epoch": 9},
            "tau-net-alpha",
            "session_capability_window_exceeds_strategy",
        ),
        (
            {"valid_from_epoch": 2, "valid_until_epoch": 11},
            "tau-net-alpha",
            "session_capability_window_exceeds_strategy",
        ),
    ],
)
def test_check_strategy_session_capability_binding_rejects_scope_violations(
    capability_overrides: dict[str, object],
    chain_id: str,
    error: str,
) -> None:
    result = check_strategy_session_capability_binding(
        strategy=_strategy(),
        capability=_capability(**capability_overrides),
        chain_id=chain_id,
    )
    assert result.ok is False
    assert result.error == error


def test_check_strategy_session_capability_binding_rejects_missing_session_id_after_tamper() -> None:
    capability = _capability()
    object.__setattr__(capability, "session_id", "")
    result = check_strategy_session_capability_binding(
        strategy=_strategy(),
        capability=capability,
        chain_id="tau-net-alpha",
    )
    assert result.ok is False
    assert result.error == "session_capability_missing_session_id"


def test_check_strategy_session_capability_binding_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        check_strategy_session_capability_binding(
            strategy="bad",
            capability=_capability(),
            chain_id="tau-net-alpha",
        )
    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        check_strategy_session_capability_binding(
            strategy=_strategy(),
            capability="bad",
            chain_id="tau-net-alpha",
        )
    with pytest.raises(TypeError, match="chain_id must be a string"):
        check_strategy_session_capability_binding(
            strategy=_strategy(),
            capability=_capability(),
            chain_id=1,
        )
    with pytest.raises(ValueError, match="chain_id must be non-empty"):
        check_strategy_session_capability_binding(
            strategy=_strategy(),
            capability=_capability(),
            chain_id=" ",
        )
