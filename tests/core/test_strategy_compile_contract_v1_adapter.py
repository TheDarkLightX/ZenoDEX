from __future__ import annotations

import pytest

from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, PolicyBackend, StrategyTemplate
from src.kernels.python.strategy_compile_contract_v1_adapter import (
    check_strategy_compile_contract,
    policy_backend_code,
    strategy_template_code,
)


def _strategy():
    return compile_policy_candidate(
        {
            "strategy_id": "compile.contract.1",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "tau",
            "template": "dca",
            "asset_universe": ["zUSD", "BTC"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": 2,
            },
            "template_params": {
                "fixed_order_size": 100,
                "cadence_epochs": 4,
                "asset_in": "zUSD",
                "asset_out": "BTC",
            },
            "tau_policy_specs": list(AUTOTRADER_TAU_POLICY_SPECS),
        }
    ).strategy


def test_strategy_compile_contract_accepts_supported_dca_strategy() -> None:
    result = check_strategy_compile_contract(_strategy())
    assert result.ok is True
    assert result.error is None


def test_strategy_compile_contract_rejects_tampered_scope_and_bundle() -> None:
    strategy = _strategy()
    object.__setattr__(strategy, "asset_universe", ("zUSD",))
    result = check_strategy_compile_contract(strategy)
    assert result.ok is False
    assert result.error == "asset_scope_invalid"

    strategy = _strategy()
    object.__setattr__(strategy, "tau_policy_specs", ("autotrader_budget_guard_v1",))
    result = check_strategy_compile_contract(strategy)
    assert result.ok is False
    assert result.error == "tau_policy_bundle_invalid"


def test_strategy_compile_contract_rejects_tampered_actions_and_required_params() -> None:
    strategy = _strategy()
    object.__setattr__(strategy, "allowed_actions", ())
    result = check_strategy_compile_contract(strategy)
    assert result.ok is False
    assert result.error == "allowed_actions_invalid"

    strategy = _strategy()
    object.__setattr__(strategy, "template_params", {"fixed_order_size": 100, "asset_in": "zUSD", "asset_out": "BTC"})
    result = check_strategy_compile_contract(strategy)
    assert result.ok is False
    assert result.error == "required_template_params_missing"


def test_strategy_compile_contract_rejects_bad_ranges_and_types() -> None:
    strategy = _strategy()
    object.__setattr__(strategy.notional_caps, "per_window_max", 50)
    result = check_strategy_compile_contract(strategy)
    assert result.ok is False
    assert result.error == "notional_caps_invalid"

    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        check_strategy_compile_contract("bad")


def test_strategy_compile_contract_code_helpers_cover_all_enum_values() -> None:
    assert policy_backend_code(PolicyBackend.LOCAL) == 0
    assert policy_backend_code(PolicyBackend.TAU) == 1
    assert strategy_template_code(StrategyTemplate.DCA) == 1
    assert strategy_template_code(StrategyTemplate.LIMIT_LADDER) == 2
    assert strategy_template_code(StrategyTemplate.STOP_LOSS) == 3
    assert strategy_template_code(StrategyTemplate.TAKE_PROFIT) == 4
    with pytest.raises(TypeError, match="value must be a PolicyBackend"):
        policy_backend_code("bad")
    with pytest.raises(TypeError, match="value must be a StrategyTemplate"):
        strategy_template_code("bad")
