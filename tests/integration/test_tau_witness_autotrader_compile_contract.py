from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_COMPILE_CONTRACT_V1,
    build_autotrader_compile_contract_v1_step,
)


def test_build_autotrader_compile_contract_v1_step() -> None:
    step = build_autotrader_compile_contract_v1_step(
        backend_ok=1,
        template_ok=1,
        strategy_id_ok=1,
        owner_binding_ok=1,
        asset_scope_ok=1,
        required_params_ok=1,
        action_scope_ok=1,
        notional_chain_ok=1,
        slippage_ok=1,
        oracle_window_ok=1,
        strategy_window_ok=1,
        controls_ok=1,
        tau_bundle_ok=1,
    )
    assert AUTOTRADER_COMPILE_CONTRACT_V1.spec_id == "autotrader_compile_contract_v1"
    assert step["i1"] == 1
    assert step["i13"] == 1


def test_build_autotrader_compile_contract_v1_step_rejects_bad_bool_inputs() -> None:
    with pytest.raises(ValueError, match="strategy_id_ok must be 0 or 1"):
        build_autotrader_compile_contract_v1_step(
            backend_ok=1,
            template_ok=1,
            strategy_id_ok=2,
            owner_binding_ok=1,
            asset_scope_ok=1,
            required_params_ok=1,
            action_scope_ok=1,
            notional_chain_ok=1,
            slippage_ok=1,
            oracle_window_ok=1,
            strategy_window_ok=1,
            controls_ok=1,
            tau_bundle_ok=1,
        )
