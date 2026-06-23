from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_COMPILATION_WITNESS_V1,
    build_autotrader_compilation_witness_v1_step,
)


def test_build_autotrader_compilation_witness_v1_step() -> None:
    step = build_autotrader_compilation_witness_v1_step(
        source_form_ok=1,
        strategy_hash_match=1,
        owner_match=1,
        backend_match=1,
        template_match=1,
        asset_universe_match=1,
        allowed_actions_match=1,
        notional_caps_match=1,
        risk_limits_match=1,
        strategy_window_match=1,
        controls_match=1,
        template_params_match=1,
        tau_policy_specs_match=1,
        compile_contract_ok=1,
    )
    assert AUTOTRADER_COMPILATION_WITNESS_V1.spec_id == "autotrader_compilation_witness_v1"
    assert step["i1"] == 1
    assert step["i14"] == 1


def test_build_autotrader_compilation_witness_v1_step_rejects_bad_bool_inputs() -> None:
    with pytest.raises(ValueError, match="tau_policy_specs_match must be 0 or 1"):
        build_autotrader_compilation_witness_v1_step(
            source_form_ok=1,
            strategy_hash_match=1,
            owner_match=1,
            backend_match=1,
            template_match=1,
            asset_universe_match=1,
            allowed_actions_match=1,
            notional_caps_match=1,
            risk_limits_match=1,
            strategy_window_match=1,
            controls_match=1,
            template_params_match=1,
            tau_policy_specs_match=2,
            compile_contract_ok=1,
        )
