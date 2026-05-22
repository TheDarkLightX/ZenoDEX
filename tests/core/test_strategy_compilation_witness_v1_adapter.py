from __future__ import annotations

import pytest

from src.agents.policy_artifacts import build_strategy_source_artifact
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS
from src.kernels.python.strategy_compilation_witness_v1_adapter import (
    check_strategy_compilation_witness,
)
from src.kernels.python.strategy_compile_contract_v1_adapter import check_strategy_compile_contract


def _strategy():
    return compile_policy_candidate(
        {
            "strategy_id": "compile.witness.1",
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


def test_strategy_compilation_witness_accepts_identity_source_artifact() -> None:
    strategy = _strategy()
    source_artifact = build_strategy_source_artifact(
        strategy=strategy,
        source_form="sentence",
        source_text="dca 100 zUSD into BTC every 4 epochs",
    )
    result = check_strategy_compilation_witness(
        source_artifact=source_artifact,
        strategy=strategy,
        compile_contract_ok=check_strategy_compile_contract(strategy).ok,
    )
    assert result.ok is True
    assert result.error is None


def test_strategy_compilation_witness_fail_closes_and_rejects_bad_types() -> None:
    strategy = _strategy()
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    tampered = _strategy()
    object.__setattr__(tampered, "template_params", {"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "BTC", "asset_out": "zUSD"})
    result = check_strategy_compilation_witness(
        source_artifact=source_artifact,
        strategy=tampered,
        compile_contract_ok=True,
    )
    assert result.ok is False
    assert result.error == "strategy_hash_mismatch"

    with pytest.raises(TypeError, match="source_artifact must be a StrategySourceArtifact"):
        check_strategy_compilation_witness(source_artifact="bad", strategy=strategy, compile_contract_ok=True)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        check_strategy_compilation_witness(source_artifact=source_artifact, strategy="bad", compile_contract_ok=True)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="compile_contract_ok must be a bool"):
        check_strategy_compilation_witness(source_artifact=source_artifact, strategy=strategy, compile_contract_ok="yes")  # type: ignore[arg-type]
