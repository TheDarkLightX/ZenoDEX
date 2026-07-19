from __future__ import annotations

import ast
from dataclasses import fields
from pathlib import Path

import pytest

from src.core import perps as production_perps
from src.core.dex import DexState
from src.core.perps import PerpsState
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.nonproduction.perps_np_state import PerpClearinghouseNpMarketState
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ROOT = Path(__file__).resolve().parents[2]
ENGINE = ROOT / "src" / "integration" / "perp_engine.py"


def _state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _historical_market() -> PerpClearinghouseNpMarketState:
    return PerpClearinghouseNpMarketState(
        quote_asset="zUSD",
        global_state={
            "now_epoch": 0,
            "index_price_e8": 100_000_000,
            "fee_pool_e8": 0,
            "insurance_e8": 0,
            "insurance_ext_e8": 0,
            "claims_paid_e8": 0,
            "net_deposited_e8": 0,
            "initial_margin_bps": 1_000,
            "maintenance_margin_bps": 500,
            "depeg_buffer_bps": 100,
            "liquidation_penalty_bps": 50,
            "max_oracle_move_bps": 500,
            "funding_cap_bps": 100,
            "max_position_abs": 1_000_000,
            "min_notional_for_bounty_e8": 0,
        },
    )


def test_production_engine_source_has_no_retired_adapter_surface() -> None:
    source = ENGINE.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(ENGINE))
    defined_names = {
        node.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
    }
    assigned_names = {
        node.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)
    }
    assert not {"_apply_chnp_op", "_apply_init_market_np", "_load_nonproduction_np_core"} & defined_names
    assert not {"PERP_OP_VERSION_CHNP_V1_2", "PERP_CHNP_MARKET_PREFIX"} & assigned_names
    assert "src.nonproduction" not in source
    assert "..nonproduction" not in source
    assert "init_market_np" not in source
    assert "perp:chnp:" not in source


def test_production_core_neither_exports_n_party_state_nor_validation() -> None:
    forbidden = {
        "PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1",
        "PerpClearinghouseNpAccount",
        "PerpClearinghouseNpMarketState",
        "PerpClearinghouseNpPendingIntent",
    }
    assert forbidden.isdisjoint(vars(production_perps))
    assert not (ROOT / "src" / "core" / "perps_np_validation.py").exists()


def test_production_perps_state_rejects_nonproduction_market() -> None:
    with pytest.raises(TypeError, match="exact persistent market state types"):
        PerpsState(version=5, markets={"historical": _historical_market()})  # type: ignore[dict-item]


def test_production_config_has_no_retired_capability_switch() -> None:
    assert "allow_nonproduction_np" not in {field.name for field in fields(PerpEngineConfig)}


def test_retired_version_is_unrecognized_and_cannot_move_state() -> None:
    state = _state()
    result = apply_perp_ops(
        config=PerpEngineConfig(operator_pubkey="operator"),
        state=state,
        operations={"5": [{"module": "TauPerp", "version": "1.2", "action": "init_market_np"}]},
        tx_sender_pubkey="operator",
        block_timestamp=0,
    )
    assert result.ok is False
    assert result.error == "invalid perps version: 1.2"
    assert result.state is None
    assert state.perps is None


def test_production_snapshot_decoder_rejects_retired_market_kind() -> None:
    snapshot = snapshot_from_state(_state()).data
    snapshot["perps"] = {
        "version": 5,
        "markets": [{"market_id": "historical", "kind": "clearinghouse_np_v1"}],
    }
    with pytest.raises(ValueError, match="unsupported perps market kind"):
        state_from_snapshot(snapshot)
