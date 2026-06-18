"""Strict legacy snapshot inference regressions for PerpMarketState."""

from __future__ import annotations

import pytest

from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_EXTERNAL_MEDIAN
from src.core.perps import PerpMarketState


def _legacy_global_state() -> dict[str, bool | int]:
    return {
        "now_epoch": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": MARK_PRICE_SOURCE_EXTERNAL_MEDIAN,
        "oracle_seen": False,
        "oracle_last_update_epoch": 0,
        "index_price_e8": 0,
        "max_oracle_staleness_epochs": 100,
        "max_oracle_move_bps": 500,
        "initial_margin_bps": 1000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "liquidation_penalty_bps": 50,
        "max_position_abs": 1_000_000,
        "fee_pool_quote": 0,
        "funding_rate_bps": 0,
        "funding_cap_bps": 100,
        "insurance_balance": 0,
        "initial_insurance": 0,
        "fee_income": 0,
        "claims_paid": 0,
        "min_notional_for_bounty": 100_000_000,
    }


def test_market_state_legacy_phase_inference_rejects_bad_bool_without_mutating() -> None:
    global_state = _legacy_global_state()
    global_state["clearing_price_seen"] = "false"  # type: ignore[assignment]

    with pytest.raises(TypeError, match=r"global_state\['clearing_price_seen'\]"):
        PerpMarketState(quote_asset="zUSD", global_state=global_state, accounts={})  # type: ignore[arg-type]

    assert "epoch_phase" not in global_state


def test_market_state_legacy_phase_inference_accepts_zero_one_bool_flags() -> None:
    global_state = _legacy_global_state()
    global_state.update(
        {
            "now_epoch": 7,
            "clearing_price_seen": 1,
            "clearing_price_epoch": 7,
            "clearing_price_e8": 100_000_000,
            "oracle_seen": 0,
        }
    )

    market = PerpMarketState(quote_asset="zUSD", global_state=global_state, accounts={})

    assert market.global_state["epoch_phase"] == 1
    assert market.global_state["clearing_price_seen"] is True
    assert market.global_state["oracle_seen"] is False
