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


def test_market_state_sink_claimant_balances_are_canonical() -> None:
    global_state = _legacy_global_state()
    global_state["fee_pool_quote"] = 30_000
    global_state["fee_income"] = 30_000
    global_state["insurance_balance"] = 30_000

    market = PerpMarketState(
        quote_asset="zUSD",
        global_state=global_state,
        accounts={},
        funding_closeout_sink_claimant_balances_quote=(
            ("z_sink", 10_000),
            ("a_sink", 20_000),
        ),
    )

    assert market.funding_closeout_sink_claimant_balances_quote == (
        ("a_sink", 20_000),
        ("z_sink", 10_000),
    )


def test_market_state_rejects_duplicate_sink_claimant_balance() -> None:
    global_state = _legacy_global_state()
    global_state["fee_pool_quote"] = 30_000
    global_state["fee_income"] = 30_000
    global_state["insurance_balance"] = 30_000

    with pytest.raises(ValueError, match="duplicate funding closeout sink claimant"):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=global_state,
            accounts={},
            funding_closeout_sink_claimant_balances_quote=(
                ("protocol_sink", 10_000),
                ("protocol_sink", 5_000),
            ),
        )


def test_market_state_rejects_unfunded_sink_claimant_balance() -> None:
    global_state = _legacy_global_state()
    global_state["fee_pool_quote"] = 9_999
    global_state["fee_income"] = 9_999
    global_state["insurance_balance"] = 9_999

    with pytest.raises(
        ValueError,
        match="funding closeout sink claimant balances exceed aggregate sink balance",
    ):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=global_state,
            accounts={},
            funding_closeout_sink_claimant_balances_quote=(
                ("protocol_sink", 10_000),
            ),
        )


def test_market_state_receiver_claim_balances_are_canonical() -> None:
    market = PerpMarketState(
        quote_asset="zUSD",
        global_state=_legacy_global_state(),
        accounts={},
        funding_closeout_receiver_claim_balances_quote=(
            ("zz_receiver", 12_000),
            ("aa_receiver", 18_000),
        ),
    )

    assert market.funding_closeout_receiver_claim_balances_quote == (
        ("aa_receiver", 18_000),
        ("zz_receiver", 12_000),
    )


def test_market_state_receiver_claim_lots_project_balances() -> None:
    market = PerpMarketState(
        quote_asset="zUSD",
        global_state=_legacy_global_state(),
        accounts={},
        funding_closeout_receiver_claim_balances_quote=(("receiver", 30_000),),
        funding_closeout_receiver_claim_lots_quote=(
            ("receiver", "future", 20_000, 10),
            ("receiver", "old", 10_000, 5),
        ),
    )

    assert market.funding_closeout_receiver_claim_lots_quote == (
        ("receiver", "old", 10_000, 5),
        ("receiver", "future", 20_000, 10),
    )
    assert market.funding_closeout_receiver_claim_balances_quote == (
        ("receiver", 30_000),
    )


def test_market_state_rejects_receiver_claim_lot_projection_mismatch() -> None:
    with pytest.raises(ValueError, match="receiver claim balance projection mismatch"):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=_legacy_global_state(),
            accounts={},
            funding_closeout_receiver_claim_balances_quote=(("receiver", 29_999),),
            funding_closeout_receiver_claim_lots_quote=(
                ("receiver", "old", 10_000, 5),
                ("receiver", "future", 20_000, 10),
            ),
        )


def test_market_state_rejects_duplicate_receiver_claim_lot() -> None:
    with pytest.raises(ValueError, match="duplicate funding closeout receiver claim lot"):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=_legacy_global_state(),
            accounts={},
            funding_closeout_receiver_claim_lots_quote=(
                ("receiver", "lot", 10_000, 5),
                ("receiver", "lot", 5_000, 10),
            ),
        )


def test_market_state_rejects_duplicate_receiver_claim_balance() -> None:
    with pytest.raises(ValueError, match="duplicate funding closeout receiver claim"):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=_legacy_global_state(),
            accounts={},
            funding_closeout_receiver_claim_balances_quote=(
                ("receiver", 10_000),
                ("receiver", 5_000),
            ),
        )


def test_market_state_rejects_non_positive_receiver_claim_balance() -> None:
    with pytest.raises(ValueError, match="receiver claim balance must be positive"):
        PerpMarketState(
            quote_asset="zUSD",
            global_state=_legacy_global_state(),
            accounts={},
            funding_closeout_receiver_claim_balances_quote=(("receiver", 0),),
        )
