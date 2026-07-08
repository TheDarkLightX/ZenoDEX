"""Strict consistency-checker regressions for isolated perps snapshots."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from src.core.perps_isolated_validation import validate_isolated_state_consistency

EPOCH_PHASES = {0: "Open", 1: "PricePublished", 2: "Settled"}


def _global_state() -> dict[str, bool | int]:
    return {
        "now_epoch": 0,
        "epoch_phase": 0,
        "breaker_active": False,
        "breaker_last_trigger_epoch": 0,
        "clearing_price_seen": False,
        "clearing_price_epoch": 0,
        "clearing_price_e8": 0,
        "mark_price_source_kind": 0,
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


def _validate(global_state: dict[str, object], accounts: dict[str, object] | None = None) -> None:
    validate_isolated_state_consistency(
        global_state=global_state,
        accounts={} if accounts is None else accounts,
        epoch_phase_int_to_str=EPOCH_PHASES,
    )


def test_validate_isolated_state_consistency_rejects_bool_int_field() -> None:
    state = _global_state()
    state["now_epoch"] = True

    with pytest.raises(TypeError, match=r"global_state\['now_epoch'\]"):
        _validate(state)


def test_validate_isolated_state_consistency_rejects_string_bool_field() -> None:
    state = _global_state()
    state["oracle_seen"] = "false"

    with pytest.raises(TypeError, match=r"global_state\['oracle_seen'\]"):
        _validate(state)


def test_validate_isolated_state_consistency_accepts_zero_one_bool_field() -> None:
    state = _global_state()
    state["breaker_active"] = 1

    _validate(state)


def test_validate_isolated_state_consistency_rejects_unfunded_liquidation_cone() -> None:
    state = _global_state()
    state["maintenance_margin_bps"] = 500
    state["depeg_buffer_bps"] = 100
    state["max_oracle_move_bps"] = 500
    state["liquidation_penalty_bps"] = 100

    with pytest.raises(ValueError, match="invalid funded liquidation params"):
        _validate(state)


def test_validate_isolated_state_consistency_accepts_funded_liquidation_boundary() -> None:
    state = _global_state()
    state["maintenance_margin_bps"] = 500
    state["depeg_buffer_bps"] = 100
    state["max_oracle_move_bps"] = 500
    state["liquidation_penalty_bps"] = 95

    _validate(state)


def test_validate_isolated_state_consistency_rejects_coerced_account_int() -> None:
    account = SimpleNamespace(
        position_base="0",
        entry_price_e8=0,
        funding_last_applied_epoch=0,
    )

    with pytest.raises(TypeError, match="account position_base"):
        _validate(_global_state(), {"alice": account})
