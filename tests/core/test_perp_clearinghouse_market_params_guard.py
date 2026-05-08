from __future__ import annotations

from src.core.perp_clearinghouse_market_params_guard import (
    MARKET_KIND_CH2P,
    MARKET_KIND_CH3P,
    REJECT_INITIAL_MARGIN_DECREASE_WHILE_OPEN,
    REJECT_MAINTENANCE_MARGIN_DECREASE_WHILE_OPEN,
    REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN,
    REJECT_MAX_ORACLE_STALENESS_INCREASE_WHILE_OPEN,
    REJECT_MAX_POSITION_INCREASE_WHILE_OPEN,
    REJECT_OK,
    evaluate_perp_clearinghouse_market_params_guard,
)


def _guard(**overrides: object):
    args: dict[str, object] = {
        "market_kind": MARKET_KIND_CH2P,
        "operator_ok": True,
        "epoch_settled_ok": True,
        "position_base_a": 1_000,
        "position_base_b": -1_000,
        "position_base_c": 0,
        "old_liquidation_penalty_bps": 50,
        "new_liquidation_penalty_bps": 50,
        "old_max_oracle_move_bps": 500,
        "new_max_oracle_move_bps": 500,
        "old_max_oracle_staleness_epochs": 100,
        "new_max_oracle_staleness_epochs": 100,
        "old_initial_margin_bps": 1_000,
        "new_initial_margin_bps": 1_000,
        "old_maintenance_margin_bps": 600,
        "new_maintenance_margin_bps": 600,
        "old_max_position_abs": 2_000,
        "new_max_position_abs": 2_000,
    }
    args.update(overrides)
    return evaluate_perp_clearinghouse_market_params_guard(**args)


def test_live_2p_market_rejects_risk_loosenings() -> None:
    cases = [
        (
            {"new_max_oracle_move_bps": 501},
            REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN,
            "max_oracle_move_increase_ok",
        ),
        (
            {"new_max_oracle_staleness_epochs": 101},
            REJECT_MAX_ORACLE_STALENESS_INCREASE_WHILE_OPEN,
            "max_oracle_staleness_increase_ok",
        ),
        (
            {"new_initial_margin_bps": 999},
            REJECT_INITIAL_MARGIN_DECREASE_WHILE_OPEN,
            "initial_margin_decrease_ok",
        ),
        (
            {"new_maintenance_margin_bps": 599},
            REJECT_MAINTENANCE_MARGIN_DECREASE_WHILE_OPEN,
            "maintenance_margin_decrease_ok",
        ),
        (
            {"new_max_position_abs": 2_001},
            REJECT_MAX_POSITION_INCREASE_WHILE_OPEN,
            "max_position_increase_ok",
        ),
    ]

    for overrides, reject_code, check_name in cases:
        outcome = _guard(**overrides)

        assert outcome.admission_ok is False
        assert outcome.positions_open is True
        assert outcome.reject_code == reject_code
        assert outcome.checks[check_name] is False


def test_live_3p_market_includes_third_leg_when_detecting_open_positions() -> None:
    outcome = _guard(
        market_kind=MARKET_KIND_CH3P,
        position_base_a=0,
        position_base_b=0,
        position_base_c=1_000,
        new_max_oracle_move_bps=501,
    )

    assert outcome.positions_open is True
    assert outcome.reject_code == REJECT_MAX_ORACLE_MOVE_INCREASE_WHILE_OPEN


def test_flat_market_can_change_risk_controls_after_operator_and_epoch_gates_pass() -> None:
    outcome = _guard(
        position_base_a=0,
        position_base_b=0,
        new_max_oracle_move_bps=501,
        new_max_oracle_staleness_epochs=101,
        new_initial_margin_bps=999,
        new_maintenance_margin_bps=599,
        new_max_position_abs=2_001,
    )

    assert outcome.positions_open is False
    assert outcome.admission_ok is True
    assert outcome.reject_code == REJECT_OK
