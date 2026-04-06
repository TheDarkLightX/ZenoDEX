from __future__ import annotations

from src.core.perp_clearinghouse_market_params_guard import (
    MARKET_KIND_CH2P,
    MARKET_KIND_CH3P,
    REJECT_MID_EPOCH,
    REJECT_OPERATOR_ONLY,
    REJECT_PENALTY_ABOVE_MAINTENANCE,
    REJECT_PENALTY_INCREASE_WHILE_OPEN,
    evaluate_perp_clearinghouse_market_params_guard,
    perp_clearinghouse_market_params_guard_error,
)


def _base_kwargs() -> dict[str, object]:
    return {
        "market_kind": MARKET_KIND_CH2P,
        "operator_ok": True,
        "epoch_settled_ok": True,
        "position_base_a": 0,
        "position_base_b": 0,
        "position_base_c": 0,
        "old_liquidation_penalty_bps": 50,
        "new_liquidation_penalty_bps": 50,
        "new_maintenance_margin_bps": 700,
    }


def test_perp_clearinghouse_market_params_guard_accepts_happy_path() -> None:
    outcome = evaluate_perp_clearinghouse_market_params_guard(**_base_kwargs())

    assert outcome.admission_ok is True
    assert outcome.positions_open is False
    assert perp_clearinghouse_market_params_guard_error(outcome) is None


def test_perp_clearinghouse_market_params_guard_rejects_operator_first() -> None:
    kwargs = _base_kwargs()
    kwargs["operator_ok"] = False
    kwargs["epoch_settled_ok"] = False
    outcome = evaluate_perp_clearinghouse_market_params_guard(**kwargs)

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_OPERATOR_ONLY
    assert perp_clearinghouse_market_params_guard_error(outcome) == "operator only"


def test_perp_clearinghouse_market_params_guard_rejects_mid_epoch_before_penalty_checks() -> None:
    kwargs = _base_kwargs()
    kwargs["epoch_settled_ok"] = False
    kwargs["position_base_a"] = 10
    kwargs["new_liquidation_penalty_bps"] = 60
    outcome = evaluate_perp_clearinghouse_market_params_guard(**kwargs)

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_MID_EPOCH
    assert perp_clearinghouse_market_params_guard_error(outcome) == "cannot update market params mid-epoch"


def test_perp_clearinghouse_market_params_guard_rejects_penalty_increase_with_open_positions() -> None:
    kwargs = _base_kwargs()
    kwargs["position_base_a"] = 25
    kwargs["new_liquidation_penalty_bps"] = 60
    outcome = evaluate_perp_clearinghouse_market_params_guard(**kwargs)

    assert outcome.positions_open is True
    assert outcome.penalty_increase_ok is False
    assert outcome.reject_code == REJECT_PENALTY_INCREASE_WHILE_OPEN
    assert perp_clearinghouse_market_params_guard_error(outcome) == (
        "invalid params: cannot increase liquidation_penalty_bps while positions are open"
    )


def test_perp_clearinghouse_market_params_guard_rejects_penalty_above_maintenance_for_3p() -> None:
    kwargs = _base_kwargs()
    kwargs["market_kind"] = MARKET_KIND_CH3P
    kwargs["new_liquidation_penalty_bps"] = 700
    kwargs["new_maintenance_margin_bps"] = 700
    outcome = evaluate_perp_clearinghouse_market_params_guard(**kwargs)

    assert outcome.admission_ok is False
    assert outcome.reject_code == REJECT_PENALTY_ABOVE_MAINTENANCE
    assert perp_clearinghouse_market_params_guard_error(outcome) == (
        "invalid params: require liquidation_penalty_bps < maintenance_margin_bps"
    )
