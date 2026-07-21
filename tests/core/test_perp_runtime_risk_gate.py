from __future__ import annotations

import pytest

from src.core.perp_runtime_risk_gate import (
    ACTION_ADVANCE_EPOCH,
    ACTION_CLEAR_BREAKER,
    ACTION_DEPOSIT_COLLATERAL,
    ACTION_PARTIAL_LIQUIDATE,
    ACTION_PUBLISH_CLEARING_PRICE,
    ACTION_SET_MARKET_PARAMS,
    ACTION_SET_POSITION,
    ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY,
    ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY,
    evaluate_perp_runtime_risk_gate,
    perp_runtime_risk_gate_error,
)


def test_runtime_risk_gate_advance_epoch_prefers_operator_only() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_ADVANCE_EPOCH,
        operator_ok=False,
        unknown_fields_ok=False,
        sender_binding_ok=True,
        epoch_settled_ok=False,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.admission_ok is False
    assert outcome.reject_code == "OperatorOnly"
    assert perp_runtime_risk_gate_error(outcome, action="advance_epoch") == "operator only"


def test_runtime_risk_gate_advance_epoch_rejects_unsettled_epoch() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_ADVANCE_EPOCH,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=False,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "EpochNotSettled"
    assert (
        perp_runtime_risk_gate_error(outcome, action="advance_epoch")
        == "cannot advance epoch before settling current epoch"
    )


def test_runtime_risk_gate_publish_price_rejects_nonpositive_price() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_PUBLISH_CLEARING_PRICE,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=True,
        positive_price_ok=False,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "PriceInvalid"
    assert (
        perp_runtime_risk_gate_error(outcome, action="publish_clearing_price")
        == "publish_clearing_price requires price_e8 > 0"
    )


def test_runtime_risk_gate_clear_breaker_rejects_open_positions() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_CLEAR_BREAKER,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=False,
        params_object_ok=True,
    )

    assert outcome.reject_code == "PositionsOpen"
    assert (
        perp_runtime_risk_gate_error(outcome, action="clear_breaker")
        == "cannot clear breaker while positions are open"
    )


def test_runtime_risk_gate_set_market_params_rejects_mid_epoch_before_params_shape() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_SET_MARKET_PARAMS,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=False,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=False,
    )

    assert outcome.reject_code == "MarketParamsMidEpoch"
    assert (
        perp_runtime_risk_gate_error(outcome, action="set_market_params")
        == "cannot update market params mid-epoch"
    )


def test_runtime_risk_gate_deposit_prefers_unknown_fields_before_sender_binding() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_DEPOSIT_COLLATERAL,
        operator_ok=True,
        unknown_fields_ok=False,
        sender_binding_ok=False,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "UnknownFields"
    assert (
        perp_runtime_risk_gate_error(outcome, action="deposit_collateral")
        == "deposit_collateral has unknown fields"
    )


def test_runtime_risk_gate_set_position_rejects_sender_binding() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_SET_POSITION,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=False,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "SenderBindingInvalid"
    assert (
        perp_runtime_risk_gate_error(outcome, action="set_position")
        == "account_pubkey must match tx sender"
    )


def test_runtime_risk_gate_partial_liquidate_rejects_sender_binding() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_PARTIAL_LIQUIDATE,
        operator_ok=True,
        unknown_fields_ok=True,
        sender_binding_ok=False,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "SenderBindingInvalid"
    assert (
        perp_runtime_risk_gate_error(outcome, action="partial_liquidate")
        == "account_pubkey must match tx sender"
    )


def test_runtime_risk_gate_settle_carried_liability_is_operator_only() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_SETTLE_FUNDING_CLOSEOUT_CARRIED_LIABILITY,
        operator_ok=False,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "OperatorOnly"
    assert (
        perp_runtime_risk_gate_error(
            outcome,
            action="settle_funding_closeout_carried_liability",
        )
        == "operator only"
    )


def test_runtime_risk_gate_settle_closeout_recovery_is_operator_only() -> None:
    outcome = evaluate_perp_runtime_risk_gate(
        action_kind=ACTION_SETTLE_FUNDING_CLOSEOUT_RECOVERY,
        operator_ok=False,
        unknown_fields_ok=True,
        sender_binding_ok=True,
        epoch_settled_ok=True,
        positive_price_ok=True,
        positions_flat_ok=True,
        params_object_ok=True,
    )

    assert outcome.reject_code == "OperatorOnly"
    assert (
        perp_runtime_risk_gate_error(
            outcome,
            action="settle_funding_closeout_recovery",
        )
        == "operator only"
    )


def test_runtime_risk_gate_rejects_noncanonical_flag() -> None:
    with pytest.raises(ValueError, match="unknown_fields_ok must be 0 or 1"):
        evaluate_perp_runtime_risk_gate(
            action_kind=ACTION_ADVANCE_EPOCH,
            operator_ok=True,
            unknown_fields_ok=2,
            sender_binding_ok=True,
            epoch_settled_ok=True,
            positive_price_ok=True,
            positions_flat_ok=True,
            params_object_ok=True,
        )
