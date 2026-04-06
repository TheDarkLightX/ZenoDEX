from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH,
    QUOTE_RECEIPT_LEG_SUMMARY_OK,
    evaluate_route_quote_receipt_leg_summary_gate,
    route_quote_receipt_leg_summary_error,
)


def _base_args() -> dict[str, int]:
    return {
        "final_asset_out_ok": 1,
        "first_hop_amount_in_ok": 1,
        "last_hop_amount_out_ok": 1,
    }


def test_quote_receipt_leg_summary_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_leg_summary_gate(**_base_args())
    assert outcome.leg_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_LEG_SUMMARY_OK
    assert route_quote_receipt_leg_summary_error(outcome) == "ok"


def test_quote_receipt_leg_summary_gate_asset_out_precedes_amount_mismatches() -> None:
    args = _base_args()
    args["final_asset_out_ok"] = 0
    args["first_hop_amount_in_ok"] = 0
    outcome = evaluate_route_quote_receipt_leg_summary_gate(**args)
    assert outcome.leg_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_LEG_SUMMARY_ASSET_OUT_MISMATCH
    assert route_quote_receipt_leg_summary_error(outcome) == "leg_asset_out_mismatch"


def test_quote_receipt_leg_summary_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["final_asset_out_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_leg_summary_gate(**args)
