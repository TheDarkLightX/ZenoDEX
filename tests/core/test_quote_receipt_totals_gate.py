from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS,
    QUOTE_RECEIPT_TOTALS_OK,
    evaluate_route_quote_receipt_totals_gate,
    route_quote_receipt_totals_error,
)


def _base_args() -> dict[str, int]:
    return {
        "body_amounts_ok": 1,
        "totals_match": 1,
    }


def test_quote_receipt_totals_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_totals_gate(**_base_args())
    assert outcome.totals_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_TOTALS_OK
    assert route_quote_receipt_totals_error(outcome) == "ok"


def test_quote_receipt_totals_gate_body_amounts_precede_totals_mismatch() -> None:
    args = _base_args()
    args["body_amounts_ok"] = 0
    args["totals_match"] = 0
    outcome = evaluate_route_quote_receipt_totals_gate(**args)
    assert outcome.totals_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_TOTALS_BAD_BODY_AMOUNTS
    assert route_quote_receipt_totals_error(outcome) == "bad_body_amounts"


def test_quote_receipt_totals_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["body_amounts_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_totals_gate(**args)
