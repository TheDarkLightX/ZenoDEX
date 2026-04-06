from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH,
    QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE,
    QUOTE_RECEIPT_CERTIFICATE_OK,
    evaluate_route_quote_receipt_certificate_gate,
    route_quote_receipt_certificate_error,
)


def _base_args() -> dict[str, int]:
    return {
        "cert_present": 1,
        "cert_dict_ok": 1,
        "winner_quote_dict_ok": 1,
        "asset_in_match": 1,
        "asset_out_match": 1,
        "amount_in_match": 1,
        "amount_out_match": 1,
        "legs_match": 1,
    }


def test_quote_receipt_certificate_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_certificate_gate(**_base_args())
    assert outcome.certificate_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_CERTIFICATE_OK
    assert route_quote_receipt_certificate_error(outcome) == "ok"


def test_quote_receipt_certificate_gate_absent_certificate_is_ok() -> None:
    args = _base_args()
    args["cert_present"] = 0
    args["cert_dict_ok"] = 0
    outcome = evaluate_route_quote_receipt_certificate_gate(**args)
    assert outcome.certificate_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_CERTIFICATE_OK


def test_quote_receipt_certificate_gate_bad_type_precedes_field_mismatches() -> None:
    args = _base_args()
    args["cert_dict_ok"] = 0
    args["amount_in_match"] = 0
    outcome = evaluate_route_quote_receipt_certificate_gate(**args)
    assert outcome.certificate_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_CERTIFICATE_BAD_TYPE
    assert route_quote_receipt_certificate_error(outcome) == "bad_canonical_route_certificate_type"


def test_quote_receipt_certificate_gate_amount_in_mismatch_after_structure_ok() -> None:
    args = _base_args()
    args["amount_in_match"] = 0
    outcome = evaluate_route_quote_receipt_certificate_gate(**args)
    assert outcome.certificate_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_CERTIFICATE_AMOUNT_IN_MISMATCH
    assert route_quote_receipt_certificate_error(outcome) == "canonical_route_certificate_amount_in_mismatch"


def test_quote_receipt_certificate_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["cert_present"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_certificate_gate(**args)
