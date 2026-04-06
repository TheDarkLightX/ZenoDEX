from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_PRECHECK_BAD_KIND,
    QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH,
    QUOTE_RECEIPT_PRECHECK_OK,
    evaluate_route_quote_receipt_precheck_gate,
    route_quote_receipt_precheck_error,
)


def _base_args() -> dict[str, int]:
    return {
        "schema_ok": 1,
        "receipt_hash_present": 1,
        "hash_matches": 1,
        "kind_ok": 1,
        "canonical_certificate_allowed": 1,
        "body_assets_ok": 1,
        "quote_epoch_ok": 1,
        "pools_object_ok": 1,
        "legs_list_ok": 1,
    }


def test_quote_receipt_precheck_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_precheck_gate(**_base_args())
    assert outcome.precheck_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_PRECHECK_OK
    assert route_quote_receipt_precheck_error(outcome) == "ok"


def test_quote_receipt_precheck_gate_hash_mismatch_precedes_bad_kind() -> None:
    args = _base_args()
    args["hash_matches"] = 0
    args["kind_ok"] = 0
    outcome = evaluate_route_quote_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_PRECHECK_HASH_MISMATCH
    assert route_quote_receipt_precheck_error(outcome) == "hash_mismatch"


def test_quote_receipt_precheck_gate_bad_kind_after_hash_ok() -> None:
    args = _base_args()
    args["kind_ok"] = 0
    outcome = evaluate_route_quote_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_PRECHECK_BAD_KIND
    assert route_quote_receipt_precheck_error(outcome) == "bad_kind"


def test_quote_receipt_precheck_gate_unexpected_certificate_precedes_bad_quote_epoch() -> None:
    args = _base_args()
    args["canonical_certificate_allowed"] = 0
    args["quote_epoch_ok"] = 0
    outcome = evaluate_route_quote_receipt_precheck_gate(**args)
    assert outcome.precheck_ok is False
    assert route_quote_receipt_precheck_error(outcome) == "unexpected_canonical_route_certificate"


def test_quote_receipt_precheck_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["schema_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_precheck_gate(**args)
