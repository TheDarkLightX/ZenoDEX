from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL,
    QUOTE_RECEIPT_POOL_SNAPSHOT_OK,
    QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT,
    evaluate_route_quote_receipt_pool_snapshot_gate,
    route_quote_receipt_pool_snapshot_error,
)


def _base_args() -> dict[str, int]:
    return {
        "pool_entries_well_formed": 1,
        "all_pools_present": 1,
        "all_fingerprints_match": 1,
    }


def test_quote_receipt_pool_snapshot_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_pool_snapshot_gate(**_base_args())
    assert outcome.snapshot_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_POOL_SNAPSHOT_OK
    assert route_quote_receipt_pool_snapshot_error(outcome) == "ok"


def test_quote_receipt_pool_snapshot_gate_bad_fingerprint_precedes_missing_pool() -> None:
    args = _base_args()
    args["pool_entries_well_formed"] = 0
    args["all_pools_present"] = 0
    outcome = evaluate_route_quote_receipt_pool_snapshot_gate(**args)
    assert outcome.snapshot_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_POOL_SNAPSHOT_BAD_FINGERPRINT
    assert route_quote_receipt_pool_snapshot_error(outcome) == "bad_pool_fingerprint"


def test_quote_receipt_pool_snapshot_gate_missing_pool_after_well_formed_entries() -> None:
    args = _base_args()
    args["all_pools_present"] = 0
    args["all_fingerprints_match"] = 0
    outcome = evaluate_route_quote_receipt_pool_snapshot_gate(**args)
    assert outcome.snapshot_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_POOL_SNAPSHOT_MISSING_POOL
    assert route_quote_receipt_pool_snapshot_error(outcome) == "missing_pool"


def test_quote_receipt_pool_snapshot_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["pool_entries_well_formed"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_pool_snapshot_gate(**args)
