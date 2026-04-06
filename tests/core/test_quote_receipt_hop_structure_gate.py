from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_HOP_BAD_HOP,
    QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH,
    QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH,
    QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL,
    QUOTE_RECEIPT_HOP_OK,
    evaluate_route_quote_receipt_hop_structure_gate,
    route_quote_receipt_hop_structure_error,
)


def _base_args() -> dict[str, int]:
    return {
        "hop_dict_ok": 1,
        "pool_id_ok": 1,
        "snapshotted_pool_present": 1,
        "working_pool_present": 1,
        "assets_shaped_ok": 1,
        "is_first_hop": 1,
        "first_hop_asset_in_ok": 1,
        "hop_asset_chain_ok": 1,
        "hop_amounts_ok": 1,
        "hop_amount_chain_ok": 1,
    }


def test_quote_receipt_hop_structure_gate_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_hop_structure_gate(**_base_args())
    assert outcome.hop_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_HOP_OK
    assert route_quote_receipt_hop_structure_error(outcome) == "ok"


def test_quote_receipt_hop_structure_gate_bad_hop_precedes_everything() -> None:
    args = _base_args()
    args["hop_dict_ok"] = 0
    args["pool_id_ok"] = 0
    outcome = evaluate_route_quote_receipt_hop_structure_gate(**args)
    assert outcome.hop_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_HOP_BAD_HOP
    assert route_quote_receipt_hop_structure_error(outcome) == "bad_hop"


def test_quote_receipt_hop_structure_gate_missing_working_pool_after_snapshot() -> None:
    args = _base_args()
    args["working_pool_present"] = 0
    args["assets_shaped_ok"] = 0
    outcome = evaluate_route_quote_receipt_hop_structure_gate(**args)
    assert outcome.hop_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_HOP_MISSING_WORKING_POOL
    assert route_quote_receipt_hop_structure_error(outcome) == "missing_working_pool"


def test_quote_receipt_hop_structure_gate_first_hop_asset_mismatch_maps_to_leg_asset_in() -> None:
    args = _base_args()
    args["first_hop_asset_in_ok"] = 0
    outcome = evaluate_route_quote_receipt_hop_structure_gate(**args)
    assert outcome.hop_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_HOP_LEG_ASSET_IN_MISMATCH
    assert route_quote_receipt_hop_structure_error(outcome) == "leg_asset_in_mismatch"


def test_quote_receipt_hop_structure_gate_later_hop_asset_mismatch_maps_to_chain_mismatch() -> None:
    args = _base_args()
    args["is_first_hop"] = 0
    args["hop_asset_chain_ok"] = 0
    outcome = evaluate_route_quote_receipt_hop_structure_gate(**args)
    assert outcome.hop_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_HOP_HOP_ASSET_CHAIN_MISMATCH
    assert route_quote_receipt_hop_structure_error(outcome) == "hop_asset_chain_mismatch"


def test_quote_receipt_hop_structure_gate_rejects_non_flag_input() -> None:
    args = _base_args()
    args["hop_dict_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_hop_structure_gate(**args)
