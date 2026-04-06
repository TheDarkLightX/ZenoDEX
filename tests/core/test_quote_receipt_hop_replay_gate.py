from __future__ import annotations

import pytest

from src.core.quote_receipts import (
    QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION,
    QUOTE_RECEIPT_REPLAY_OK,
    evaluate_route_quote_receipt_hop_replay_gate,
    route_quote_receipt_hop_replay_error,
)


def _base_args() -> dict[str, int]:
    return {
        "direction_ok": 1,
        "forward_direction": 1,
        "swap_ok": 1,
        "quote_matches": 1,
        "next_reserve_in": 900,
        "next_reserve_out": 1100,
    }


def test_quote_receipt_hop_replay_gate_forward_happy_path() -> None:
    outcome = evaluate_route_quote_receipt_hop_replay_gate(**_base_args())
    assert outcome.replay_ok is True
    assert outcome.reject_code == QUOTE_RECEIPT_REPLAY_OK
    assert outcome.next_reserve0 == 900
    assert outcome.next_reserve1 == 1100
    assert route_quote_receipt_hop_replay_error(outcome) == "ok"


def test_quote_receipt_hop_replay_gate_reverse_direction_swaps_writeback() -> None:
    args = _base_args()
    args["forward_direction"] = 0
    outcome = evaluate_route_quote_receipt_hop_replay_gate(**args)
    assert outcome.replay_ok is True
    assert outcome.next_reserve0 == 1100
    assert outcome.next_reserve1 == 900


def test_quote_receipt_hop_replay_gate_direction_failure_precedes_other_failures() -> None:
    args = _base_args()
    args["direction_ok"] = 0
    args["swap_ok"] = 0
    args["quote_matches"] = 0
    outcome = evaluate_route_quote_receipt_hop_replay_gate(**args)
    assert outcome.replay_ok is False
    assert outcome.reject_code == QUOTE_RECEIPT_REPLAY_BAD_POOL_DIRECTION
    assert route_quote_receipt_hop_replay_error(outcome) == "bad_pool_direction"


def test_quote_receipt_hop_replay_gate_rejects_negative_next_reserve() -> None:
    args = _base_args()
    args["next_reserve_in"] = -1
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_hop_replay_gate(**args)


def test_quote_receipt_hop_replay_gate_rejects_noncanonical_flag() -> None:
    args = _base_args()
    args["swap_ok"] = 2
    with pytest.raises(ValueError):
        evaluate_route_quote_receipt_hop_replay_gate(**args)
