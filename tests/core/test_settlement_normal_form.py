from __future__ import annotations

import pytest

from src.core.settlement_normal_form import normalize_settlement_op_for_commitment


def test_normalize_settlement_op_handles_missing_and_none_deltas() -> None:
    op = {
        "included_intents": [],
        "fills": [],
        "balance_deltas": [
            {"pubkey": "alice", "asset": "ETH", "delta_add": 100, "delta_sub": None},
            {"pubkey": "alice", "asset": "ETH", "delta_add": 0},  # delta_sub missing
            {"pubkey": "bob", "asset": "ETH", "delta_sub": 5},  # delta_add missing
        ],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    norm = normalize_settlement_op_for_commitment(op)
    assert norm["balance_deltas"] == [
        {"pubkey": "alice", "asset": "ETH", "delta_add": 100, "delta_sub": 0},
        {"pubkey": "bob", "asset": "ETH", "delta_add": 0, "delta_sub": 5},
    ]


def test_normalize_settlement_op_aggregates_duplicate_deltas() -> None:
    op_split = {
        "included_intents": [],
        "fills": [],
        "balance_deltas": [
            {"pubkey": "alice", "asset": "ETH", "delta_add": 50},
            {"pubkey": "alice", "asset": "ETH", "delta_add": 50},
        ],
        "reserve_deltas": [],
        "lp_deltas": [],
    }
    op_agg = {
        "included_intents": [],
        "fills": [],
        "balance_deltas": [{"pubkey": "alice", "asset": "ETH", "delta_add": 100, "delta_sub": 0}],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    assert normalize_settlement_op_for_commitment(op_split) == normalize_settlement_op_for_commitment(op_agg)


def test_normalize_settlement_op_sorts_fills_deterministically() -> None:
    op1 = {
        "included_intents": [["intent_0", "FILL"]],
        "fills": [
            {"intent_id": "intent_0", "action": "FILL", "amount_in_filled": 100, "amount_out_filled": 90, "reason": None},
            {"intent_id": "intent_0", "action": "FILL", "amount_in_filled": 50, "amount_out_filled": 45, "reason": None},
        ],
        "balance_deltas": [],
        "reserve_deltas": [],
        "lp_deltas": [],
    }
    op2 = {
        "included_intents": [["intent_0", "FILL"]],
        "fills": [
            {"intent_id": "intent_0", "action": "FILL", "amount_in_filled": 50, "amount_out_filled": 45, "reason": None},
            {"intent_id": "intent_0", "action": "FILL", "amount_in_filled": 100, "amount_out_filled": 90, "reason": None},
        ],
        "balance_deltas": [],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    assert normalize_settlement_op_for_commitment(op1) == normalize_settlement_op_for_commitment(op2)


def test_normalize_settlement_op_rejects_unknown_delta_fields() -> None:
    op = {
        "included_intents": [],
        "fills": [],
        "balance_deltas": [
            {"pubkey": "alice", "asset": "ETH", "delta_add": 1, "vault": {"hidden": 1}},
        ],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    with pytest.raises(TypeError, match="balance_deltas entries have unknown fields: vault"):
        normalize_settlement_op_for_commitment(op)


def test_normalize_settlement_op_rejects_negative_delta_amounts() -> None:
    op = {
        "included_intents": [],
        "fills": [],
        "balance_deltas": [{"pubkey": "alice", "asset": "ETH", "delta_add": -1}],
        "reserve_deltas": [],
        "lp_deltas": [],
    }

    with pytest.raises(ValueError, match="balance_deltas.delta_add must be non-negative"):
        normalize_settlement_op_for_commitment(op)
