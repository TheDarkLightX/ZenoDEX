from __future__ import annotations

from dataclasses import replace

from src.core.batch_clearing import compute_settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.core.test_settlement_strong_validator import (
    _setup_add_liquidity_context,
    _setup_create_pool_context,
    _setup_swap_context,
)


def test_settlement_conservation_lane_rejects_balance_delta_replay_drift() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.balance_deltas[0].delta_sub += 1

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err == "balance_deltas mismatch vs replay"


def test_settlement_negative_balance_lane_rejects_apply_path() -> None:
    _pk, asset0, _asset1, pool_id, pool, _balances, intent, settlement = _setup_swap_context()
    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")


def test_fee_semantics_lane_rejects_fee_paid_drift() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, _settlement = _setup_swap_context()
    fee_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    fee_mismatch.fills[0].fee_paid += 1

    ok, err = validate_settlement_strong(
        settlement=fee_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"


def test_settlement_reserve_and_lp_replay_lanes_reject_drift() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.reserve_deltas[0].delta_add += 1

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = _setup_add_liquidity_context()
    settlement.lp_deltas[0].delta_add += 1

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas mismatch vs replay"


def test_settlement_event_replay_lane_rejects_drift() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.events[0]["fee_bps"] += 1

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err == "events mismatch vs replay"


def test_create_pool_fee_bps_bound_lane_rejects_invalid_fee_bps() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    invalid_fee_intent = replace(intent, fields={**(intent.fields or {}), "fee_bps": 10_001})

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_fee_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err == f"invalid CREATE_POOL fee_bps for intent_id={intent.intent_id}"
