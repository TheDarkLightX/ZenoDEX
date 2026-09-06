"""Regression tests for the nonspendable initial LP lock during replay."""

from __future__ import annotations

from dataclasses import asdict

import pytest

from src.core.cpmm import MIN_LP_LOCK
from src.core.liquidity import create_pool
from src.core.settlement import Fill, FillAction
from src.core.settlement_replay_context import ReplayContext, build_replay_context
from src.core.settlement_replay_remove_liquidity import (
    RemoveLiquidityReplayRequest,
    replay_remove_liquidity_fill,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolStatus
from src.state.support_root import LP_LOCK_PUBKEY

_OWNER = "0x" + "11" * 48
_OTHER_RECIPIENT = "0x" + "22" * 48
_ASSET0 = "0x" + "01" * 32
_ASSET1 = "0x" + "02" * 32


def _intent_id(number: int) -> str:
    return "0x" + f"{number:064x}"


def _build_active_replay() -> tuple[str, ReplayContext]:
    pool_id, pool, owner_lp = create_pool(
        asset0=_ASSET0,
        asset1=_ASSET1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=_OWNER,
    )
    pre_balances = BalanceTable()
    pre_balances.set(_OTHER_RECIPIENT, _ASSET0, 17)
    pre_balances.set(_OTHER_RECIPIENT, _ASSET1, 29)
    pre_lp = LPTable()
    pre_lp.set(_OWNER, pool_id, owner_lp)
    pre_lp.set(LP_LOCK_PUBKEY, pool_id, MIN_LP_LOCK)
    pre_lp.set_last_mint_timestamp(_OWNER, pool_id, 7)
    return (
        pool_id,
        build_replay_context(
            pre_balances=pre_balances,
            pre_pools={pool_id: pool},
            pre_lp_balances=pre_lp,
        ),
    )


def _remove_request(
    *,
    pool_id: str,
    replay: ReplayContext,
    sender: str,
    recipient: str,
    lp_amount: int,
    intent_number: int,
) -> tuple[Intent, RemoveLiquidityReplayRequest]:
    pool = replay.pools[pool_id]
    assert pool.reserve0 == pool.lp_supply
    assert pool.reserve1 == pool.lp_supply
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_intent_id(intent_number),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "pool_id": pool_id,
            "lp_amount": lp_amount,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    return intent, RemoveLiquidityReplayRequest(
        intent=intent,
        fill=Fill(
            intent_id=intent.intent_id,
            action=FillAction.FILL,
            amount0_out=lp_amount,
            amount1_out=lp_amount,
            lp_burned=lp_amount,
        ),
        pool=pool,
        pool_id=pool_id,
        recipient=recipient,
        replay=replay,
    )


def _replay_snapshot(replay: ReplayContext) -> dict[str, object]:
    return {
        "pools": {pool_id: asdict(pool) for pool_id, pool in replay.pools.items()},
        "balances": replay.balances.get_all_balances(),
        "lp_balances": replay.lp.get_all_balances(),
        "lp_duration_metadata": replay.lp.get_all_duration_risk_metadata(),
        "expected_events": list(replay.expected_events),
        "balance_deltas": list(replay.bal_deltas),
        "reserve_deltas": list(replay.res_deltas),
        "lp_deltas": list(replay.lp_deltas),
    }


@pytest.mark.parametrize("lp_amount", (1, MIN_LP_LOCK))
def test_reserved_lp_lock_rejects_positive_burn_without_mutating_replay(
    lp_amount: int,
) -> None:
    """Given a valid active pool, the reserved LP row cannot authorize a replay burn."""
    pool_id, replay = _build_active_replay()
    replay.expected_events.append({"type": "PREEXISTING"})
    intent, request = _remove_request(
        pool_id=pool_id,
        replay=replay,
        sender=LP_LOCK_PUBKEY,
        recipient=_OTHER_RECIPIENT,
        lp_amount=lp_amount,
        intent_number=1 + lp_amount,
    )
    before = _replay_snapshot(replay)

    # This kills the mutant that removes the reserved-sender eligibility guard.
    err = replay_remove_liquidity_fill(request=request)

    assert (
        err
        == f"REMOVE_LIQUIDITY reserved LP lock cannot be burned for intent_id={intent.intent_id}"
    )
    assert _replay_snapshot(replay) == before


def test_reserved_lp_lock_keeps_invalid_amount_rejection_precedence() -> None:
    pool_id, replay = _build_active_replay()
    intent, request = _remove_request(
        pool_id=pool_id,
        replay=replay,
        sender=LP_LOCK_PUBKEY,
        recipient=_OTHER_RECIPIENT,
        lp_amount=0,
        intent_number=3,
    )
    before = _replay_snapshot(replay)

    err = replay_remove_liquidity_fill(request=request)

    assert err == f"invalid lp_amount for intent_id={intent.intent_id}"
    assert _replay_snapshot(replay) == before


def test_reserved_lp_lock_keeps_inactive_pool_rejection_precedence() -> None:
    pool_id, replay = _build_active_replay()
    replay.pools[pool_id].status = PoolStatus.FROZEN
    intent, request = _remove_request(
        pool_id=pool_id,
        replay=replay,
        sender=LP_LOCK_PUBKEY,
        recipient=_OTHER_RECIPIENT,
        lp_amount=MIN_LP_LOCK,
        intent_number=4,
    )
    before = _replay_snapshot(replay)

    err = replay_remove_liquidity_fill(request=request)

    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"
    assert _replay_snapshot(replay) == before


def test_ordinary_holder_can_remove_one_lp_atom() -> None:
    """Given one owner LP atom, a valid ordinary withdrawal still records exact effects."""
    pool_id, replay = _build_active_replay()
    pool = replay.pools[pool_id]
    reserve0_before = pool.reserve0
    reserve1_before = pool.reserve1
    lp_supply_before = pool.lp_supply
    owner_lp_before = replay.lp.get(_OWNER, pool_id)
    intent, request = _remove_request(
        pool_id=pool_id,
        replay=replay,
        sender=_OWNER,
        recipient=_OWNER,
        lp_amount=1,
        intent_number=5,
    )

    err = replay_remove_liquidity_fill(request=request)

    assert err is None
    assert pool.reserve0 == reserve0_before - 1
    assert pool.reserve1 == reserve1_before - 1
    assert pool.lp_supply == lp_supply_before - 1
    assert replay.lp.get(_OWNER, pool_id) == owner_lp_before - 1
    assert replay.lp.get(LP_LOCK_PUBKEY, pool_id) == MIN_LP_LOCK
    assert replay.balances.get(_OWNER, pool.asset0) == 1
    assert replay.balances.get(_OWNER, pool.asset1) == 1
    assert replay.balances.get(_OTHER_RECIPIENT, pool.asset0) == 17
    assert replay.balances.get(_OTHER_RECIPIENT, pool.asset1) == 29
    assert replay.expected_events == []
    assert [
        (delta.pubkey, delta.pool_id, delta.delta_add, delta.delta_sub)
        for delta in replay.lp_deltas
    ] == [(_OWNER, pool_id, 0, 1)]
    assert [
        (delta.pubkey, delta.asset, delta.delta_add, delta.delta_sub) for delta in replay.bal_deltas
    ] == [
        (_OWNER, pool.asset0, 1, 0),
        (_OWNER, pool.asset1, 1, 0),
    ]
    assert [
        (delta.pool_id, delta.asset, delta.delta_add, delta.delta_sub)
        for delta in replay.res_deltas
    ] == [
        (pool_id, pool.asset0, 0, 1),
        (pool_id, pool.asset1, 0, 1),
    ]
