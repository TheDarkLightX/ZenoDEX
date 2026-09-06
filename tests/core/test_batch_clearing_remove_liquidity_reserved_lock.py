"""Regression tests for reserved-LP exclusion in legacy batch execution."""

from __future__ import annotations

from dataclasses import asdict, dataclass

import pytest

from src.core.batch_clearing import _apply_filled_intent_to_locals, _process_liquidity_intent
from src.core.batch_clearing_single_pool_liquidity import (
    _apply_remove_liquidity_to_single_pool_runtime,
    _LiquidityRuntimeRequest,
)
from src.core.cpmm import MIN_LP_LOCK
from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus
from src.state.support_root import LP_LOCK_PUBKEY

_OWNER = "0x" + "11" * 48
_RECIPIENT = "0x" + "22" * 48
_ASSET0 = "0x" + "01" * 32
_ASSET1 = "0x" + "02" * 32
_POOL_ID = "0x" + "aa" * 32


@dataclass
class _SinglePoolRuntime:
    balances_scratch: BalanceTable
    lp_scratch: LPTable
    current_reserves: tuple[int, int]
    current_lp_supply: int
    fills: list[Fill]


def _intent_id(number: int) -> str:
    return "0x" + f"{number:064x}"


def _build_state() -> tuple[PoolState, BalanceTable, LPTable]:
    pool = PoolState(
        pool_id=_POOL_ID,
        asset0=_ASSET0,
        asset1=_ASSET1,
        reserve0=10_000,
        reserve1=10_000,
        fee_bps=30,
        lp_supply=10_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(_RECIPIENT, _ASSET0, 17)
    balances.set(_RECIPIENT, _ASSET1, 29)
    lp_balances = LPTable()
    lp_balances.set(LP_LOCK_PUBKEY, _POOL_ID, MIN_LP_LOCK)
    lp_balances.set(_OWNER, _POOL_ID, 9_000)
    return pool, balances, lp_balances


def _remove_intent(*, sender: str, lp_amount: int, number: int) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_intent_id(number),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "pool_id": _POOL_ID,
            "lp_amount": lp_amount,
            "amount0_min": 0,
            "amount1_min": 0,
            "recipient": _RECIPIENT,
        },
    )


def _remove_fill(intent: Intent, *, lp_amount: int) -> Fill:
    return Fill(
        intent_id=intent.intent_id,
        action=FillAction.FILL,
        reason="REMOVE_LIQUIDITY",
        amount0_out=lp_amount,
        amount1_out=lp_amount,
        lp_burned=lp_amount,
    )


def _state_snapshot(
    pool: PoolState,
    balances: BalanceTable,
    lp_balances: LPTable,
    *,
    balance_deltas: list[BalanceDelta] | None = None,
    reserve_deltas: list[ReserveDelta] | None = None,
    lp_deltas: list[LPDelta] | None = None,
) -> dict[str, object]:
    return {
        "pool": asdict(pool),
        "balances": balances.get_all_balances(),
        "lp_balances": lp_balances.get_all_balances(),
        "lp_duration_metadata": {
            key: asdict(value)
            for key, value in lp_balances.get_all_duration_risk_metadata().items()
        },
        "balance_deltas": list(balance_deltas or []),
        "reserve_deltas": list(reserve_deltas or []),
        "lp_deltas": list(lp_deltas or []),
    }


@pytest.mark.parametrize("lp_amount", (1, MIN_LP_LOCK))
def test_reserved_lp_lock_rejects_in_batch_producer_without_mutating_inputs(lp_amount: int) -> None:
    """Given valid lock-backed LP, batch admission returns a no-effect rejection."""
    pool, balances, lp_balances = _build_state()
    intent = _remove_intent(sender=LP_LOCK_PUBKEY, lp_amount=lp_amount, number=lp_amount)
    before = _state_snapshot(pool, balances, lp_balances)

    fill = _process_liquidity_intent(intent, pool, lp_balances, balances)

    assert fill.action == FillAction.REJECT
    assert fill.reason == "RESERVED_LP_LOCK"
    assert _state_snapshot(pool, balances, lp_balances) == before


def test_reserved_lp_lock_keeps_invalid_parameter_rejection_precedence_in_batch_producer() -> None:
    pool, balances, lp_balances = _build_state()
    intent = _remove_intent(sender=LP_LOCK_PUBKEY, lp_amount=0, number=9)
    before = _state_snapshot(pool, balances, lp_balances)

    fill = _process_liquidity_intent(intent, pool, lp_balances, balances)

    assert fill.action == FillAction.REJECT
    assert fill.reason == "INVALID_PARAMS"
    assert _state_snapshot(pool, balances, lp_balances) == before


def test_reserved_lp_lock_cannot_enter_general_or_single_pool_apply_paths() -> None:
    """A fabricated accepted fill still cannot debit the reserved LP row."""
    pool, balances, lp_balances = _build_state()
    intent = _remove_intent(sender=LP_LOCK_PUBKEY, lp_amount=MIN_LP_LOCK, number=10)
    fill = _remove_fill(intent, lp_amount=MIN_LP_LOCK)
    balance_deltas: list[BalanceDelta] = []
    reserve_deltas: list[ReserveDelta] = []
    lp_deltas: list[LPDelta] = []
    before = _state_snapshot(
        pool,
        balances,
        lp_balances,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=lp_deltas,
    )

    with pytest.raises(ValueError, match="reserved LP lock cannot be burned"):
        _apply_filled_intent_to_locals(
            intent,
            fill,
            _POOL_ID,
            pool,
            balances,
            lp_balances,
            balance_deltas,
            reserve_deltas,
            lp_deltas,
        )

    assert (
        _state_snapshot(
            pool,
            balances,
            lp_balances,
            balance_deltas=balance_deltas,
            reserve_deltas=reserve_deltas,
            lp_deltas=lp_deltas,
        )
        == before
    )

    pool, balances, lp_balances = _build_state()
    intent = _remove_intent(sender=LP_LOCK_PUBKEY, lp_amount=MIN_LP_LOCK, number=11)
    runtime = _SinglePoolRuntime(
        balances_scratch=balances,
        lp_scratch=lp_balances,
        current_reserves=(pool.reserve0, pool.reserve1),
        current_lp_supply=pool.lp_supply,
        fills=[],
    )
    request = _LiquidityRuntimeRequest(
        intent=intent,
        fill=_remove_fill(intent, lp_amount=MIN_LP_LOCK),
        snap_pool=pool,
        runtime=runtime,
        recipient=_RECIPIENT,
    )
    before = _state_snapshot(pool, balances, lp_balances)
    runtime_before = (runtime.current_reserves, runtime.current_lp_supply, list(runtime.fills))

    with pytest.raises(ValueError, match="reserved LP lock cannot be burned"):
        _apply_remove_liquidity_to_single_pool_runtime(request)

    assert _state_snapshot(pool, balances, lp_balances) == before
    assert (runtime.current_reserves, runtime.current_lp_supply, runtime.fills) == runtime_before


def test_ordinary_lp_holder_still_withdraws_one_atom_through_batch_apply() -> None:
    pool, balances, lp_balances = _build_state()
    intent = _remove_intent(sender=_OWNER, lp_amount=1, number=12)

    fill = _process_liquidity_intent(intent, pool, lp_balances, balances)

    assert fill.action == FillAction.FILL
    assert (fill.amount0_out, fill.amount1_out, fill.lp_burned) == (1, 1, 1)
    balance_deltas: list[BalanceDelta] = []
    reserve_deltas: list[ReserveDelta] = []
    lp_deltas: list[LPDelta] = []
    _apply_filled_intent_to_locals(
        intent,
        fill,
        _POOL_ID,
        pool,
        balances,
        lp_balances,
        balance_deltas,
        reserve_deltas,
        lp_deltas,
    )

    assert (pool.reserve0, pool.reserve1, pool.lp_supply) == (9_999, 9_999, 9_999)
    assert lp_balances.get(_OWNER, _POOL_ID) == 8_999
    assert lp_balances.get(LP_LOCK_PUBKEY, _POOL_ID) == MIN_LP_LOCK
    assert balances.get(_RECIPIENT, _ASSET0) == 18
    assert balances.get(_RECIPIENT, _ASSET1) == 30
    assert [
        (delta.pubkey, delta.pool_id, delta.delta_add, delta.delta_sub) for delta in lp_deltas
    ] == [(_OWNER, _POOL_ID, 0, 1)]
    assert [
        (delta.pool_id, delta.asset, delta.delta_add, delta.delta_sub) for delta in reserve_deltas
    ] == [
        (_POOL_ID, _ASSET0, 0, 1),
        (_POOL_ID, _ASSET1, 0, 1),
    ]
