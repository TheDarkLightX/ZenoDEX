from __future__ import annotations

import importlib.util
import itertools

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.core.batch_clearing import (
    _eval_ordering_ab,
    _order_swaps_greedy_ab,
    _order_swaps_limit_price,
    _refine_ab_ordering_global,
    _refine_b_ordering,
    clear_batch_single_pool,
)
from src.core.settlement import Fill, FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

ASSET0 = "A"
ASSET1 = "B"
POOL_ID = "pool_ab"


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _make_pool(reserve0: int, reserve1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _make_intent(idx: int, sender_id: int, amount_in: int, min_amount_out: int) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        intent_id=_iid(idx),
        sender_pubkey=_sender(sender_id),
        kind=IntentKind.SWAP_EXACT_IN,
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _make_balances(entries: dict[int, int]) -> BalanceTable:
    balances = BalanceTable()
    for sender_id, amount in entries.items():
        balances.set(_sender(sender_id), ASSET0, amount)
        balances.set(_sender(sender_id), ASSET1, 0)
    return balances


def _copy_balances(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, amount)
    return copied


def _better_ab_key(candidate: tuple[int, int, tuple[str, ...]], best: tuple[int, int, tuple[str, ...]]) -> bool:
    cand_a, cand_b, cand_ids = candidate
    best_a, best_b, best_ids = best
    if cand_a != best_a:
        return cand_a > best_a
    if cand_b != best_b:
        return cand_b > best_b
    return cand_ids < best_ids


def _actual_execution_key(
    ordering: list[Intent],
    pool: PoolState,
    balances: BalanceTable,
) -> tuple[int, int, tuple[str, ...]]:
    """Independent execution oracle for same-direction exact-in batches."""
    balances_scratch = _copy_balances(balances)
    reserve_in = int(pool.reserve0)
    reserve_out = int(pool.reserve1)
    total_a = 0
    total_b = 0

    from src.core.amm_dispatch import swap_exact_in_for_pool

    for intent in ordering:
        amount_in = int(intent.get_field("amount_in"))
        min_amount_out = int(intent.get_field("min_amount_out", 0))
        sender = intent.sender_pubkey

        if balances_scratch.get(sender, ASSET0) < amount_in:
            continue

        try:
            amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in_for_pool(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=amount_in,
            )
        except Exception:
            continue

        if amount_out < min_amount_out:
            continue

        balances_scratch.subtract(sender, ASSET0, amount_in)
        reserve_in, reserve_out = new_reserve_in, new_reserve_out
        total_a += amount_in
        total_b += amount_out - min_amount_out

    return total_a, total_b, tuple(intent.intent_id for intent in ordering)


def _best_execution_key(
    intents: list[Intent],
    pool: PoolState,
    balances: BalanceTable,
) -> tuple[int, int, tuple[str, ...]]:
    best = (-1, -1, tuple())
    for ordering in itertools.permutations(intents):
        key = _actual_execution_key(list(ordering), pool, balances)
        if best == (-1, -1, tuple()) or _better_ab_key(key, best):
            best = key
    return best


def _fill_signature(fills: list[Fill]) -> tuple[tuple[str, str, str | None, int | None, int | None], ...]:
    return tuple(
        (
            fill.intent_id,
            fill.action.value,
            fill.reason,
            fill.amount_in_filled,
            fill.amount_out_filled,
        )
        for fill in fills
    )


@st.composite
def _exact_in_batch(draw: st.DrawFn) -> tuple[PoolState, list[Intent], BalanceTable]:
    reserve0 = draw(st.integers(min_value=500, max_value=20_000))
    reserve1 = draw(st.integers(min_value=500, max_value=20_000))
    fee_bps = draw(st.integers(min_value=0, max_value=100))
    intent_count = draw(st.integers(min_value=1, max_value=5))
    sender_count = draw(st.integers(min_value=1, max_value=3))

    amounts_in: list[int] = []
    min_amounts_out: list[int] = []
    senders: list[int] = []
    sender_totals = {sender_id: 0 for sender_id in range(1, sender_count + 1)}

    for _ in range(intent_count):
        amount_in = draw(st.integers(min_value=1, max_value=min(3_000, reserve0)))
        min_amount_out = draw(st.integers(min_value=0, max_value=min(3_000, reserve1)))
        sender_id = draw(st.integers(min_value=1, max_value=sender_count))
        amounts_in.append(amount_in)
        min_amounts_out.append(min_amount_out)
        senders.append(sender_id)
        sender_totals[sender_id] += amount_in

    balances_by_sender = {
        sender_id: draw(st.integers(min_value=0, max_value=max(1, total + 500)))
        for sender_id, total in sender_totals.items()
    }

    pool = _make_pool(reserve0=reserve0, reserve1=reserve1, fee_bps=fee_bps)
    intents = [
        _make_intent(
            idx=idx,
            sender_id=senders[idx],
            amount_in=amounts_in[idx],
            min_amount_out=min_amounts_out[idx],
        )
        for idx in range(intent_count)
    ]
    balances = _make_balances(balances_by_sender)
    return pool, intents, balances


@st.composite
def _same_direction_swaps(draw: st.DrawFn) -> tuple[PoolState, list[Intent]]:
    reserve0 = draw(st.integers(min_value=500, max_value=20_000))
    reserve1 = draw(st.integers(min_value=500, max_value=20_000))
    fee_bps = draw(st.integers(min_value=0, max_value=100))
    intent_count = draw(st.integers(min_value=2, max_value=6))
    intents = [
        _make_intent(
            idx=idx,
            sender_id=idx + 1,
            amount_in=draw(st.integers(min_value=1, max_value=min(3_000, reserve0))),
            min_amount_out=draw(st.integers(min_value=0, max_value=min(3_000, reserve1))),
        )
        for idx in range(intent_count)
    ]
    return _make_pool(reserve0=reserve0, reserve1=reserve1, fee_bps=fee_bps), intents


@given(batch=_exact_in_batch())
@settings(max_examples=60, deadline=None)
def test_optimal_ab_bounded_matches_bounded_bruteforce_execution(batch: tuple[PoolState, list[Intent], BalanceTable]) -> None:
    pool, intents, balances = batch

    fills = clear_batch_single_pool(
        intents,
        pool,
        balances,
        LPTable(),
        swap_ordering="optimal_ab_bounded",
    )

    ordered_intents = {intent.intent_id: intent for intent in intents}
    chosen_order = [ordered_intents[fill.intent_id] for fill in fills]
    chosen_key = _actual_execution_key(chosen_order, pool, balances)
    best_key = _best_execution_key(intents, pool, balances)

    assert chosen_key == best_key


@given(batch=_exact_in_batch())
@settings(max_examples=60, deadline=None)
def test_optimal_ab_bounded_is_input_permutation_invariant(batch: tuple[PoolState, list[Intent], BalanceTable]) -> None:
    pool, intents, balances = batch

    fills_forward = clear_batch_single_pool(
        intents,
        pool,
        balances,
        LPTable(),
        swap_ordering="optimal_ab_bounded",
    )
    fills_reversed = clear_batch_single_pool(
        list(reversed(intents)),
        pool,
        balances,
        LPTable(),
        swap_ordering="optimal_ab_bounded",
    )

    assert _fill_signature(fills_forward) == _fill_signature(fills_reversed)


@given(batch=_same_direction_swaps())
@settings(max_examples=80, deadline=None)
def test_ab_refinement_chain_never_degrades_ordering(batch: tuple[PoolState, list[Intent]]) -> None:
    pool, intents = batch
    reserves = (pool.reserve0, pool.reserve1)

    limit_order = _order_swaps_limit_price(intents)
    greedy_order = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
    refined_order = _refine_b_ordering(greedy_order, pool_state=pool, reserves=reserves)
    global_order = _refine_ab_ordering_global(refined_order, pool_state=pool, reserves=reserves)

    limit_ab = _eval_ordering_ab(limit_order, pool, reserves)
    greedy_ab = _eval_ordering_ab(greedy_order, pool, reserves)
    refined_ab = _eval_ordering_ab(refined_order, pool, reserves)
    global_ab = _eval_ordering_ab(global_order, pool, reserves)

    assert greedy_ab >= limit_ab
    assert refined_ab >= greedy_ab
    assert global_ab >= refined_ab


def test_optimal_ab_bounded_rejects_shared_sender_overdraw_deterministically() -> None:
    pool = _make_pool(reserve0=5_000, reserve1=5_000, fee_bps=30)
    balances = _make_balances({1: 700, 2: 700})
    intents = [
        _make_intent(idx=0, sender_id=1, amount_in=400, min_amount_out=0),
        _make_intent(idx=1, sender_id=1, amount_in=400, min_amount_out=0),
        _make_intent(idx=2, sender_id=2, amount_in=300, min_amount_out=0),
    ]

    fills = clear_batch_single_pool(
        intents,
        pool,
        balances,
        LPTable(),
        swap_ordering="optimal_ab_bounded",
    )

    assert [fill.intent_id for fill in fills] == [_iid(0), _iid(1), _iid(2)]
    assert sum(fill.action == FillAction.FILL for fill in fills) == 2
    assert sum(fill.action == FillAction.REJECT for fill in fills) == 1
