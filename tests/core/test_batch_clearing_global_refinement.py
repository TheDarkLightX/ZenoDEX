"""Tests for global AB refinement ordering (`greedy_ab_global`).

This mode extends `greedy_ab_refined` with deterministic non-adjacent pair swaps
that can improve `(A, B)` beyond adjacent-only local optima.
"""

from __future__ import annotations

from src.core.batch_clearing import (
    _eval_ordering_ab,
    _order_swaps_greedy_ab,
    _refine_ab_ordering_global,
    _refine_b_ordering,
    clear_batch_single_pool,
    compute_settlement,
    validate_settlement,
)
from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


PK = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _make_pool(reserve0: int = 2_000_000, reserve1: int = 2_000_000, fee_bps: int = 30) -> PoolState:
    _pool_id, pool, _ = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=reserve0,
        amount1=reserve1,
        fee_bps=fee_bps,
        creator_pubkey=PK,
        created_at=0,
    )
    return pool


def _make_swap_intent(intent_id: int, amount_in: int, min_amount_out: int, sender_hex_byte: int) -> Intent:
    sender = "0x" + f"{sender_hex_byte:02x}" * 48
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_id),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def test_global_refinement_no_worse_than_adjacent_refinement() -> None:
    pool = _make_pool()
    reserves = (pool.reserve0, pool.reserve1)

    intents = [
        _make_swap_intent(0, 90_000, 10_000, 1),
        _make_swap_intent(1, 70_000, 20_000, 2),
        _make_swap_intent(2, 55_000, 15_000, 3),
        _make_swap_intent(3, 45_000, 5_000, 4),
        _make_swap_intent(4, 110_000, 40_000, 5),
        _make_swap_intent(5, 35_000, 1_000, 6),
    ]

    greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
    refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
    global_refined = _refine_ab_ordering_global(refined, pool_state=pool, reserves=reserves)

    refined_ab = _eval_ordering_ab(refined, pool, reserves)
    global_ab = _eval_ordering_ab(global_refined, pool, reserves)

    assert global_ab >= refined_ab


def test_global_refinement_finds_known_better_ordering_witness() -> None:
    """Regression witness: non-adjacent swap improves B by +1 with A unchanged."""
    pool = _make_pool()
    reserves = (pool.reserve0, pool.reserve1)

    # Witness mined via deterministic search.
    intents = [
        _make_swap_intent(0, 103_230, 25_797, 1),
        _make_swap_intent(1, 45_824, 13_708, 2),
        _make_swap_intent(2, 57_345, 25_765, 3),
        _make_swap_intent(3, 79_287, 74_537, 4),
        _make_swap_intent(4, 61_193, 1_633, 5),
        _make_swap_intent(5, 100_057, 43_724, 6),
    ]

    greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
    refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
    global_refined = _refine_ab_ordering_global(refined, pool_state=pool, reserves=reserves)

    refined_ab = _eval_ordering_ab(refined, pool, reserves)
    global_ab = _eval_ordering_ab(global_refined, pool, reserves)

    assert global_ab > refined_ab
    assert global_ab[0] == refined_ab[0]
    assert global_ab[1] == refined_ab[1] + 1


def test_greedy_ab_global_mode_is_accepted_and_valid() -> None:
    pool = _make_pool()
    pools = {pool.pool_id: pool}
    balances = BalanceTable()
    lp = LPTable()

    for i in range(1, 10):
        sender = "0x" + f"{i:02x}" * 48
        balances.set(sender, ASSET0, 10_000_000)
        balances.set(sender, ASSET1, 10_000_000)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(i),
            sender_pubkey="0x" + f"{(i+1):02x}" * 48,
            deadline=9_999_999_999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": ASSET0,
                "asset_out": ASSET1,
                "amount_in": 20_000 + i * 3_000,
                "min_amount_out": i * 1_000,
            },
        )
        for i in range(6)
    ]

    settlement = compute_settlement(intents, pools, balances, lp, swap_ordering="greedy_ab_global")
    ok, err = validate_settlement(settlement, balances, pools, lp)
    assert ok, err

    fills_global = clear_batch_single_pool(intents, pool, balances, lp, swap_ordering="greedy_ab_global")
    fills_refined = clear_batch_single_pool(intents, pool, balances, lp, swap_ordering="greedy_ab_refined")
    a_global = sum(f.amount_in_filled or 0 for f in fills_global if f.action.value == "FILL")
    a_refined = sum(f.amount_in_filled or 0 for f in fills_refined if f.action.value == "FILL")
    assert a_global >= a_refined
