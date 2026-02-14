"""Tests for B-refinement pass in batch clearing (H-BC-001).

Validates that the greedy_ab_refined ordering improves surplus (B) without
decreasing volume (A) compared to the base greedy_ab ordering.
"""

from __future__ import annotations

import pytest

from src.core.batch_clearing import (
    clear_batch_single_pool,
    compute_settlement,
    validate_settlement,
    _eval_ordering_ab,
    _order_swaps_greedy_ab,
    _refine_b_ordering,
)
from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


PK = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _make_pool(reserve0: int = 2_000_000, reserve1: int = 2_000_000, fee_bps: int = 30) -> PoolState:
    pool_id, pool, _ = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=reserve0,
        amount1=reserve1,
        fee_bps=fee_bps,
        creator_pubkey=PK,
        created_at=0,
    )
    return pool


def _make_swap_intent(
    intent_id: int,
    amount_in: int,
    min_amount_out: int = 0,
    sender: str = PK,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_id),
        sender_pubkey=sender,
        deadline=9999999999,
        fields={
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


class TestBRefinementBasics:
    """Basic functionality of the B-refinement pass."""

    def test_single_intent_unchanged(self):
        """Single intent: refinement should not change anything."""
        pool = _make_pool()
        intent = _make_swap_intent(1, 1000)
        reserves = (pool.reserve0, pool.reserve1)

        greedy = _order_swaps_greedy_ab([intent], pool_state=pool, reserves=reserves)
        refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
        assert len(refined) == 1
        assert refined[0].intent_id == intent.intent_id

    def test_empty_list_unchanged(self):
        """Empty list: refinement returns empty list."""
        pool = _make_pool()
        reserves = (pool.reserve0, pool.reserve1)
        refined = _refine_b_ordering([], pool_state=pool, reserves=reserves)
        assert refined == []

    def test_a_never_decreases(self):
        """B-refinement must never decrease A."""
        pool = _make_pool()
        reserves = (pool.reserve0, pool.reserve1)

        # Create intents with different slippage tolerances.
        intents = [
            _make_swap_intent(0, 10000, min_amount_out=0),
            _make_swap_intent(1, 10000, min_amount_out=5000),
            _make_swap_intent(2, 10000, min_amount_out=3000),
        ]

        greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
        greedy_a, greedy_b = _eval_ordering_ab(greedy, pool, reserves)

        refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
        refined_a, refined_b = _eval_ordering_ab(refined, pool, reserves)

        assert refined_a >= greedy_a, f"A decreased: {refined_a} < {greedy_a}"

    def test_b_improves_or_stays(self):
        """B-refinement must improve B or leave it unchanged."""
        pool = _make_pool()
        reserves = (pool.reserve0, pool.reserve1)

        intents = [
            _make_swap_intent(0, 10000, min_amount_out=0),
            _make_swap_intent(1, 10000, min_amount_out=5000),
            _make_swap_intent(2, 10000, min_amount_out=3000),
        ]

        greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
        greedy_a, greedy_b = _eval_ordering_ab(greedy, pool, reserves)

        refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
        refined_a, refined_b = _eval_ordering_ab(refined, pool, reserves)

        # If A is the same, B should be >= greedy B.
        if refined_a == greedy_a:
            assert refined_b >= greedy_b, f"B decreased: {refined_b} < {greedy_b}"


class TestBRefinementImprovement:
    """Verify B-refinement actually improves B in cases where greedy is B-suboptimal."""

    def test_refinement_improves_b_varied_slippage(self):
        """Intents with varied slippage should benefit from B-refinement.

        Greedy_ab puts tightest-slippage first, which is A-optimal but may
        leave B on the table. Reordering can improve surplus without
        losing volume.
        """
        pool = _make_pool(reserve0=1_000_000, reserve1=1_000_000, fee_bps=30)
        reserves = (pool.reserve0, pool.reserve1)

        # Intent 0: very tolerant (0 min_out) -- high surplus
        # Intent 1: tight slippage -- low surplus
        # Intent 2: moderate slippage
        intents = [
            _make_swap_intent(0, 50000, min_amount_out=0),
            _make_swap_intent(1, 50000, min_amount_out=40000),
            _make_swap_intent(2, 50000, min_amount_out=20000),
        ]

        greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
        greedy_a, greedy_b = _eval_ordering_ab(greedy, pool, reserves)

        refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
        refined_a, refined_b = _eval_ordering_ab(refined, pool, reserves)

        # A must not decrease.
        assert refined_a >= greedy_a
        # B should be at least as good.
        assert refined_b >= greedy_b

    def test_refinement_with_many_intents(self):
        """Larger batch: verify invariant holds for many intents."""
        pool = _make_pool(reserve0=10_000_000, reserve1=10_000_000, fee_bps=30)
        reserves = (pool.reserve0, pool.reserve1)

        # Generate sender-distinct intents with varied slippage.
        senders = ["0x" + f"{i:02x}" * 48 for i in range(1, 9)]
        intents = []
        for i, sender in enumerate(senders):
            min_out = i * 500  # Increasing slippage tolerance
            intents.append(
                Intent(
                    module="TauSwap",
                    version="0.1",
                    kind=IntentKind.SWAP_EXACT_IN,
                    intent_id=_iid(i),
                    sender_pubkey=sender,
                    deadline=9999999999,
                    fields={
                        "asset_in": ASSET0,
                        "asset_out": ASSET1,
                        "amount_in": 10000,
                        "min_amount_out": min_out,
                    },
                )
            )

        greedy = _order_swaps_greedy_ab(intents, pool_state=pool, reserves=reserves)
        greedy_a, greedy_b = _eval_ordering_ab(greedy, pool, reserves)

        refined = _refine_b_ordering(greedy, pool_state=pool, reserves=reserves)
        refined_a, refined_b = _eval_ordering_ab(refined, pool, reserves)

        assert refined_a >= greedy_a
        assert refined_b >= greedy_b


class TestBRefinementIntegration:
    """Integration: greedy_ab_refined ordering through compute_settlement."""

    def test_greedy_ab_refined_accepted(self):
        """greedy_ab_refined is a valid swap_ordering choice."""
        pool = _make_pool()
        pools = {pool.pool_id: pool}
        balances = BalanceTable()
        balances.set(PK, ASSET0, 10_000_000)
        balances.set(PK, ASSET1, 10_000_000)
        lp = LPTable()

        intents = [
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(1),
                sender_pubkey=PK,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": 1000,
                    "min_amount_out": 1,
                },
            )
        ]

        settlement = compute_settlement(intents, pools, balances, lp, swap_ordering="greedy_ab_refined")
        ok, err = validate_settlement(settlement, balances, pools, lp)
        assert ok, err

    def test_greedy_ab_refined_settlement_valid(self):
        """Settlement via greedy_ab_refined passes conservation validation."""
        pool = _make_pool()
        pools = {pool.pool_id: pool}
        balances = BalanceTable()
        balances.set(PK, ASSET0, 10_000_000)
        balances.set(PK, ASSET1, 10_000_000)
        lp = LPTable()

        intents = [
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(i),
                sender_pubkey=PK,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": 10000,
                    "min_amount_out": i * 100,
                },
            )
            for i in range(5)
        ]

        settlement = compute_settlement(intents, pools, balances, lp, swap_ordering="greedy_ab_refined")
        ok, err = validate_settlement(settlement, balances, pools, lp)
        assert ok, err

    def test_greedy_ab_refined_at_least_as_good_as_greedy(self):
        """greedy_ab_refined should produce (A,B) >= greedy_ab."""
        pool = _make_pool()
        reserves = (pool.reserve0, pool.reserve1)
        balances = BalanceTable()
        balances.set(PK, ASSET0, 10_000_000)
        lp = LPTable()

        intents = [
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(i),
                sender_pubkey=PK,
                deadline=9999999999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": 10000,
                    "min_amount_out": i * 1000,
                },
            )
            for i in range(4)
        ]

        fills_greedy = clear_batch_single_pool(intents, pool, balances, lp, swap_ordering="greedy_ab")
        fills_refined = clear_batch_single_pool(intents, pool, balances, lp, swap_ordering="greedy_ab_refined")

        # Count volume (A) from fills.
        a_greedy = sum(f.amount_in_filled or 0 for f in fills_greedy if f.action.value == "FILL")
        a_refined = sum(f.amount_in_filled or 0 for f in fills_refined if f.action.value == "FILL")

        assert a_refined >= a_greedy, f"Refined A ({a_refined}) < greedy A ({a_greedy})"
