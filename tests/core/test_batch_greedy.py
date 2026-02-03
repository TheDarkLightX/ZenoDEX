"""Tests for greedy AB-optimal batch approximation (WS5)."""

from __future__ import annotations

from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.core.batch_clearing import (
    _SWAP_ORDERING_GREEDY_AB,
    _SWAP_ORDERING_LIMIT_PRICE,
    _SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
    clear_batch_single_pool,
    compute_settlement,
)
from src.core.settlement import FillAction


def _make_pool(reserve0: int = 1_000_000, reserve1: int = 1_000_000, fee_bps: int = 30) -> PoolState:
    return PoolState(
        pool_id="pool_ab",
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _make_swap(
    intent_id: str,
    sender: str,
    amount_in: int,
    min_amount_out: int = 0,
    asset_in: str = "A",
    asset_out: str = "B",
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        intent_id="0x" + intent_id.ljust(64, "0"),
        sender_pubkey=sender,
        kind=IntentKind.SWAP_EXACT_IN,
        deadline=999999999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _make_balances(*pairs: tuple[str, str, int]) -> BalanceTable:
    bt = BalanceTable()
    for pubkey, asset, amount in pairs:
        bt.set(pubkey, asset, amount)
    return bt


# ---------------------------------------------------------------------------
# Basic greedy ordering
# ---------------------------------------------------------------------------

def test_greedy_single_swap() -> None:
    """Single swap should pass through unchanged."""
    pool = _make_pool()
    intents = [_make_swap("s1", "alice", 10000)]
    balances = _make_balances(("alice", "A", 1_000_000))

    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    assert len(fills) == 1
    assert fills[0].action == FillAction.FILL


def test_greedy_two_swaps_deterministic() -> None:
    """Two swaps should be ordered deterministically (by best marginal AB)."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 50000),
        _make_swap("s2", "bob", 10000),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
    )

    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    filled = [f for f in fills if f.action == FillAction.FILL]
    assert len(filled) == 2

    # Total A (volume) should be sum of both amounts
    total_a = sum(f.amount_in_filled or 0 for f in filled)
    assert total_a == 60000


def test_greedy_matches_brute_force_small_n() -> None:
    """For small N, greedy should produce same total A as brute force."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 10000),
        _make_swap("s2", "bob", 20000),
        _make_swap("s3", "carol", 15000),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
        ("carol", "A", 1_000_000),
    )

    greedy_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    brute_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_OPTIMAL_AB_BOUNDED,
    )

    greedy_a = sum(f.amount_in_filled or 0 for f in greedy_fills if f.action == FillAction.FILL)
    brute_a = sum(f.amount_in_filled or 0 for f in brute_fills if f.action == FillAction.FILL)

    # Greedy should be at least as good as limit price for A
    assert greedy_a == brute_a


def test_greedy_at_least_limit_price() -> None:
    """Greedy A must be >= limit_price A for same-direction batches."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 10000, min_amount_out=5000),
        _make_swap("s2", "bob", 50000, min_amount_out=30000),
        _make_swap("s3", "carol", 20000),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
        ("carol", "A", 1_000_000),
    )

    greedy_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    limit_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_LIMIT_PRICE,
    )

    greedy_a = sum(f.amount_in_filled or 0 for f in greedy_fills if f.action == FillAction.FILL)
    limit_a = sum(f.amount_in_filled or 0 for f in limit_fills if f.action == FillAction.FILL)

    assert greedy_a >= limit_a


# ---------------------------------------------------------------------------
# Conservation
# ---------------------------------------------------------------------------

def test_greedy_conservation() -> None:
    """Settlement from greedy ordering must pass conservation validation."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 10000),
        _make_swap("s2", "bob", 20000),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
    )

    settlement = compute_settlement(
        intents,
        {"pool_ab": pool},
        balances,
        LPTable(),
        swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )

    from src.core.batch_clearing import validate_settlement
    valid, err = validate_settlement(settlement, balances, {"pool_ab": pool}, LPTable())
    assert valid, f"Conservation violation: {err}"


# ---------------------------------------------------------------------------
# Determinism
# ---------------------------------------------------------------------------

def test_greedy_deterministic_tiebreak() -> None:
    """Equal-AB swaps should tie-break by intent_id (lexicographic)."""
    pool = _make_pool()
    intents = [
        _make_swap("s2", "alice", 10000),
        _make_swap("s1", "bob", 10000),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
    )

    fills1 = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    # Reverse input order
    fills2 = clear_batch_single_pool(
        list(reversed(intents)), pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )

    ids1 = [f.intent_id for f in fills1 if f.action == FillAction.FILL]
    ids2 = [f.intent_id for f in fills2 if f.action == FillAction.FILL]
    assert ids1 == ids2


# ---------------------------------------------------------------------------
# Mixed direction fallback
# ---------------------------------------------------------------------------

def test_greedy_mixed_direction_falls_back() -> None:
    """Mixed-direction swaps should fall back to limit_price ordering."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 10000, asset_in="A", asset_out="B"),
        _make_swap("s2", "bob", 10000, asset_in="B", asset_out="A"),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "B", 1_000_000),
    )

    # Should not crash, falls back to limit price
    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    assert len(fills) == 2


# ---------------------------------------------------------------------------
# Insufficient balance handling
# ---------------------------------------------------------------------------

def test_greedy_insufficient_balance_skips() -> None:
    """Intent with insufficient balance should be skipped, not crash."""
    pool = _make_pool()
    intents = [
        _make_swap("s1", "alice", 10000),
        _make_swap("s2", "bob", 10000),
    ]
    balances = _make_balances(
        ("alice", "A", 10000),
        ("bob", "A", 0),  # Bob has no balance
    )

    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    filled = [f for f in fills if f.action == FillAction.FILL]
    rejected = [f for f in fills if f.action == FillAction.REJECT]
    assert len(filled) == 1
    assert "s1" in filled[0].intent_id


# ---------------------------------------------------------------------------
# Large N performance (smoke test)
# ---------------------------------------------------------------------------

def test_greedy_handles_50_swaps() -> None:
    """Greedy should handle 50 swaps without timeout."""
    pool = _make_pool(reserve0=100_000_000, reserve1=100_000_000)
    intents = [
        _make_swap(f"s{i:03d}", f"user{i}", 10000 + i * 100)
        for i in range(50)
    ]
    balances = _make_balances(
        *[(f"user{i}", "A", 1_000_000) for i in range(50)]
    )

    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    filled = [f for f in fills if f.action == FillAction.FILL]
    assert len(filled) == 50

    total_a = sum(f.amount_in_filled or 0 for f in filled)
    assert total_a > 0


# ---------------------------------------------------------------------------
# Tight-before-loose ordering (Codex counterexample regression)
# ---------------------------------------------------------------------------

def test_greedy_tight_before_loose() -> None:
    """Tight-slippage swaps must execute before loose swaps.

    Codex counterexample: pool (100,100) fee=0, tight swap (in=20, min=16)
    and loose swap (in=60, min=0). Greedy must not pick the large swap first
    and starve the tight swap of reserves.
    """
    pool = _make_pool(reserve0=100, reserve1=100, fee_bps=0)
    intents = [
        _make_swap("tight", "alice", 20, min_amount_out=16),
        _make_swap("loose", "bob", 60, min_amount_out=0),
    ]
    balances = _make_balances(
        ("alice", "A", 1_000_000),
        ("bob", "A", 1_000_000),
    )

    fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    filled = [f for f in fills if f.action == FillAction.FILL]
    total_a = sum(f.amount_in_filled or 0 for f in filled)

    # Both must fill: A = 80 (not 60)
    assert len(filled) == 2
    assert total_a == 80


def test_greedy_never_worse_than_limit_price() -> None:
    """Greedy (A, B) must be >= limit_price (A, B) — hard guarantee.

    Uses the same tight/loose setup but with multiple additional swaps
    to stress-test the comparison logic.
    """
    pool = _make_pool(reserve0=10000, reserve1=10000, fee_bps=30)
    intents = [
        _make_swap("s1", "u1", 500, min_amount_out=450),  # tight
        _make_swap("s2", "u2", 2000, min_amount_out=0),   # very loose
        _make_swap("s3", "u3", 300, min_amount_out=280),   # tight
        _make_swap("s4", "u4", 1000, min_amount_out=0),    # loose
    ]
    balances = _make_balances(
        ("u1", "A", 1_000_000),
        ("u2", "A", 1_000_000),
        ("u3", "A", 1_000_000),
        ("u4", "A", 1_000_000),
    )

    greedy_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_GREEDY_AB,
    )
    limit_fills = clear_batch_single_pool(
        intents, pool, balances, LPTable(), swap_ordering=_SWAP_ORDERING_LIMIT_PRICE,
    )

    greedy_a = sum(f.amount_in_filled or 0 for f in greedy_fills if f.action == FillAction.FILL)
    limit_a = sum(f.amount_in_filled or 0 for f in limit_fills if f.action == FillAction.FILL)

    assert greedy_a >= limit_a
