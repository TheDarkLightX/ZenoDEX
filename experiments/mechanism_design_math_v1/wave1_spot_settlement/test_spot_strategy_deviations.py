"""Wave 1 spot-settlement strategy-deviation evidence.

These tests bind participant-side spot obligations to the implemented
`compute_settlement` functional core. They cover:

- H-MD-SS-001 / O-SS-01: tight `min_amount_out` can buy execution priority.
- H-MD-SS-004 / O-SS-04: free `intent_id` choice has positive tie value.
- H-MD-SS-007 / O-SS-06: CoW self-netting captures fees/spread relative to
  pool execution.

They are research evidence only. They do not change settlement behavior.
"""

from __future__ import annotations

from src.core.batch_clearing import compute_settlement, validate_settlement
from src.core.settlement import Fill, FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _pool(*, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id="pool_ab",
        asset0="A",
        asset1="B",
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _swap(
    intent_n: int,
    sender: str,
    *,
    amount_in: int,
    min_amount_out: int,
    asset_in: str = "A",
    asset_out: str = "B",
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(intent_n),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={
            "pool_id": "pool_ab",
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _balances(*entries: tuple[str, str, int]) -> BalanceTable:
    balances = BalanceTable()
    for pubkey, asset, amount in entries:
        balances.set(pubkey, asset, amount)
    return balances


def _fill(settlement, intent_n: int) -> Fill:
    intent_id = _iid(intent_n)
    matches = [fill for fill in settlement.fills if fill.intent_id == intent_id]
    assert len(matches) == 1
    return matches[0]


def _assert_valid(settlement, pools, balances, lp_balances) -> None:
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err


# ---------------------------------------------------------------------------
# H-MD-SS-001 / O-SS-01: tight min_out can buy greedy priority.
# ---------------------------------------------------------------------------


def test_h_md_ss_001_tight_min_out_buys_greedy_priority() -> None:
    """A tighter executable min_out flips execution order and raises output."""

    pools = {"pool_ab": _pool(fee_bps=0)}
    balances = _balances(("bob", "A", 100_000), ("alice", "A", 100_000))
    lp_balances = LPTable()

    loose = compute_settlement(
        [
            _swap(1, "bob", amount_in=10_000, min_amount_out=0),
            _swap(2, "alice", amount_in=10_000, min_amount_out=0),
        ],
        pools,
        balances,
        lp_balances,
        swap_ordering="greedy_ab",
    )
    _assert_valid(loose, pools, balances, lp_balances)
    assert [fill.intent_id for fill in loose.fills] == [_iid(1), _iid(2)]
    assert _fill(loose, 2).amount_out_filled == 9_706

    tight = compute_settlement(
        [
            _swap(1, "bob", amount_in=10_000, min_amount_out=0),
            _swap(2, "alice", amount_in=10_000, min_amount_out=9_000),
        ],
        pools,
        balances,
        lp_balances,
        swap_ordering="greedy_ab",
    )
    _assert_valid(tight, pools, balances, lp_balances)
    assert [fill.intent_id for fill in tight.fills] == [_iid(2), _iid(1)]
    assert _fill(tight, 2).amount_out_filled == 9_900
    assert _fill(tight, 2).amount_out_filled > _fill(loose, 2).amount_out_filled


# ---------------------------------------------------------------------------
# H-MD-SS-004 / O-SS-04: tie-break value is strictly positive.
# ---------------------------------------------------------------------------


def test_h_md_ss_004_intent_id_tie_break_has_positive_output_value() -> None:
    """Identical swaps tie-break by intent_id, and first position earns more."""

    pools = {"pool_ab": _pool(fee_bps=0)}
    balances = _balances(("low", "A", 100_000), ("high", "A", 100_000))
    lp_balances = LPTable()
    settlement = compute_settlement(
        [
            _swap(2, "high", amount_in=10_000, min_amount_out=0),
            _swap(1, "low", amount_in=10_000, min_amount_out=0),
        ],
        pools,
        balances,
        lp_balances,
        swap_ordering="limit_price",
    )
    _assert_valid(settlement, pools, balances, lp_balances)

    assert [fill.intent_id for fill in settlement.fills] == [_iid(1), _iid(2)]
    assert _fill(settlement, 1).amount_out_filled == 9_900
    assert _fill(settlement, 2).amount_out_filled == 9_706
    assert _fill(settlement, 1).amount_out_filled - _fill(settlement, 2).amount_out_filled == 194


# ---------------------------------------------------------------------------
# H-MD-SS-007 / O-SS-06: self-netting captures pool fees/spread.
# ---------------------------------------------------------------------------


def test_h_md_ss_007_cow_self_netting_captures_fee_and_spread() -> None:
    """A self-supplied counter-intent nets at zero fee and no reserve movement."""

    intents = [
        _swap(1, "self", amount_in=100, min_amount_out=90, asset_in="A", asset_out="B"),
        _swap(2, "self", amount_in=100, min_amount_out=90, asset_in="B", asset_out="A"),
    ]
    balances = _balances(("self", "A", 1_000), ("self", "B", 1_000))
    lp_balances = LPTable()

    cow_pools = {"pool_ab": _pool(fee_bps=30)}
    cow = compute_settlement(
        intents,
        cow_pools,
        balances,
        lp_balances,
        swap_ordering="cow_pair_netting_v1",
    )
    _assert_valid(cow, cow_pools, balances, lp_balances)
    assert all(fill.action == FillAction.FILL for fill in cow.fills)
    assert all(fill.reason == "COW_NETTED" for fill in cow.fills)
    assert sum(fill.fee_paid or 0 for fill in cow.fills) == 0
    assert cow.reserve_deltas == []
    assert _fill(cow, 1).amount_out_filled == 100
    assert _fill(cow, 2).amount_out_filled == 100

    pool_pools = {"pool_ab": _pool(fee_bps=30)}
    pool_execution = compute_settlement(
        intents,
        pool_pools,
        balances,
        lp_balances,
        swap_ordering="optimal_ab_bounded",
    )
    _assert_valid(pool_execution, pool_pools, balances, lp_balances)
    assert sum(fill.fee_paid or 0 for fill in pool_execution.fills) == 2
    assert pool_execution.reserve_deltas != []
    assert _fill(pool_execution, 1).amount_out_filled == 98
    assert _fill(pool_execution, 2).amount_out_filled == 99
