# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import (
    _aggregate_balance_deltas_chunked,
    _aggregate_lp_deltas_chunked,
    _aggregate_reserve_deltas_chunked,
    clear_batch_single_pool,
    compute_settlement,
    validate_settlement,
)
from src.core.liquidity import create_pool
from src.core.settlement import BalanceDelta, LPDelta, ReserveDelta
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_compute_settlement_does_not_mutate_input_pools() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    pools = {pool_id: pool}
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    lp_balances = LPTable()

    pre_r0 = pool.reserve0
    pre_r1 = pool.reserve1

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        )
    ]

    settlement = compute_settlement(intents, pools, balances, lp_balances)
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err

    # Purity check: original pool object is not mutated by compute_settlement.
    assert pool.reserve0 == pre_r0
    assert pool.reserve1 == pre_r1


def test_batch_clearing_rejects_second_swap_when_overdrawn() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )

    pools = {pool_id: pool}
    balances = BalanceTable()
    balances.set(pk, asset0, 1000)  # only enough for one of the swaps
    balances.set(pk, asset1, 0)
    lp_balances = LPTable()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 1000,
                "min_amount_out": 1,
            },
        ),
    ]

    settlement = compute_settlement(intents, pools, balances, lp_balances)
    ok, err = validate_settlement(settlement, balances, pools, lp_balances)
    assert ok, err

    filled = [f for f in settlement.fills if f.action.value == "FILL"]
    rejected = [f for f in settlement.fills if f.action.value == "REJECT"]
    assert len(filled) == 1
    assert len(rejected) == 1
    assert rejected[0].reason == "INSUFFICIENT_BALANCE"


def test_clear_batch_single_pool_optimal_ab_bounded_canonicalizes_lex_order() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool = PoolState(
        pool_id="0x" + "aa" * 32,
        asset0=asset0,
        asset1=asset1,
        reserve0=100,
        reserve1=100,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 200)
    balances.set(pk, asset1, 0)
    lp_balances = LPTable()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(0),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 0,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(1),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 1,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 50,
                "min_amount_out": 1,
            },
        ),
    ]

    fills_greedy = clear_batch_single_pool(intents, pool, balances, lp_balances)
    assert [f.intent_id for f in fills_greedy] == [_iid(1), _iid(2), _iid(0)]

    fills_ab = clear_batch_single_pool(intents, pool, balances, lp_balances, swap_ordering="optimal_ab_bounded")
    assert [f.intent_id for f in fills_ab] == [_iid(0), _iid(1), _iid(2)]


def test_chunked_delta_aggregation_preserves_semantics_and_order() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset_a = "0x" + "01" * 32
    asset_b = "0x" + "02" * 32
    pool_a = "0x" + "aa" * 32
    pool_b = "0x" + "bb" * 32

    balance_deltas = [
        BalanceDelta(pubkey=pk_b, asset=asset_a, delta_add=7, delta_sub=0),
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=3, delta_sub=2),
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=5, delta_sub=1),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=0, delta_sub=4),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=2, delta_sub=0),
    ]
    expected_balance = [
        BalanceDelta(pubkey=pk_a, asset=asset_a, delta_add=8, delta_sub=3),
        BalanceDelta(pubkey=pk_b, asset=asset_a, delta_add=7, delta_sub=0),
        BalanceDelta(pubkey=pk_b, asset=asset_b, delta_add=2, delta_sub=4),
    ]
    for chunk_size in (1, 2, 3, 128):
        assert _aggregate_balance_deltas_chunked(balance_deltas, chunk_size=chunk_size) == expected_balance

    reserve_deltas = [
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=0, delta_sub=5),
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=10, delta_sub=0),
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=1, delta_sub=2),
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=3, delta_sub=0),
    ]
    expected_reserve = [
        ReserveDelta(pool_id=pool_a, asset=asset_a, delta_add=11, delta_sub=2),
        ReserveDelta(pool_id=pool_b, asset=asset_b, delta_add=3, delta_sub=5),
    ]
    for chunk_size in (1, 2, 5, 128):
        assert _aggregate_reserve_deltas_chunked(reserve_deltas, chunk_size=chunk_size) == expected_reserve

    lp_deltas = [
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=0, delta_sub=2),
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=4, delta_sub=0),
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=1, delta_sub=1),
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=3, delta_sub=0),
    ]
    expected_lp = [
        LPDelta(pubkey=pk_a, pool_id=pool_a, delta_add=5, delta_sub=1),
        LPDelta(pubkey=pk_b, pool_id=pool_b, delta_add=3, delta_sub=2),
    ]
    for chunk_size in (1, 2, 4, 128):
        assert _aggregate_lp_deltas_chunked(lp_deltas, chunk_size=chunk_size) == expected_lp
