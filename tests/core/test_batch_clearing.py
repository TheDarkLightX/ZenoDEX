# [TESTER] v1

from __future__ import annotations

from src.core.batch_clearing import compute_settlement, validate_settlement, clear_batch_single_pool
from src.core.liquidity import create_pool
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
