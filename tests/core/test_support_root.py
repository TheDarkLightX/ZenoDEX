# [TESTER] v1

from __future__ import annotations

from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import compute_pool_id
from src.state.support_root import compute_support_state_root_for_batch


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_support_root_commits_to_balances_for_add_liquidity_into_new_pool() -> None:
    # Create a pool in-batch, then add liquidity to it from another sender.
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    fee_bps = 30

    pool_id = compute_pool_id(min(asset0, asset1), max(asset0, asset1), fee_bps, curve_tag="CPMM", curve_params="")

    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1),
        sender_pubkey=pk_a,
        deadline=9999999999,
        fields={
            "asset0": min(asset0, asset1),
            "asset1": max(asset0, asset1),
            "fee_bps": fee_bps,
            "amount0": 1000,
            "amount1": 2000,
            "created_at": 1,
        },
    )
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(2),
        sender_pubkey=pk_b,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100,
            "amount1_desired": 200,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    intents = [create_pool, add_liq]

    balances1 = BalanceTable()
    balances1.set(pk_a, min(asset0, asset1), 1000)
    balances1.set(pk_a, max(asset0, asset1), 2000)
    balances1.set(pk_b, min(asset0, asset1), 100)
    balances1.set(pk_b, max(asset0, asset1), 200)

    balances2 = BalanceTable()
    balances2.set(pk_a, min(asset0, asset1), 1000)
    balances2.set(pk_a, max(asset0, asset1), 2000)
    balances2.set(pk_b, min(asset0, asset1), 99)  # differs only here
    balances2.set(pk_b, max(asset0, asset1), 200)

    pools = {}
    lp = LPTable()

    r1 = compute_support_state_root_for_batch(intents=intents, balances=balances1, pools=pools, lp_balances=lp)
    r2 = compute_support_state_root_for_batch(intents=intents, balances=balances2, pools=pools, lp_balances=lp)
    assert r1 != r2

