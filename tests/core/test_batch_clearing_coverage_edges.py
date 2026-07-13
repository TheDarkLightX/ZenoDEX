from __future__ import annotations

import src.core.batch_clearing as batch_clearing_module
from src.core.batch_clearing import _cow_pair_netting_exact_in_v1, _refine_ab_ordering_global
from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_cow_pair_netting_falls_back_when_aggregate_debit_check_fails_closed(monkeypatch) -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool = PoolState(
        pool_id=compute_pool_id(asset0, asset1, 30),
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk_a, asset0, 100)
    balances.set(pk_b, asset1, 200)

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(3001),
            sender_pubkey=pk_a,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 150,
            },
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(3002),
            sender_pubkey=pk_b,
            deadline=9999999999,
            fields={
                "pool_id": pool.pool_id,
                "asset_in": asset1,
                "asset_out": asset0,
                "amount_in": 200,
                "min_amount_out": 90,
            },
        ),
    ]

    call_counter = {"n": 0}
    original_get = balances.get

    def _stateful_get(pubkey: str, asset: str) -> int:
        call_counter["n"] += 1
        if call_counter["n"] <= 2:
            return int(original_get(pubkey, asset))
        return 0

    monkeypatch.setattr(balances, "get", _stateful_get)
    fills, remaining = _cow_pair_netting_exact_in_v1(intents, pool_state=pool, balances=balances)
    assert fills == []
    assert [it.intent_id for it in remaining] == sorted([it.intent_id for it in intents])
    assert original_get(pk_a, asset0) == 100
    assert original_get(pk_b, asset1) == 200


def test_refine_ab_ordering_global_can_exhaust_pass_budget_with_monotone_improvements(monkeypatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    _pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    reserves = (pool.reserve0, pool.reserve1)

    order = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(3101),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"asset_in": asset0, "asset_out": asset1, "amount_in": 100, "min_amount_out": 1},
        ),
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(3102),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={"asset_in": asset0, "asset_out": asset1, "amount_in": 120, "min_amount_out": 1},
        ),
    ]

    counter = {"n": 0}

    def _monotone_eval(ordering: list[Intent], *_args: object) -> tuple[int, int]:
        counter["n"] += 1
        return counter["n"], counter["n"]

    monkeypatch.setattr(batch_clearing_module, "_eval_ordering_ab", _monotone_eval)
    refined = _refine_ab_ordering_global(order, pool_state=pool, reserves=reserves)
    assert sorted(it.intent_id for it in refined) == sorted(it.intent_id for it in order)
    assert counter["n"] >= 3
