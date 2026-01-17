# [TESTER] v1

from __future__ import annotations

from src.core.intent_access import partition_independent_intents
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_partition_splits_intents_that_touch_disjoint_state() -> None:
    pk1 = "0x" + "11" * 48
    pk2 = "0x" + "22" * 48

    a0 = "0x" + "01" * 32
    a1 = "0x" + "02" * 32
    b0 = "0x" + "03" * 32
    b1 = "0x" + "04" * 32

    pool1 = "0x" + "aa" * 32
    pool2 = "0x" + "bb" * 32

    pools = {
        pool1: PoolState(pool_id=pool1, asset0=a0, asset1=a1, reserve0=1000, reserve1=2000, fee_bps=30, lp_supply=1, status=PoolStatus.ACTIVE, created_at=0),
        pool2: PoolState(pool_id=pool2, asset0=b0, asset1=b1, reserve0=1000, reserve1=2000, fee_bps=30, lp_supply=1, status=PoolStatus.ACTIVE, created_at=0),
    }

    swap1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={"pool_id": pool1, "asset_in": a0, "asset_out": a1, "amount_in": 10, "min_amount_out": 1},
    )
    swap2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=pk2,
        deadline=9999999999,
        fields={"pool_id": pool2, "asset_in": b0, "asset_out": b1, "amount_in": 10, "min_amount_out": 1},
    )

    groups = partition_independent_intents([swap1, swap2], pools=pools)
    assert len(groups) == 2
    assert {g[0].intent_id for g in groups} == {swap1.intent_id, swap2.intent_id}


def test_partition_groups_intents_that_write_same_pool() -> None:
    pk1 = "0x" + "11" * 48
    pk2 = "0x" + "22" * 48

    a0 = "0x" + "01" * 32
    a1 = "0x" + "02" * 32
    pool1 = "0x" + "aa" * 32

    pools = {
        pool1: PoolState(pool_id=pool1, asset0=a0, asset1=a1, reserve0=1000, reserve1=2000, fee_bps=30, lp_supply=1, status=PoolStatus.ACTIVE, created_at=0),
    }

    swap1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={"pool_id": pool1, "asset_in": a0, "asset_out": a1, "amount_in": 10, "min_amount_out": 1},
    )
    swap2 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=pk2,
        deadline=9999999999,
        fields={"pool_id": pool1, "asset_in": a0, "asset_out": a1, "amount_in": 10, "min_amount_out": 1},
    )

    groups = partition_independent_intents([swap1, swap2], pools=pools)
    assert len(groups) == 1
    assert [i.intent_id for i in groups[0]] == [swap1.intent_id, swap2.intent_id]


def test_partition_treats_add_liquidity_into_new_pool_as_reading_sender_assets() -> None:
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
        },
    )
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(2),
        sender_pubkey=pk_b,
        deadline=9999999999,
        fields={"pool_id": pool_id, "amount0_desired": 10, "amount1_desired": 20, "amount0_min": 0, "amount1_min": 0},
    )

    # If add_liq didn't read pk_b's balances, it could be (incorrectly) grouped as independent
    # from other intents that write pk_b's balances in those assets. Use a dummy swap that writes pk_b/a0.
    pool_other = "0x" + "aa" * 32
    pools = {
        pool_other: PoolState(pool_id=pool_other, asset0=asset0, asset1=asset1, reserve0=1000, reserve1=2000, fee_bps=30, lp_supply=1, status=PoolStatus.ACTIVE, created_at=0),
    }
    swap_touching_pkb = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(3),
        sender_pubkey=pk_b,
        deadline=9999999999,
        fields={"pool_id": pool_other, "asset_in": asset0, "asset_out": asset1, "amount_in": 1, "min_amount_out": 0},
    )

    groups = partition_independent_intents([create_pool, add_liq, swap_touching_pkb], pools=pools)
    # add_liq and swap_touching_pkb must be in the same component via pk_b asset access.
    group_ids = [{i.intent_id for i in g} for g in groups]
    assert any({add_liq.intent_id, swap_touching_pkb.intent_id}.issubset(s) for s in group_ids)
