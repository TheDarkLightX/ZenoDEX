# [TESTER] v1

from __future__ import annotations

import pytest

from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.support_root import (
    BatchStateSupport,
    compute_support_state_root,
    compute_support_state_root_for_batch,
    derive_batch_state_support,
)


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


def _pool(pool_id: str, asset0: str, asset1: str) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=3_000,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )


def test_derive_batch_state_support_tracks_swap_and_remove_liquidity_reads() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")

    swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 10,
            "max_amount_in": 15,
        },
    )
    remove = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "lp_amount": 10},
    )

    support = derive_batch_state_support([swap, remove], pools={pool_id: _pool(pool_id, asset0, asset1)})
    assert support.balance_keys == ((pk, asset0),)
    assert support.pool_ids == (pool_id,)
    assert support.lp_keys == ((pk, pool_id),)


def test_derive_batch_state_support_ignores_invalid_create_pool_fields_fail_closed() -> None:
    pk = "0x" + "11" * 48
    invalid_create = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": 7, "asset1": "0x" + "02" * 32, "fee_bps": True},
    )

    support = derive_batch_state_support([invalid_create], pools={})
    assert support == BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=())


def test_compute_support_state_root_rejects_wrong_table_types() -> None:
    with pytest.raises(TypeError, match="balances must be a BalanceTable"):
        compute_support_state_root(  # type: ignore[arg-type]
            balances={},
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=()),
        )
    with pytest.raises(TypeError, match="lp_balances must be an LPTable"):
        compute_support_state_root(  # type: ignore[arg-type]
            balances=BalanceTable(),
            pools={},
            lp_balances={},
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=()),
        )


def test_compute_support_state_root_omits_missing_pools_and_zero_entries() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    pool_id = "0x" + "aa" * 32
    support = BatchStateSupport(balance_keys=((pk, asset0),), pool_ids=(pool_id,), lp_keys=((pk, pool_id),))

    root_empty = compute_support_state_root(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        support=support,
    )
    root_zero = compute_support_state_root(
        balances=BalanceTable(),
        pools={pool_id: _pool(pool_id, asset0, "0x" + "02" * 32)},
        lp_balances=LPTable(),
        support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=()),
    )
    assert isinstance(root_empty, str) and root_empty.startswith("0x")
    assert root_empty == root_zero


def test_compute_support_state_root_rejects_duplicate_decoded_support_keys() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset = "0x" + "01" * 32
    balances = BalanceTable()
    balances.set(pk, asset, 1)
    lp = LPTable()
    lp.set(pk, pool_id, 1)

    with pytest.raises(ValueError, match="duplicate decoded \\(pubkey, asset\\)"):
        compute_support_state_root(
            balances=balances,
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=((pk, asset), (pk.upper().replace("0X", "0x"), asset)), pool_ids=(), lp_keys=()),
        )

    with pytest.raises(ValueError, match="duplicate decoded pool_id"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: _pool(pool_id, asset, "0x" + "02" * 32), pool_id.upper().replace("0X", "0x"): _pool(pool_id.upper().replace("0X", "0x"), asset, "0x" + "02" * 32)},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id, pool_id.upper().replace("0X", "0x")), lp_keys=()),
        )

    with pytest.raises(ValueError, match="duplicate decoded \\(pubkey, pool_id\\)"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=lp,
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=((pk, pool_id), (pk.upper().replace("0X", "0x"), pool_id))),
        )


def test_compute_support_state_root_rejects_invalid_pool_and_amount_scalars() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")

    balances = BalanceTable()
    balances._balances[(pk, asset0)] = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid balance amount"):
        compute_support_state_root(
            balances=balances,
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=((pk, asset0),), pool_ids=(), lp_keys=()),
        )

    good_balances = BalanceTable()
    good_balances.set(pk, asset0, 10)
    lp = LPTable()
    lp._balances[(pk, pool_id)] = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid LP amount"):
        compute_support_state_root(
            balances=good_balances,
            pools={},
            lp_balances=lp,
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=((pk, pool_id),)),
        )

    bad_pool = _pool(pool_id, asset0, asset1)
    bad_pool.pool_id = "0x" + "ff" * 32
    with pytest.raises(ValueError, match="pool_id mismatch"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_pool},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=()),
        )

    bad_fee_pool = _pool(pool_id, asset0, asset1)
    bad_fee_pool.fee_bps = 10_001
    with pytest.raises(ValueError, match="invalid pool fee_bps"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_fee_pool},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=()),
        )
