# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.state_root import compute_state_root


def test_state_root_is_insertion_order_independent() -> None:
    pk1 = "0x" + "11" * 48
    pk2 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    asset2 = "0x" + "03" * 32

    pool_id_a, pool_a, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk1,
        created_at=0,
    )
    pool_id_b, pool_b, _ = create_pool(
        asset0=asset0,
        asset1=asset2,
        amount0=1_000_000,
        amount1=3_000_000,
        fee_bps=10,
        creator_pubkey=pk2,
        created_at=1,
    )

    balances_1 = BalanceTable()
    balances_1.set(pk1, asset0, 10)
    balances_1.set(pk2, asset1, 20)

    balances_2 = BalanceTable()
    balances_2.set(pk2, asset1, 20)
    balances_2.set(pk1, asset0, 10)

    pools_1 = {pool_id_a: pool_a, pool_id_b: pool_b}
    pools_2 = {pool_id_b: pool_b, pool_id_a: pool_a}

    lp_1 = LPTable()
    lp_1.set(pk1, pool_id_a, 123)
    lp_1.set(pk2, pool_id_b, 456)

    lp_2 = LPTable()
    lp_2.set(pk2, pool_id_b, 456)
    lp_2.set(pk1, pool_id_a, 123)

    root_1 = compute_state_root(balances=balances_1, pools=pools_1, lp_balances=lp_1)
    root_2 = compute_state_root(balances=balances_2, pools=pools_2, lp_balances=lp_2)
    assert root_1 == root_2


def test_state_root_changes_on_state_change() -> None:
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

    balances = BalanceTable()
    balances.set(pk, asset0, 10)
    pools = {pool_id: pool}
    lp = LPTable()

    root_1 = compute_state_root(balances=balances, pools=pools, lp_balances=lp)
    balances.set(pk, asset0, 11)
    root_2 = compute_state_root(balances=balances, pools=pools, lp_balances=lp)
    assert root_1 != root_2


def test_state_root_rejects_invalid_hex_lengths() -> None:
    pk = "0x" + "11" * 47  # should be 48 bytes
    asset0 = "0x" + "01" * 32
    balances = BalanceTable()
    balances.set(pk, asset0, 10)
    with pytest.raises(ValueError):
        compute_state_root(balances=balances, pools={}, lp_balances=LPTable())


def test_state_root_rejects_duplicate_decoded_balance_keys() -> None:
    pk_lower = "0x" + "aa" * 48
    pk_upper = "0x" + "AA" * 48
    asset = "0x" + "11" * 32

    balances = BalanceTable()
    balances.set(pk_lower, asset, 1)
    balances.set(pk_upper, asset, 2)

    with pytest.raises(ValueError):
        compute_state_root(balances=balances, pools={}, lp_balances=LPTable())


def test_state_root_rejects_duplicate_decoded_pool_ids() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id_lower, pool_state, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    pool_id_upper = "0x" + pool_id_lower[2:].upper()

    pool_state_upper = type(pool_state)(
        pool_id=pool_id_upper,
        asset0=pool_state.asset0,
        asset1=pool_state.asset1,
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        fee_bps=pool_state.fee_bps,
        lp_supply=pool_state.lp_supply,
        status=pool_state.status,
        created_at=pool_state.created_at,
    )

    pools = {
        pool_id_lower: pool_state,
        pool_id_upper: pool_state_upper,
    }
    with pytest.raises(ValueError):
        compute_state_root(balances=BalanceTable(), pools=pools, lp_balances=LPTable())


def test_state_root_rejects_fee_bps_above_10000() -> None:
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

    pool.fee_bps = 10_001
    with pytest.raises(ValueError):
        compute_state_root(balances=BalanceTable(), pools={pool_id: pool}, lp_balances=LPTable())
