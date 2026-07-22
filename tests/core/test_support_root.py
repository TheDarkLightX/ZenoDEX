# [TESTER] v1

from __future__ import annotations

from typing import Any, cast

import pytest

import src.state.support_root as support_root_module
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id, normalize_curve_config
from src.state.support_root import (
    SUPPORT_ROOT_VERSION,
    BatchStateSupport,
    compute_support_state_root,
    compute_support_state_root_for_batch,
    derive_batch_state_support,
)


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sum_boost_create_and_add_liq() -> tuple[str, str, str, str, str, Intent, Intent]:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "03" * 32
    asset1 = "0x" + "04" * 32
    fee_bps = 20
    curve_tag, curve_params = normalize_curve_config(
        curve_tag="SUM_BOOST_V1",
        curve_params={"mu_num": 1, "mu_den": 2},
    )
    pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag=curve_tag, curve_params=curve_params)
    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(201),
        sender_pubkey=pk_a,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": fee_bps,
            "amount0": 1000,
            "amount1": 2000,
            "curve_tag": " sum_boost_v1 ",
            "curve_params": {"mu_num": 1, "mu_den": 2},
        },
    )
    add_liq = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(202),
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
    return pk_a, pk_b, asset0, asset1, pool_id, create_pool, add_liq


def test_support_root_version_commits_lp_age_schema() -> None:
    assert SUPPORT_ROOT_VERSION == 4


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

    pools: dict[str, PoolState] = {}
    lp = LPTable()

    r1 = compute_support_state_root_for_batch(intents=intents, balances=balances1, pools=pools, lp_balances=lp)
    r2 = compute_support_state_root_for_batch(intents=intents, balances=balances2, pools=pools, lp_balances=lp)
    assert r1 != r2


def test_support_root_uses_live_curve_config_for_add_liquidity_into_new_pool() -> None:
    _, pk_b, asset0, asset1, pool_id, create_pool, add_liq = _sum_boost_create_and_add_liq()

    support = derive_batch_state_support([create_pool, add_liq], pools={})
    assert (pk_b, asset0) in support.balance_keys
    assert (pk_b, asset1) in support.balance_keys
    assert pool_id in support.pool_ids

    balances1 = BalanceTable()
    balances1.set(pk_b, asset0, 100)
    balances1.set(pk_b, asset1, 200)
    balances2 = BalanceTable()
    balances2.set(pk_b, asset0, 99)
    balances2.set(pk_b, asset1, 200)

    root1 = compute_support_state_root_for_batch(
        intents=[create_pool, add_liq],
        balances=balances1,
        pools={},
        lp_balances=LPTable(),
    )
    root2 = compute_support_state_root_for_batch(
        intents=[create_pool, add_liq],
        balances=balances2,
        pools={},
        lp_balances=LPTable(),
    )
    assert root1 != root2


def test_support_root_changes_on_tracked_nonce_change() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")

    swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(99),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": asset0, "asset_out": asset1, "amount_in": 5, "min_amount_out": 1},
    )

    nonces_1 = NonceTable()
    nonces_2 = NonceTable()
    nonces_2.set_last(pk, 1)

    root_1 = compute_support_state_root_for_batch(
        intents=[swap],
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=nonces_1,
    )
    root_2 = compute_support_state_root_for_batch(
        intents=[swap],
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=nonces_2,
    )
    assert root_1 != root_2


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
    assert support.nonce_keys == (pk,)


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
    assert support == BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=(pk,))


def test_derive_batch_state_support_propagates_create_pool_helper_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(101),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30},
    )

    def broken_compute_pool_id(*args: object, **kwargs: object) -> str:
        raise RuntimeError("pool-id helper bug")

    monkeypatch.setattr(support_root_module, "compute_pool_id", broken_compute_pool_id)
    with pytest.raises(RuntimeError, match="pool-id helper bug"):
        derive_batch_state_support([create_pool], pools={})


def test_compute_support_state_root_rejects_wrong_table_types() -> None:
    bad_mapping = cast(Any, {})
    with pytest.raises(TypeError, match="balances must be a BalanceTable"):
        compute_support_state_root(
            balances=bad_mapping,
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=()),
        )
    with pytest.raises(TypeError, match="lp_balances must be an LPTable"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=bad_mapping,
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=()),
        )
    with pytest.raises(TypeError, match="support must be a BatchStateSupport"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            support=bad_mapping,
        )
    with pytest.raises(TypeError, match="nonces must be a NonceTable"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=()),
            nonces=bad_mapping,
        )


def test_compute_support_state_root_omits_missing_pools_and_zero_entries() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    pool_id = "0x" + "aa" * 32
    support = BatchStateSupport(balance_keys=((pk, asset0),), pool_ids=(pool_id,), lp_keys=((pk, pool_id),), nonce_keys=(pk,))

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
        support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=()),
    )
    assert isinstance(root_empty, str) and root_empty.startswith("0x")
    assert root_empty == root_zero


def test_derive_batch_state_support_covers_invalid_create_pool_and_missing_pool_variants() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "02" * 32
    asset1 = "0x" + "01" * 32
    valid_asset0 = "0x" + "03" * 32
    valid_asset1 = "0x" + "04" * 32
    pool_id = compute_pool_id(valid_asset0, valid_asset1, 30, curve_tag="CPMM", curve_params="")

    missing_asset1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(10),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": valid_asset0, "asset1": None, "fee_bps": 30},
    )
    bool_fee = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(11),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": valid_asset0, "asset1": valid_asset1, "fee_bps": True},
    )
    noncanonical_assets = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(12),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30},
    )
    invalid_swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(13),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": "", "asset_in": "", "asset_out": valid_asset1, "amount_in": 1, "min_amount_out": 0},
    )
    remove_missing_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(14),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={},
    )
    add_unknown_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(15),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "amount0_desired": 1, "amount1_desired": 1},
    )

    support = derive_batch_state_support(
        [missing_asset1, bool_fee, noncanonical_assets, invalid_swap, remove_missing_pool, add_unknown_pool],
        pools={},
    )
    assert set(support.balance_keys) == {
        (pk, valid_asset0),
        (pk, valid_asset1),
        (pk, asset0),
        (pk, asset1),
    }
    assert support.pool_ids == (pool_id,)
    assert support.lp_keys == ((pk, pool_id),)
    assert support.nonce_keys == (pk,)


def test_derive_batch_state_support_reads_add_liquidity_from_existing_pool_and_created_pool() -> None:
    pk = "0x" + "11" * 48
    recipient = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    asset2 = "0x" + "03" * 32
    asset3 = "0x" + "04" * 32
    existing_pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    created_pool_id = compute_pool_id(asset2, asset3, 20, curve_tag="CPMM", curve_params="")

    existing_add = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(16),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": existing_pool_id, "recipient": recipient},
    )
    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(17),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset2, "asset1": asset3, "fee_bps": 20},
    )
    created_add = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(18),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": created_pool_id},
    )

    support = derive_batch_state_support(
        [existing_add, create_pool, created_add],
        pools={existing_pool_id: _pool(existing_pool_id, asset0, asset1)},
    )
    assert set(support.balance_keys) == {(pk, asset0), (pk, asset1), (pk, asset2), (pk, asset3)}
    assert set(support.pool_ids) == {existing_pool_id, created_pool_id}
    assert set(support.lp_keys) == {(recipient, existing_pool_id), (pk, created_pool_id)}
    assert support.nonce_keys == (pk,)


def test_support_root_commits_add_liquidity_recipient_duration_metadata() -> None:
    sender = "0x" + "11" * 48
    recipient = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(21),
        sender_pubkey=sender,
        deadline=9999999999,
        fields={"pool_id": pool_id, "recipient": recipient},
    )
    support = derive_batch_state_support(
        [intent],
        pools={pool_id: _pool(pool_id, asset0, asset1)},
    )
    lp = LPTable()
    before = compute_support_state_root(
        balances=BalanceTable(),
        pools={pool_id: _pool(pool_id, asset0, asset1)},
        lp_balances=lp,
        support=support,
    )
    lp.set_last_remove_timestamp(recipient, pool_id, 500)
    lp.set_churn_tier(recipient, pool_id, 2)
    lp.set_last_churn_update_timestamp(recipient, pool_id, 500)
    after = compute_support_state_root(
        balances=BalanceTable(),
        pools={pool_id: _pool(pool_id, asset0, asset1)},
        lp_balances=lp,
        support=support,
    )

    assert support.lp_keys == ((recipient, pool_id),)
    assert after != before


def test_derive_batch_state_support_covers_missing_add_liquidity_pool_and_unknown_kind() -> None:
    pk = "0x" + "11" * 48

    missing_pool_add = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(19),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={},
    )
    unknown = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(20),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={},
    )
    unknown.kind = "UNKNOWN_KIND"

    support = derive_batch_state_support([missing_pool_add, unknown], pools={})
    assert support == BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=(), nonce_keys=(pk,))


def test_compute_support_state_root_covers_positive_lp_section_unknown_status_and_invalid_pool_scalars() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")

    balances = BalanceTable()
    balances.set(pk, asset0, 7)
    lp = LPTable()
    lp.set(pk, pool_id, 9)
    support = BatchStateSupport(balance_keys=((pk, asset0),), pool_ids=(pool_id,), lp_keys=((pk, pool_id),), nonce_keys=(pk,))
    root = compute_support_state_root(
        balances=balances,
        pools={pool_id: _pool(pool_id, asset0, asset1)},
        lp_balances=lp,
        support=support,
    )
    assert root.startswith("0x")

    bad_status = _pool(pool_id, asset0, asset1)
    bad_status.status = object()
    with pytest.raises(ValueError, match="unknown pool status"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_status},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=(), nonce_keys=()),
        )

    bad_reserve = _pool(pool_id, asset0, asset1)
    bad_reserve.reserve0 = True
    with pytest.raises(ValueError, match="invalid pool reserve0"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_reserve},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=(), nonce_keys=()),
        )


def test_compute_support_state_root_rejects_duplicate_and_noncanonical_support_keys() -> None:
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
            support=BatchStateSupport(balance_keys=((pk, asset), (pk, asset)), pool_ids=(), lp_keys=(), nonce_keys=()),
        )

    with pytest.raises(ValueError, match="pool_id must be valid hex"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: _pool(pool_id, asset, "0x" + "02" * 32), pool_id.upper().replace("0X", "0x"): _pool(pool_id.upper().replace("0X", "0x"), asset, "0x" + "02" * 32)},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id, pool_id.upper().replace("0X", "0x")), lp_keys=(), nonce_keys=()),
        )

    with pytest.raises(ValueError, match="duplicate decoded \\(pubkey, pool_id\\)"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=lp,
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=((pk, pool_id), (pk, pool_id)), nonce_keys=()),
        )


def test_compute_support_state_root_rejects_invalid_pool_and_amount_scalars() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")

    balances = BalanceTable()
    balances._balances[(pk, asset0)] = True
    with pytest.raises(ValueError, match="invalid balance amount"):
        compute_support_state_root(
            balances=balances,
            pools={},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=((pk, asset0),), pool_ids=(), lp_keys=(), nonce_keys=()),
        )

    good_balances = BalanceTable()
    good_balances.set(pk, asset0, 10)
    lp = LPTable()
    lp._balances[(pk, pool_id)] = True
    with pytest.raises(ValueError, match="invalid LP amount"):
        compute_support_state_root(
            balances=good_balances,
            pools={},
            lp_balances=lp,
            support=BatchStateSupport(balance_keys=(), pool_ids=(), lp_keys=((pk, pool_id),), nonce_keys=()),
        )

    bad_pool = _pool(pool_id, asset0, asset1)
    bad_pool.pool_id = "0x" + "ff" * 32
    with pytest.raises(ValueError, match="pool_id mismatch"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_pool},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=(), nonce_keys=()),
        )

    bad_fee_pool = _pool(pool_id, asset0, asset1)
    bad_fee_pool.fee_bps = 10_001
    with pytest.raises(ValueError, match="invalid pool fee_bps"):
        compute_support_state_root(
            balances=BalanceTable(),
            pools={pool_id: bad_fee_pool},
            lp_balances=LPTable(),
            support=BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=(), nonce_keys=()),
        )


def test_support_root_changes_when_curve_configuration_changes() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="SUM_BOOST_V1", curve_params='{"mu_num":1,"mu_den":2}')

    pool_a = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=3_000,
        status=PoolStatus.ACTIVE,
        created_at=1,
        curve_tag="SUM_BOOST_V1",
        curve_params='{"mu_num":1,"mu_den":2}',
    )
    pool_b = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=3_000,
        status=PoolStatus.ACTIVE,
        created_at=1,
        curve_tag="SUM_BOOST_V1",
        curve_params='{"mu_num":2,"mu_den":3}',
    )

    support = BatchStateSupport(balance_keys=(), pool_ids=(pool_id,), lp_keys=(), nonce_keys=())
    root_a = compute_support_state_root(
        balances=BalanceTable(),
        pools={pool_id: pool_a},
        lp_balances=LPTable(),
        support=support,
    )
    root_b = compute_support_state_root(
        balances=BalanceTable(),
        pools={pool_id: pool_b},
        lp_balances=LPTable(),
        support=support,
    )
    assert root_a != root_b
