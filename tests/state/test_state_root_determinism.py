# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.lp import LPDurationRiskMetadata
from src.state.nonces import NonceTable
from src.state.state_root import STATE_ROOT_VERSION, compute_state_root


def test_state_root_version_commits_lp_age_schema() -> None:
    assert STATE_ROOT_VERSION == 4


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


def test_state_root_changes_on_nonce_change() -> None:
    pk = "0x" + "11" * 48

    nonces = NonceTable()
    root_1 = compute_state_root(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=nonces,
    )

    nonces.set_last(pk, 1)
    root_2 = compute_state_root(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=nonces,
    )
    assert root_1 != root_2


def test_state_root_rejects_invalid_nonce_table_type() -> None:
    with pytest.raises(TypeError, match="nonces must be a NonceTable"):
        compute_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            nonces={},  # type: ignore[arg-type]
        )


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


def test_state_root_rejects_wrong_input_table_types() -> None:
    with pytest.raises(TypeError, match="balances must be a BalanceTable"):
        compute_state_root(balances={}, pools={}, lp_balances=LPTable())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="lp_balances must be an LPTable"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances={})  # type: ignore[arg-type]


def test_state_root_rejects_invalid_balance_and_lp_amounts() -> None:
    pk = "0x" + "11" * 48
    asset = "0x" + "01" * 32
    pool_id = "0x" + "aa" * 32

    balances = BalanceTable()
    balances._balances[(pk, asset)] = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid balance amount"):
        compute_state_root(balances=balances, pools={}, lp_balances=LPTable())

    lp = LPTable()
    lp._balances[(pk, pool_id)] = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid LP amount"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)


def test_state_root_rejects_duplicate_decoded_lp_keys() -> None:
    pk_lower = "0x" + "aa" * 48
    pk_upper = "0x" + "AA" * 48
    pool_id = "0x" + "11" * 32

    lp = LPTable()
    lp.set(pk_lower, pool_id, 1)
    lp.set(pk_upper, pool_id, 2)

    with pytest.raises(ValueError, match="duplicate decoded \\(pubkey, pool_id\\)"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)


def test_state_root_rejects_pool_id_mismatch_unknown_status_and_invalid_scalars() -> None:
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

    mismatch = type(pool)(
        pool_id="0x" + "ff" * 32,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=pool.reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=pool.status,
        created_at=pool.created_at,
    )
    with pytest.raises(ValueError, match="pool_id mismatch"):
        compute_state_root(balances=BalanceTable(), pools={pool_id: mismatch}, lp_balances=LPTable())

    pool.status = object()  # type: ignore[assignment]
    with pytest.raises(ValueError, match="unknown pool status"):
        compute_state_root(balances=BalanceTable(), pools={pool_id: pool}, lp_balances=LPTable())

    _pool_id2, bad_pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    bad_pool.reserve0 = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid pool reserve0"):
        compute_state_root(balances=BalanceTable(), pools={_pool_id2: bad_pool}, lp_balances=LPTable())


def test_state_root_changes_when_curve_configuration_changes() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool_a, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
        curve_tag="SUM_BOOST_V1",
        curve_params={"mu_num": 1, "mu_den": 2},
    )

    pool_b = type(pool_a)(
        pool_id=pool_a.pool_id,
        asset0=pool_a.asset0,
        asset1=pool_a.asset1,
        reserve0=pool_a.reserve0,
        reserve1=pool_a.reserve1,
        fee_bps=pool_a.fee_bps,
        lp_supply=pool_a.lp_supply,
        status=pool_a.status,
        created_at=pool_a.created_at,
        curve_tag="SUM_BOOST_V1",
        curve_params='{"mu_num":2,"mu_den":3}',
    )

    root_a = compute_state_root(balances=BalanceTable(), pools={pool_id: pool_a}, lp_balances=LPTable())
    root_b = compute_state_root(balances=BalanceTable(), pools={pool_id: pool_b}, lp_balances=LPTable())
    assert root_a != root_b


def test_state_root_commits_lp_duration_risk_metadata() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "22" * 32

    lp = LPTable()
    lp.set(pk, pool_id, 10)
    root_without_metadata = compute_state_root(
        balances=BalanceTable(),
        pools={},
        lp_balances=lp,
    )

    lp.set_last_mint_timestamp(pk, pool_id, 7)
    lp.set_last_remove_timestamp(pk, pool_id, 11)
    lp.set_churn_tier(pk, pool_id, 2)
    lp.set_last_churn_update_timestamp(pk, pool_id, 13)
    root_with_metadata = compute_state_root(
        balances=BalanceTable(),
        pools={},
        lp_balances=lp,
    )

    assert root_without_metadata != root_with_metadata


def test_state_root_rejects_duplicate_decoded_lp_duration_risk_keys() -> None:
    pk_lower = "0x" + "aa" * 48
    pk_upper = "0x" + "AA" * 48
    pool_id = "0x" + "33" * 32

    lp = LPTable()
    lp.set(pk_lower, pool_id, 10)
    lp.set_last_mint_timestamp(pk_lower, pool_id, 1)
    lp.set_last_remove_timestamp(pk_upper, pool_id, 2)

    with pytest.raises(ValueError, match="duplicate decoded \\(pubkey, pool_id\\) in lp_duration_risk"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)


def test_state_root_rejects_corrupt_lp_duration_risk_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "22" * 32

    lp = LPTable()
    lp.set(pk, pool_id, 10)
    lp._last_mint_timestamps[(pk, pool_id)] = -1  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid LP mint timestamp"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)

    lp = LPTable()
    monkeypatch.setattr(
        lp,
        "get_all_duration_risk_metadata",
        lambda: {(pk, pool_id): LPDurationRiskMetadata(churn_tier=True)},  # type: ignore[arg-type]
    )
    with pytest.raises(ValueError, match="invalid LP churn tier"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)


def test_state_root_rejects_duplicate_decoded_nonce_pubkeys() -> None:
    pk_lower = "0x" + "aa" * 48
    pk_upper = "0x" + "AA" * 48

    nonces = NonceTable()
    nonces._last[pk_lower] = 1
    nonces._last[pk_upper] = 2

    with pytest.raises(ValueError, match="duplicate decoded pubkey in nonces"):
        compute_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            nonces=nonces,
        )


def test_state_root_rejects_corrupt_nonce_amount() -> None:
    pk = "0x" + "11" * 48

    nonces = NonceTable()
    nonces._last[pk] = True  # type: ignore[assignment]

    with pytest.raises(ValueError, match="invalid nonce amount"):
        compute_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            nonces=nonces,
        )
