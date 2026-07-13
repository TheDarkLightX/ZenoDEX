# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_root import STATE_ROOT_VERSION, compute_state_root


def test_state_root_version_commits_lp_age_schema() -> None:
    assert STATE_ROOT_VERSION == 5


def test_state_root_binds_fee_accumulator_dust() -> None:
    from src.core.fees import FeeAccumulatorState

    pk = "0x" + "11" * 48
    asset = "0x" + "0a" * 32
    balances = BalanceTable()
    balances.set(pk, asset, 1000)

    def root(fee) -> str:
        return compute_state_root(
            balances=balances,
            pools={},
            lp_balances=LPTable(),
            nonces=NonceTable(),
            fee_accumulator=fee,
        )

    assert root(None) == root(FeeAccumulatorState(dust=0))
    assert root(FeeAccumulatorState(dust=0)) != root(FeeAccumulatorState(dust=7))


def test_state_root_rejects_invalid_fee_accumulator_dust() -> None:
    balances = BalanceTable()
    balances.set("0x" + "11" * 48, "0x" + "0a" * 32, 1)

    class BadFee:
        dust = -1

    with pytest.raises(ValueError):
        compute_state_root(
            balances=balances,
            pools={},
            lp_balances=LPTable(),
            fee_accumulator=BadFee(),
        )


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


def test_state_root_rejects_noncanonical_duplicate_pool_alias() -> None:
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
        pool_id=pool_id_lower,
        asset0=pool_state.asset0,
        asset1=pool_state.asset1,
        reserve0=pool_state.reserve0,
        reserve1=pool_state.reserve1,
        fee_bps=pool_state.fee_bps,
        lp_supply=pool_state.lp_supply,
        status=pool_state.status,
        created_at=pool_state.created_at,
    )
    pool_state_upper.pool_id = pool_id_upper

    pools = {
        pool_id_lower: pool_state,
        pool_id_upper: pool_state_upper,
    }
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
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


def test_pool_assets_canonicalize_hex_case_and_reject_decoded_self_pair() -> None:
    asset0_upper = "0x" + "0A" * 32
    asset1_lower = "0x" + "0b" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0_upper,
        asset1=asset1_lower,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey="0x" + "11" * 48,
        created_at=0,
    )
    assert pool.asset0 == "0x" + "0a" * 32
    assert pool.asset1 == asset1_lower
    assert pool_id == pool.pool_id

    with pytest.raises(ValueError, match="canonical order"):
        PoolState(
            pool_id="0x" + "12" * 32,
            asset0=asset0_upper,
            asset1="0x" + "0a" * 32,
            reserve0=1,
            reserve1=1,
            fee_bps=30,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )


def test_state_root_rejects_mutated_mixed_case_pool_asset_byte_order() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "0a" * 32
    asset1 = "0x" + "0b" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    pool.asset0 = "0x" + "0B" * 32
    pool.asset1 = asset0
    with pytest.raises(ValueError, match="canonical order"):
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
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=pool.reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=pool.status,
        created_at=pool.created_at,
    )
    mismatch.pool_id = "0x" + "ff" * 32
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


def test_pool_state_rejects_canonical_hex_pool_id_parameter_mismatch() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    canonical_pool_id = compute_pool_id(asset0, asset1, 30)
    mismatched_pool_id = "0x" + "ff" * 32
    assert mismatched_pool_id != canonical_pool_id

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        PoolState(
            pool_id=mismatched_pool_id,
            asset0=asset0,
            asset1=asset1,
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=30,
            lp_supply=10,
            status=PoolStatus.ACTIVE,
            created_at=1,
        )


def test_pool_state_preserves_symbolic_id_as_non_authoritative_compatibility() -> None:
    pool = PoolState(
        pool_id="local-pool-a",
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )

    assert pool.pool_id == "local-pool-a"
    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        compute_state_root(
            balances=BalanceTable(),
            pools={pool.pool_id: pool},
            lp_balances=LPTable(),
        )


def test_state_root_rejects_canonical_hex_pool_id_parameter_mismatch() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30)
    pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    pool.pool_id = "0x" + "ff" * 32

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        compute_state_root(
            balances=BalanceTable(),
            pools={pool.pool_id: pool},
            lp_balances=LPTable(),
        )


def test_state_root_rejects_noncanonical_pool_id_case() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    canonical_pool_id = compute_pool_id(asset0, asset1, 30)
    uppercase_pool_id = "0x" + canonical_pool_id[2:].upper()
    pool = PoolState(
        pool_id=canonical_pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    pool.pool_id = uppercase_pool_id

    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        compute_state_root(
            balances=BalanceTable(),
            pools={uppercase_pool_id: pool},
            lp_balances=LPTable(),
        )


def test_state_root_rejects_noncanonical_lp_pool_id_case() -> None:
    canonical_pool_id = "0x" + "ab" * 32
    uppercase_pool_id = "0x" + canonical_pool_id[2:].upper()
    lp_balances = LPTable()
    lp_balances.set("0x" + "11" * 48, uppercase_pool_id, 1)

    with pytest.raises(ValueError, match="canonical lowercase 0x-prefixed 32-byte hex"):
        compute_state_root(
            balances=BalanceTable(),
            pools={},
            lp_balances=lp_balances,
        )


def test_state_root_rejects_pool_identity_before_rust_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.runtime import authority, rust_invoker

    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    mismatched_pool_id = "0x" + "ff" * 32
    canonical_pool_id = compute_pool_id(asset0, asset1, 30)
    pool = PoolState(
        pool_id=canonical_pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=10,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )
    pool.pool_id = mismatched_pool_id
    rust_called = False

    def fake_rust_root(_state: dict[str, object]) -> str:
        nonlocal rust_called
        rust_called = True
        return "0x" + "00" * 32

    monkeypatch.setattr(
        authority,
        "active_mode",
        lambda _surface: authority.AuthorityMode.RUST_AUTHORITY,
    )
    monkeypatch.setattr(rust_invoker, "state_root_hash", fake_rust_root)

    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        compute_state_root(
            balances=BalanceTable(),
            pools={mismatched_pool_id: pool},
            lp_balances=LPTable(),
        )
    assert rust_called is False


def test_state_root_rejects_curve_configuration_change_without_new_pool_id() -> None:
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
        curve_params=pool_a.curve_params,
    )
    pool_b.curve_params = '{"mu_den":3,"mu_num":2}'

    compute_state_root(balances=BalanceTable(), pools={pool_id: pool_a}, lp_balances=LPTable())
    with pytest.raises(ValueError, match="pool_id does not match canonical pool identity"):
        compute_state_root(balances=BalanceTable(), pools={pool_id: pool_b}, lp_balances=LPTable())
