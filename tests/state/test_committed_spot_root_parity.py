from __future__ import annotations

from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.domain_limits import DEX_LP_AMOUNT_MAX, DEX_POOL_RESERVE_MAX
from src.core.fees import FeeAccumulatorState
from src.state.balances import BalanceTable
from src.state.canonical import sha256_hex
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.owned_collections import OwnedMapV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_root import (
    state_root_preimage,
    state_root_preimage_with_committed_spot_state_v1,
)
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPoolStateV1,
)
from src.state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_pool_map,
)
from src.state.support_root import (
    BatchStateSupport,
    compute_support_state_root,
    compute_support_state_root_with_committed_spot_state_v1,
)

_PUBKEY_A = "0x" + "11" * 48
_PUBKEY_B = "0x" + "22" * 48
_PUBKEY_C = "0x" + "33" * 48
_ASSET_A = "0x" + "44" * 32
_ASSET_B = "0x" + "55" * 32


def _legacy_state(
    *,
    status: PoolStatus = PoolStatus.ACTIVE,
    reserve0: int = 1_000,
    reserve1: int = 2_000,
    lp_amount: int = 100,
    nonce: int = 9,
    dust: int = 4,
) -> tuple[
    BalanceTable,
    dict[str, PoolState],
    LPTable,
    NonceTable,
    FeeAccumulatorState,
]:
    balances = BalanceTable()
    balances.set(_PUBKEY_B, _ASSET_B, 13)
    balances.set(_PUBKEY_A, _ASSET_A, 7)
    balances.set(_PUBKEY_C, _ASSET_A, 19)

    pool_id = compute_pool_id(_ASSET_A, _ASSET_B, 30)
    pool = PoolState(
        pool_id=pool_id,
        asset0=_ASSET_A,
        asset1=_ASSET_B,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=500,
        status=status,
        created_at=7,
    )
    lp_balances = LPTable()
    lp_balances.set(_PUBKEY_A, pool_id, lp_amount)
    lp_balances.set_last_mint_timestamp(_PUBKEY_A, pool_id, 3)
    lp_balances.set_last_remove_timestamp(_PUBKEY_A, pool_id, 5)
    lp_balances.set_churn_tier(_PUBKEY_A, pool_id, 2)
    lp_balances.set_last_churn_update_timestamp(_PUBKEY_A, pool_id, 6)
    nonces = NonceTable()
    nonces.set_last(_PUBKEY_A, nonce)
    return balances, {pool_id: pool}, lp_balances, nonces, FeeAccumulatorState(dust=dust)


def _committed_state(
    legacy: tuple[
        BalanceTable,
        dict[str, PoolState],
        LPTable,
        NonceTable,
        FeeAccumulatorState,
    ],
) -> tuple[
    CommittedBalanceTableV1,
    OwnedMapV1[str, CommittedPoolStateV1],
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedFeeAccumulatorStateV1,
]:
    balances, pools, lp_balances, nonces, fees = legacy
    return (
        snapshot_balance_table(balances),
        snapshot_pool_map(pools),
        snapshot_lp_table(lp_balances),
        snapshot_nonce_table(nonces),
        snapshot_fee_accumulator(fees),
    )


def _exact_preimage(
    legacy: tuple[
        BalanceTable,
        dict[str, PoolState],
        LPTable,
        NonceTable,
        FeeAccumulatorState,
    ],
) -> bytes:
    balances, pools, lp_balances, nonces, fees = _committed_state(legacy)
    return state_root_preimage_with_committed_spot_state_v1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        fee_accumulator=fees,
    )


def _legacy_preimage(
    legacy: tuple[
        BalanceTable,
        dict[str, PoolState],
        LPTable,
        NonceTable,
        FeeAccumulatorState,
    ],
) -> bytes:
    balances, pools, lp_balances, nonces, fees = legacy
    return state_root_preimage(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        fee_accumulator=fees,
    )


def _support(pool_id: str) -> BatchStateSupport:
    return BatchStateSupport(
        balance_keys=((_PUBKEY_A, _ASSET_A), (_PUBKEY_B, _ASSET_B)),
        pool_ids=(pool_id,),
        lp_keys=((_PUBKEY_A, pool_id),),
        nonce_keys=(_PUBKEY_A,),
    )


def test_exact_committed_spot_state_preserves_pinned_root_v5_bytes() -> None:
    legacy = _legacy_state()

    exact = _exact_preimage(legacy)

    assert exact == _legacy_preimage(legacy)
    assert sha256_hex(exact) == "0xbfac7a34affa3f7729554cd4e35d62f20024ecf978b5e8f08b8c86ac028f6c23"


def test_exact_committed_spot_state_preserves_pinned_support_root_v4() -> None:
    legacy = _legacy_state()
    balances, pools, lp_balances, nonces, _fees = legacy
    committed_balances, committed_pools, committed_lp, committed_nonces, _committed_fees = (
        _committed_state(legacy)
    )
    support = _support(next(iter(pools)))

    legacy_root = compute_support_state_root(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )
    exact_root = compute_support_state_root_with_committed_spot_state_v1(
        balances=committed_balances,
        pools=committed_pools,
        lp_balances=committed_lp,
        support=support,
        nonces=committed_nonces,
    )

    assert exact_root == legacy_root
    assert exact_root == "0x51e0eae22c183effbe62a3708253de808ffe27dac2338d97318ba27833dc4007"


@pytest.mark.parametrize("status", tuple(PoolStatus))
def test_pool_status_ordinal_encoding_matches_legacy(status: PoolStatus) -> None:
    legacy = _legacy_state(status=status)

    assert _exact_preimage(legacy) == _legacy_preimage(legacy)


def test_exact_root_reader_owns_every_legacy_source() -> None:
    legacy = _legacy_state()
    balances, pools, lp_balances, nonces, fees = legacy
    committed = _committed_state(legacy)
    before = state_root_preimage_with_committed_spot_state_v1(
        balances=committed[0],
        pools=committed[1],
        lp_balances=committed[2],
        nonces=committed[3],
        fee_accumulator=committed[4],
    )

    balances.set(_PUBKEY_A, _ASSET_A, 999)
    pool_id = next(iter(pools))
    pools[pool_id].reserve0 = 999
    lp_balances.set(_PUBKEY_A, pool_id, 999)
    nonces.set_last(_PUBKEY_A, 999)
    object.__setattr__(fees, "dust", 999)

    after = state_root_preimage_with_committed_spot_state_v1(
        balances=committed[0],
        pools=committed[1],
        lp_balances=committed[2],
        nonces=committed[3],
        fee_accumulator=committed[4],
    )
    assert after == before


def test_exact_root_reader_revalidates_corrupted_owned_graph() -> None:
    legacy = _legacy_state()
    balances, pools, lp_balances, nonces, fees = _committed_state(legacy)
    owned_nonce_map = object.__getattribute__(nonces, "_last")
    object.__setattr__(owned_nonce_map, "_entries", ((_PUBKEY_A, True),))

    with pytest.raises(StateAdmissionError) as raised:
        state_root_preimage_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fees,
        )
    assert raised.value.code.value == "registry_drift"


def test_exact_root_reader_rejects_legacy_types_at_every_exact_boundary() -> None:
    legacy = _legacy_state()
    legacy_balances, legacy_pools, legacy_lp, legacy_nonces, legacy_fees = legacy
    balances, pools, lp_balances, nonces, fees = _committed_state(legacy)

    with pytest.raises(TypeError, match="exact CommittedBalanceTableV1"):
        state_root_preimage_with_committed_spot_state_v1(
            balances=cast(CommittedBalanceTableV1, legacy_balances),
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fees,
        )
    with pytest.raises(TypeError, match="exact OwnedMapV1"):
        state_root_preimage_with_committed_spot_state_v1(
            balances=balances,
            pools=cast(OwnedMapV1[str, CommittedPoolStateV1], legacy_pools),
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fees,
        )
    with pytest.raises(TypeError, match="exact CommittedLPTableV1"):
        state_root_preimage_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=cast(CommittedLPTableV1, legacy_lp),
            nonces=nonces,
            fee_accumulator=fees,
        )
    with pytest.raises(TypeError, match="exact CommittedNonceTableV1"):
        state_root_preimage_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=cast(CommittedNonceTableV1, legacy_nonces),
            fee_accumulator=fees,
        )
    with pytest.raises(TypeError, match="exact CommittedFeeAccumulatorStateV1"):
        state_root_preimage_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=legacy_fees,
        )


def test_exact_support_reader_rejects_noncanonical_or_mutated_support_values() -> None:
    legacy = _legacy_state()
    balances, pools, lp_balances, nonces, _fees = _committed_state(legacy)
    pool_id = pools.entries[0][0]
    support = _support(pool_id)
    object.__setattr__(support, "nonce_keys", [_PUBKEY_A])

    with pytest.raises(TypeError, match="nonce_keys must be an exact tuple"):
        compute_support_state_root_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            support=support,
            nonces=nonces,
        )

    duplicate_support = BatchStateSupport(
        balance_keys=(),
        pool_ids=(pool_id, pool_id),
        lp_keys=(),
        nonce_keys=(),
    )
    with pytest.raises(ValueError, match="pool_ids must be duplicate-free"):
        compute_support_state_root_with_committed_spot_state_v1(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            support=duplicate_support,
            nonces=nonces,
        )


@settings(max_examples=75, deadline=None)
@given(
    reserve0=st.integers(min_value=0, max_value=DEX_POOL_RESERVE_MAX),
    reserve1=st.integers(min_value=0, max_value=DEX_POOL_RESERVE_MAX),
    lp_amount=st.integers(min_value=1, max_value=DEX_LP_AMOUNT_MAX),
    nonce=st.integers(min_value=0, max_value=2**32 - 1),
    dust=st.integers(min_value=0, max_value=2**64),
)
def test_exact_committed_spot_root_matches_legacy_over_machine_domain(
    reserve0: int,
    reserve1: int,
    lp_amount: int,
    nonce: int,
    dust: int,
) -> None:
    legacy = _legacy_state(
        reserve0=reserve0,
        reserve1=reserve1,
        lp_amount=lp_amount,
        nonce=nonce,
        dust=dust,
    )

    assert _exact_preimage(legacy) == _legacy_preimage(legacy)
