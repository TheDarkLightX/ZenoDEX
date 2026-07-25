from __future__ import annotations

from itertools import permutations
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.fees import FeeAccumulatorState
from src.state.balances import BalanceTable
from src.state.canonical import sha256_hex
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_root import (
    state_root_preimage,
    state_root_preimage_with_committed_balances_v1,
)
from src.state.state_snapshot_values import CommittedBalanceTableV1
from src.state.state_snapshots import StateAdmissionError, snapshot_balance_table
from src.state.support_root import (
    BatchStateSupport,
    compute_support_state_root,
    compute_support_state_root_with_committed_balances_v1,
)

_PUBKEY_A = "0x" + "11" * 48
_PUBKEY_B = "0x" + "22" * 48
_PUBKEY_C = "0x" + "33" * 48
_ASSET_A = "0x" + "44" * 32
_ASSET_B = "0x" + "55" * 32


def _legacy_balances(
    entries: tuple[tuple[tuple[str, str], int], ...],
) -> BalanceTable:
    balances = BalanceTable()
    for (pubkey, asset), amount in entries:
        balances.set(pubkey, asset, amount)
    return balances


def _other_state() -> tuple[dict[str, PoolState], LPTable, NonceTable, FeeAccumulatorState]:
    pool_id = compute_pool_id(_ASSET_A, _ASSET_B, 30)
    pool = PoolState(
        pool_id=pool_id,
        asset0=_ASSET_A,
        asset1=_ASSET_B,
        reserve0=1_000,
        reserve1=2_000,
        fee_bps=30,
        lp_supply=500,
        status=PoolStatus.ACTIVE,
        created_at=7,
    )
    lp_balances = LPTable()
    lp_balances.set(_PUBKEY_A, pool_id, 100)
    lp_balances.set_last_mint_timestamp(_PUBKEY_A, pool_id, 3)
    lp_balances.set_last_remove_timestamp(_PUBKEY_A, pool_id, 5)
    lp_balances.set_churn_tier(_PUBKEY_A, pool_id, 2)
    lp_balances.set_last_churn_update_timestamp(_PUBKEY_A, pool_id, 6)
    nonces = NonceTable()
    nonces.set_last(_PUBKEY_A, 9)
    return {pool_id: pool}, lp_balances, nonces, FeeAccumulatorState(dust=4)


def _full_preimages(
    balances: BalanceTable,
) -> tuple[bytes, bytes]:
    pools, lp_balances, nonces, fee_accumulator = _other_state()
    committed = snapshot_balance_table(balances)
    return (
        state_root_preimage(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fee_accumulator,
        ),
        state_root_preimage_with_committed_balances_v1(
            balances=committed,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fee_accumulator,
        ),
    )


def _support() -> BatchStateSupport:
    pools, _lp_balances, _nonces, _fee_accumulator = _other_state()
    pool_id = next(iter(pools))
    return BatchStateSupport(
        balance_keys=((_PUBKEY_A, _ASSET_A), (_PUBKEY_B, _ASSET_B)),
        pool_ids=(pool_id,),
        lp_keys=((_PUBKEY_A, pool_id),),
        nonce_keys=(_PUBKEY_A,),
    )


def test_full_state_root_bytes_match_pinned_legacy_fixture() -> None:
    balances = _legacy_balances(
        (
            ((_PUBKEY_B, _ASSET_B), 13),
            ((_PUBKEY_A, _ASSET_A), 7),
            ((_PUBKEY_C, _ASSET_A), 19),
        )
    )

    legacy_preimage, committed_preimage = _full_preimages(balances)

    assert committed_preimage == legacy_preimage
    assert sha256_hex(committed_preimage) == (
        "0xbfac7a34affa3f7729554cd4e35d62f20024ecf978b5e8f08b8c86ac028f6c23"
    )


def test_support_root_matches_pinned_legacy_fixture() -> None:
    balances = _legacy_balances(
        (
            ((_PUBKEY_B, _ASSET_B), 13),
            ((_PUBKEY_A, _ASSET_A), 7),
            ((_PUBKEY_C, _ASSET_A), 19),
        )
    )
    pools, lp_balances, nonces, _fee_accumulator = _other_state()
    support = _support()

    legacy_root = compute_support_state_root(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )
    committed_root = compute_support_state_root_with_committed_balances_v1(
        balances=snapshot_balance_table(balances),
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )

    assert committed_root == legacy_root
    assert committed_root == "0x51e0eae22c183effbe62a3708253de808ffe27dac2338d97318ba27833dc4007"


def test_balance_insertion_order_cannot_change_full_or_support_roots() -> None:
    entries = (
        ((_PUBKEY_A, _ASSET_A), 7),
        ((_PUBKEY_B, _ASSET_B), 13),
        ((_PUBKEY_C, _ASSET_A), 19),
    )
    pools, lp_balances, nonces, _fee_accumulator = _other_state()
    support = _support()
    observed: set[tuple[str, str]] = set()

    for ordering in permutations(entries):
        balances = _legacy_balances(ordering)
        legacy_preimage, committed_preimage = _full_preimages(balances)
        committed_support_root = compute_support_state_root_with_committed_balances_v1(
            balances=snapshot_balance_table(balances),
            pools=pools,
            lp_balances=lp_balances,
            support=support,
            nonces=nonces,
        )
        observed.add((sha256_hex(legacy_preimage), committed_support_root))
        assert committed_preimage == legacy_preimage

    assert len(observed) == 1


def test_committed_root_readers_own_source_and_revalidate_corruption() -> None:
    source = _legacy_balances((((_PUBKEY_A, _ASSET_A), 7),))
    committed = snapshot_balance_table(source)
    before = _full_preimages(source)[1]

    source.set(_PUBKEY_A, _ASSET_A, 999)
    pools, lp_balances, nonces, fee_accumulator = _other_state()
    after = state_root_preimage_with_committed_balances_v1(
        balances=committed,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )

    assert after == before

    owned_map = object.__getattribute__(committed, "_balances")
    object.__setattr__(owned_map, "_entries", (((_PUBKEY_A, _ASSET_A), True),))
    with pytest.raises(StateAdmissionError):
        state_root_preimage_with_committed_balances_v1(
            balances=committed,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fee_accumulator,
        )


def test_committed_root_readers_reject_legacy_and_subclass_inputs() -> None:
    pools, lp_balances, nonces, fee_accumulator = _other_state()
    legacy = _legacy_balances((((_PUBKEY_A, _ASSET_A), 7),))
    with pytest.raises(TypeError, match="exact CommittedBalanceTableV1"):
        state_root_preimage_with_committed_balances_v1(
            balances=cast(CommittedBalanceTableV1, legacy),
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonces,
            fee_accumulator=fee_accumulator,
        )

    exact = snapshot_balance_table(legacy)
    committed_subclass = type("_CommittedBalanceSubclass", (CommittedBalanceTableV1,), {})
    subclass = committed_subclass(object.__getattribute__(exact, "_balances"))
    with pytest.raises(TypeError, match="exact CommittedBalanceTableV1"):
        compute_support_state_root_with_committed_balances_v1(
            balances=cast(CommittedBalanceTableV1, subclass),
            pools=pools,
            lp_balances=lp_balances,
            support=_support(),
            nonces=nonces,
        )


@settings(max_examples=50, deadline=None)
@given(
    amounts=st.dictionaries(
        keys=st.integers(min_value=0, max_value=5),
        values=st.integers(min_value=1, max_value=2**64),
        max_size=6,
    )
)
def test_committed_full_root_matches_legacy_for_canonical_balance_maps(
    amounts: dict[int, int],
) -> None:
    pubkeys = (_PUBKEY_A, _PUBKEY_B, _PUBKEY_C)
    assets = (_ASSET_A, _ASSET_B)
    entries = tuple(
        ((pubkeys[cell // 2], assets[cell % 2]), amount) for cell, amount in amounts.items()
    )
    legacy_preimage, committed_preimage = _full_preimages(_legacy_balances(entries))

    assert committed_preimage == legacy_preimage
