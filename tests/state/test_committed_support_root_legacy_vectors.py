"""Pinned legacy vectors for the exact committed support-root reader.

The expected values in this file were produced by the legacy-only reader at
``fa7ae7f7096bb5f2f58fd253bb1571a243b8b69d``. That commit is the parent of
the exact batch support reader. The constants therefore remain independent of
later refactors that may change both live legacy and exact paths together.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import pytest

from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id, normalize_curve_config
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_pool_map,
)
from src.state.support_root import (
    BatchStateSupport,
    compute_support_state_root_for_batch,
    compute_support_state_root_for_batch_committed_v1,
    derive_batch_state_support,
    derive_batch_state_support_committed_v1,
)

_LEGACY_SOURCE_COMMIT = "fa7ae7f7096bb5f2f58fd253bb1571a243b8b69d"

_PUBKEYS = tuple("0x" + f"{value:02x}" * 48 for value in (0x11, 0x22, 0x33, 0x44))
_ASSETS = tuple("0x" + f"{value:02x}" * 32 for value in (0x51, 0x52, 0x53, 0x54, 0x55, 0x56))

_ALL_KINDS_POOL_ACTIVE = "0x7ea3c83795fc4a865c33a724fca2c8c592de47b4390f25df74fd28e4e61f3bff"
_ALL_KINDS_POOL_FROZEN = "0xd3d5a86c31b29fda2bee6bd00fb4a2c0f91b9edb44dc5cd733d864e21d81fd1a"
_ALL_KINDS_CREATED_POOL = "0x78823cb7362c8e04757741881c510fc8ddefdc6afc16ba6f30c112cff9ac7e84"
_IN_BATCH_CREATED_POOL = "0x7f3d6ccaf535768c1c139eb473c4bfa4b9f5c4b316c5e0e2433c5772b92086c7"
_DISABLED_POOL = "0x2cfa8f65b352ae0447fcaafb3495dffadcefb0ac9532f86b94c99bb896741875"
_PERMUTED_POOL = "0xe502fdccbe1077413feac3a70d1a5389c96aa39cec7b172310082faf9b0e246a"


@dataclass(frozen=True, slots=True)
class _LegacySupportVector:
    name: str
    balances: BalanceTable
    pools: dict[str, PoolState]
    lp_balances: LPTable
    nonces: NonceTable
    intents: tuple[Intent, ...]
    expected_support: BatchStateSupport
    expected_root: str


def _intent_id(value: int) -> str:
    return "0x" + f"{value:064x}"


def _intent(
    value: int,
    kind: IntentKind,
    sender: str,
    fields: dict[str, object],
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_intent_id(value),
        sender_pubkey=sender,
        deadline=999_999,
        fields=fields,
    )


def _pool(
    asset0: str,
    asset1: str,
    fee_bps: int,
    status: PoolStatus,
    *,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    created_at: int,
    curve_tag: str = "CPMM",
    curve_params: str = "",
) -> PoolState:
    normalized_tag, normalized_params = normalize_curve_config(
        curve_tag=curve_tag,
        curve_params=curve_params,
    )
    pool_id = compute_pool_id(
        asset0,
        asset1,
        fee_bps,
        curve_tag=normalized_tag,
        curve_params=normalized_params,
    )
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=lp_supply,
        status=status,
        created_at=created_at,
        curve_tag=normalized_tag,
        curve_params=normalized_params,
    )


def _empty_vector() -> _LegacySupportVector:
    return _LegacySupportVector(
        name="empty",
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=NonceTable(),
        intents=(),
        expected_support=BatchStateSupport(
            balance_keys=(),
            pool_ids=(),
            lp_keys=(),
            nonce_keys=(),
        ),
        expected_root="0x3634653e136b4920230054b965b4cbf330afa164cfefba744840b6a3ed602f71",
    )


def _all_intent_kinds_vector() -> _LegacySupportVector:
    balances = BalanceTable()
    for pubkey, asset, amount in (
        (_PUBKEYS[0], _ASSETS[0], 101),
        (_PUBKEYS[0], _ASSETS[1], 102),
        (_PUBKEYS[0], _ASSETS[2], 103),
        (_PUBKEYS[1], _ASSETS[0], 201),
        (_PUBKEYS[1], _ASSETS[1], 202),
        (_PUBKEYS[2], _ASSETS[4], 303),
    ):
        balances.set(pubkey, asset, amount)

    active = _pool(
        _ASSETS[0],
        _ASSETS[1],
        30,
        PoolStatus.ACTIVE,
        reserve0=1_001,
        reserve1=2_002,
        lp_supply=3_003,
        created_at=7,
    )
    frozen = _pool(
        _ASSETS[2],
        _ASSETS[3],
        45,
        PoolStatus.FROZEN,
        reserve0=4_004,
        reserve1=5_005,
        lp_supply=6_006,
        created_at=8,
        curve_tag="SUM_BOOST_V1",
        curve_params='{"mu_den":10000,"mu_num":250}',
    )
    assert active.pool_id == _ALL_KINDS_POOL_ACTIVE
    assert frozen.pool_id == _ALL_KINDS_POOL_FROZEN

    lp_balances = LPTable()
    lp_balances.set(_PUBKEYS[0], active.pool_id, 77)
    lp_balances.set_last_mint_timestamp(_PUBKEYS[0], active.pool_id, 11)
    lp_balances.set_last_remove_timestamp(_PUBKEYS[0], active.pool_id, 12)
    lp_balances.set_churn_tier(_PUBKEYS[0], active.pool_id, 3)
    lp_balances.set_last_churn_update_timestamp(_PUBKEYS[0], active.pool_id, 13)
    lp_balances.set(_PUBKEYS[1], frozen.pool_id, 88)
    lp_balances.set_last_mint_timestamp(_PUBKEYS[1], frozen.pool_id, 21)

    nonces = NonceTable()
    for pubkey, nonce in zip(_PUBKEYS, (9, 19, 29, 39), strict=True):
        nonces.set_last(pubkey, nonce)

    intents = (
        _intent(
            1,
            IntentKind.SWAP_EXACT_IN,
            _PUBKEYS[0],
            {
                "pool_id": active.pool_id,
                "asset_in": _ASSETS[0],
                "asset_out": _ASSETS[1],
                "amount_in": 5,
                "min_amount_out": 1,
                "nonce": 10,
            },
        ),
        _intent(
            2,
            IntentKind.SWAP_EXACT_OUT,
            _PUBKEYS[1],
            {
                "pool_id": active.pool_id,
                "asset_in": _ASSETS[1],
                "asset_out": _ASSETS[0],
                "amount_out": 4,
                "max_amount_in": 9,
                "nonce": 20,
            },
        ),
        _intent(
            3,
            IntentKind.ADD_LIQUIDITY,
            _PUBKEYS[0],
            {
                "pool_id": frozen.pool_id,
                "recipient": _PUBKEYS[1],
                "amount0_desired": 2,
                "amount1_desired": 3,
                "amount0_min": 1,
                "amount1_min": 1,
                "nonce": 11,
            },
        ),
        _intent(
            4,
            IntentKind.REMOVE_LIQUIDITY,
            _PUBKEYS[0],
            {"pool_id": active.pool_id, "lp_amount": 2, "nonce": 12},
        ),
        _intent(
            5,
            IntentKind.CREATE_POOL,
            _PUBKEYS[2],
            {
                "asset0": _ASSETS[4],
                "asset1": _ASSETS[5],
                "fee_bps": 17,
                "amount0": 8,
                "amount1": 9,
                "created_at": 22,
                "nonce": 30,
            },
        ),
        _intent(
            6,
            IntentKind.ROUTE_EXACT_IN,
            _PUBKEYS[3],
            {
                "quote_receipt_hash": _intent_id(66),
                "asset_in": _ASSETS[0],
                "asset_out": _ASSETS[3],
                "leg_indices": [0, 1],
                "total_amount_in": 7,
                "total_min_amount_out": 1,
                "nonce": 40,
            },
        ),
        _intent(
            7,
            IntentKind.ROUTE_EXACT_OUT,
            _PUBKEYS[3],
            {
                "quote_receipt_hash": _intent_id(67),
                "asset_in": _ASSETS[3],
                "asset_out": _ASSETS[0],
                "leg_indices": [0],
                "total_amount_out": 2,
                "total_max_amount_in": 8,
                "nonce": 41,
            },
        ),
    )
    return _LegacySupportVector(
        name="all_intent_kinds_and_sections",
        balances=balances,
        pools={active.pool_id: active, frozen.pool_id: frozen},
        lp_balances=lp_balances,
        nonces=nonces,
        intents=intents,
        expected_support=BatchStateSupport(
            balance_keys=(
                (_PUBKEYS[0], _ASSETS[0]),
                (_PUBKEYS[0], _ASSETS[2]),
                (_PUBKEYS[0], _ASSETS[3]),
                (_PUBKEYS[1], _ASSETS[1]),
                (_PUBKEYS[2], _ASSETS[4]),
                (_PUBKEYS[2], _ASSETS[5]),
            ),
            pool_ids=(
                _ALL_KINDS_CREATED_POOL,
                _ALL_KINDS_POOL_ACTIVE,
                _ALL_KINDS_POOL_FROZEN,
            ),
            lp_keys=(
                (_PUBKEYS[0], _ALL_KINDS_POOL_ACTIVE),
                (_PUBKEYS[1], _ALL_KINDS_POOL_FROZEN),
            ),
            nonce_keys=_PUBKEYS,
        ),
        expected_root="0xbfeef220e37eb9d0707abe05746f28d783daed998b29b297a5550b526b46ddbe",
    )


def _in_batch_create_then_add_vector() -> _LegacySupportVector:
    balances = BalanceTable()
    for pubkey, asset, amount in (
        (_PUBKEYS[0], _ASSETS[0], 1_000),
        (_PUBKEYS[0], _ASSETS[1], 2_000),
        (_PUBKEYS[1], _ASSETS[0], 3_000),
        (_PUBKEYS[1], _ASSETS[1], 4_000),
    ):
        balances.set(pubkey, asset, amount)
    intents = (
        _intent(
            10,
            IntentKind.CREATE_POOL,
            _PUBKEYS[0],
            {
                "asset0": _ASSETS[0],
                "asset1": _ASSETS[1],
                "fee_bps": 25,
                "amount0": 100,
                "amount1": 200,
                "created_at": 31,
            },
        ),
        _intent(
            11,
            IntentKind.ADD_LIQUIDITY,
            _PUBKEYS[1],
            {
                "pool_id": _IN_BATCH_CREATED_POOL,
                "recipient": _PUBKEYS[2],
                "amount0_desired": 10,
                "amount1_desired": 20,
                "amount0_min": 0,
                "amount1_min": 0,
            },
        ),
    )
    return _LegacySupportVector(
        name="in_batch_create_then_add",
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        nonces=NonceTable(),
        intents=intents,
        expected_support=BatchStateSupport(
            balance_keys=(
                (_PUBKEYS[0], _ASSETS[0]),
                (_PUBKEYS[0], _ASSETS[1]),
                (_PUBKEYS[1], _ASSETS[0]),
                (_PUBKEYS[1], _ASSETS[1]),
            ),
            pool_ids=(_IN_BATCH_CREATED_POOL,),
            lp_keys=((_PUBKEYS[2], _IN_BATCH_CREATED_POOL),),
            nonce_keys=(_PUBKEYS[0], _PUBKEYS[1]),
        ),
        expected_root="0x1f5495411fde99687175e3d4949b402e6c9585436da01009d7ecc552b7240381",
    )


def _disabled_pool_and_omissions_vector() -> _LegacySupportVector:
    balances = BalanceTable()
    balances.set(_PUBKEYS[2], _ASSETS[4], 1)
    disabled = _pool(
        _ASSETS[4],
        _ASSETS[5],
        0,
        PoolStatus.DISABLED,
        reserve0=0,
        reserve1=9,
        lp_supply=0,
        created_at=0,
        curve_tag="CUBIC_SUM_V1",
        curve_params='{"p":2,"q":3}',
    )
    assert disabled.pool_id == _DISABLED_POOL
    lp_balances = LPTable()
    lp_balances.set_last_remove_timestamp(_PUBKEYS[2], disabled.pool_id, 0)
    lp_balances.set_churn_tier(_PUBKEYS[2], disabled.pool_id, 1)
    lp_balances.set_last_churn_update_timestamp(_PUBKEYS[2], disabled.pool_id, 2)
    missing_pool_id = _intent_id(99)
    intents = (
        _intent(
            20,
            IntentKind.REMOVE_LIQUIDITY,
            _PUBKEYS[2],
            {"pool_id": disabled.pool_id, "lp_amount": 1},
        ),
        _intent(
            21,
            IntentKind.SWAP_EXACT_IN,
            _PUBKEYS[2],
            {
                "pool_id": missing_pool_id,
                "asset_in": _ASSETS[5],
                "asset_out": _ASSETS[4],
                "amount_in": 1,
                "min_amount_out": 0,
            },
        ),
    )
    return _LegacySupportVector(
        name="disabled_pool_metadata_only_and_missing_omissions",
        balances=balances,
        pools={disabled.pool_id: disabled},
        lp_balances=lp_balances,
        nonces=NonceTable(),
        intents=intents,
        expected_support=BatchStateSupport(
            balance_keys=((_PUBKEYS[2], _ASSETS[5]),),
            pool_ids=(missing_pool_id, _DISABLED_POOL),
            lp_keys=((_PUBKEYS[2], _DISABLED_POOL),),
            nonce_keys=(_PUBKEYS[2],),
        ),
        expected_root="0xc8173080147b979c7c2219c6ff12477678c312d391d343133c4cc9f6eda26cdc",
    )


def _invalid_create_fields_vector() -> _LegacySupportVector:
    intents = (
        _intent(
            30,
            IntentKind.CREATE_POOL,
            _PUBKEYS[0],
            {"asset0": 7, "asset1": _ASSETS[1], "fee_bps": True},
        ),
        _intent(
            31,
            IntentKind.CREATE_POOL,
            _PUBKEYS[1],
            {"asset0": _ASSETS[0], "asset1": _ASSETS[1], "fee_bps": 10_001},
        ),
        _intent(
            32,
            IntentKind.ADD_LIQUIDITY,
            _PUBKEYS[2],
            {"pool_id": "", "recipient": ""},
        ),
    )
    return _LegacySupportVector(
        name="invalid_create_fields_minimal_support",
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        nonces=NonceTable(),
        intents=intents,
        expected_support=BatchStateSupport(
            balance_keys=(
                (_PUBKEYS[1], _ASSETS[0]),
                (_PUBKEYS[1], _ASSETS[1]),
            ),
            pool_ids=(),
            lp_keys=(),
            nonce_keys=(_PUBKEYS[0], _PUBKEYS[1], _PUBKEYS[2]),
        ),
        expected_root="0x3634653e136b4920230054b965b4cbf330afa164cfefba744840b6a3ed602f71",
    )


def _permuted_batch_vector(*, reversed_order: bool) -> _LegacySupportVector:
    balances = BalanceTable()
    balances.set(_PUBKEYS[0], _ASSETS[0], 31)
    balances.set(_PUBKEYS[1], _ASSETS[1], 37)
    pool = _pool(
        _ASSETS[0],
        _ASSETS[1],
        99,
        PoolStatus.ACTIVE,
        reserve0=17,
        reserve1=19,
        lp_supply=23,
        created_at=29,
    )
    assert pool.pool_id == _PERMUTED_POOL
    lp_balances = LPTable()
    lp_balances.set(_PUBKEYS[0], pool.pool_id, 41)
    nonces = NonceTable()
    nonces.set_last(_PUBKEYS[0], 43)
    nonces.set_last(_PUBKEYS[1], 47)
    add = _intent(
        40,
        IntentKind.ADD_LIQUIDITY,
        _PUBKEYS[0],
        {
            "pool_id": pool.pool_id,
            "amount0_desired": 1,
            "amount1_desired": 1,
        },
    )
    swap = _intent(
        41,
        IntentKind.SWAP_EXACT_IN,
        _PUBKEYS[1],
        {
            "pool_id": pool.pool_id,
            "asset_in": _ASSETS[1],
            "asset_out": _ASSETS[0],
            "amount_in": 1,
            "min_amount_out": 0,
        },
    )
    intents = (swap, add) if reversed_order else (add, swap)
    return _LegacySupportVector(
        name=f"permuted_batch_{'b' if reversed_order else 'a'}",
        balances=balances,
        pools={pool.pool_id: pool},
        lp_balances=lp_balances,
        nonces=nonces,
        intents=intents,
        expected_support=BatchStateSupport(
            balance_keys=(
                (_PUBKEYS[0], _ASSETS[0]),
                (_PUBKEYS[0], _ASSETS[1]),
                (_PUBKEYS[1], _ASSETS[1]),
            ),
            pool_ids=(_PERMUTED_POOL,),
            lp_keys=((_PUBKEYS[0], _PERMUTED_POOL),),
            nonce_keys=(_PUBKEYS[0], _PUBKEYS[1]),
        ),
        expected_root="0x6d96406408e53803a06fbafbde18d17f350b35c2d2488e4731972a62d3ee40fe",
    )


_VECTOR_FACTORIES: tuple[Callable[[], _LegacySupportVector], ...] = (
    _empty_vector,
    _all_intent_kinds_vector,
    _in_batch_create_then_add_vector,
    _disabled_pool_and_omissions_vector,
    _invalid_create_fields_vector,
    lambda: _permuted_batch_vector(reversed_order=False),
    lambda: _permuted_batch_vector(reversed_order=True),
)


@pytest.mark.parametrize(
    "vector_factory",
    _VECTOR_FACTORIES,
    ids=(
        "empty",
        "all-intent-kinds",
        "create-then-add",
        "disabled-and-omissions",
        "invalid-create",
        "permutation-a",
        "permutation-b",
    ),
)
def test_exact_support_reader_matches_source_pinned_legacy_vector(
    vector_factory: Callable[[], _LegacySupportVector],
) -> None:
    vector = vector_factory()
    committed_balances = snapshot_balance_table(vector.balances)
    committed_pools = snapshot_pool_map(vector.pools)
    committed_lp = snapshot_lp_table(vector.lp_balances)
    committed_nonces = snapshot_nonce_table(vector.nonces)

    exact_support = derive_batch_state_support_committed_v1(
        vector.intents,
        pools=committed_pools,
    )
    exact_root = compute_support_state_root_for_batch_committed_v1(
        intents=vector.intents,
        balances=committed_balances,
        pools=committed_pools,
        lp_balances=committed_lp,
        nonces=committed_nonces,
    )

    assert exact_support == vector.expected_support
    assert exact_root == vector.expected_root


@pytest.mark.parametrize(
    "vector_factory",
    _VECTOR_FACTORIES,
    ids=(
        "empty",
        "all-intent-kinds",
        "create-then-add",
        "disabled-and-omissions",
        "invalid-create",
        "permutation-a",
        "permutation-b",
    ),
)
def test_live_legacy_reader_still_matches_its_source_pinned_vector(
    vector_factory: Callable[[], _LegacySupportVector],
) -> None:
    vector = vector_factory()

    support = derive_batch_state_support(vector.intents, pools=vector.pools)
    root = compute_support_state_root_for_batch(
        intents=vector.intents,
        balances=vector.balances,
        pools=vector.pools,
        lp_balances=vector.lp_balances,
        nonces=vector.nonces,
    )

    assert support == vector.expected_support
    assert root == vector.expected_root


def test_source_pinned_corpus_covers_every_intent_kind_and_support_section() -> None:
    vector = _all_intent_kinds_vector()

    assert {intent.kind for intent in vector.intents} == set(IntentKind)
    assert vector.expected_support.balance_keys
    assert vector.expected_support.pool_ids
    assert vector.expected_support.lp_keys
    assert vector.expected_support.nonce_keys
    assert _LEGACY_SOURCE_COMMIT == "fa7ae7f7096bb5f2f58fd253bb1571a243b8b69d"


def test_source_pinned_permutation_pair_has_identical_support_and_root() -> None:
    first = _permuted_batch_vector(reversed_order=False)
    second = _permuted_batch_vector(reversed_order=True)

    assert first.expected_support == second.expected_support
    assert first.expected_root == second.expected_root
