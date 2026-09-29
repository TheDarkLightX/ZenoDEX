"""Committed state snapshots own their entries and cannot be mutated.

Obligations (current-source repair of STATE-ALIAS-001..004 at the table level):

- a committed snapshot admits builder content by copy, never by alias;
- every committed table rejects in-place mutation;
- builders and snapshots with equal logical content produce byte-identical
  state roots (differential oracle against the unchanged encoder);
- builder -> snapshot -> builder round trips preserve every rail.
"""

from __future__ import annotations

import copy
import random
from dataclasses import FrozenInstanceError

import pytest

from src.state.balances import BalanceSnapshot, BalanceTable, snapshot_balances
from src.state.lp import (
    LPDurationRiskMetadata,
    LPPositionRow,
    LPSnapshot,
    LPTable,
    snapshot_lp_table,
)
from src.state.nonces import NonceSnapshot, NonceTable, snapshot_nonces
from src.state.pools import (
    PoolSnapshot,
    PoolState,
    PoolStatus,
    PoolTableSnapshot,
    copy_pool_state,
    snapshot_pool,
    snapshot_pool_table,
)
from src.state.state_root import compute_state_root

ALICE = "0x" + "aa" * 48
BOB = "0x" + "bb" * 48
ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
POOL_ID = "0x" + "cc" * 32
U32_MAX = 0xFFFFFFFF


def _pool(**overrides: object) -> PoolState:
    fields: dict[str, object] = {
        "pool_id": POOL_ID,
        "asset0": ASSET_A,
        "asset1": ASSET_B,
        "reserve0": 1_000,
        "reserve1": 2_000,
        "fee_bps": 30,
        "lp_supply": 1_414,
        "status": PoolStatus.ACTIVE,
        "created_at": 7,
    }
    fields.update(overrides)
    return PoolState(**fields)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# STATE-ALIAS-001: balances
# ---------------------------------------------------------------------------


def test_balance_snapshot_copies_builder_and_rejects_every_mutation_path() -> None:
    builder = BalanceTable()
    builder.set(ALICE, ASSET_A, 5)
    builder.set(BOB, ASSET_B, 2**63)

    snapshot = snapshot_balances(builder)
    assert type(snapshot) is BalanceSnapshot
    assert snapshot.get(ALICE, ASSET_A) == 5
    assert snapshot.get(BOB, ASSET_B) == 2**63
    assert snapshot.get(BOB, ASSET_A) == 0
    assert snapshot.get(123, ASSET_A) == 0  # type: ignore[arg-type]

    # Later builder mutation does not reach the committed value.
    builder.set(ALICE, ASSET_A, 999)
    builder.set("mallory", ASSET_A, 1)
    assert snapshot.get(ALICE, ASSET_A) == 5
    assert snapshot.get("mallory", ASSET_A) == 0

    # No setter exists and attribute rebinding is refused.
    assert not hasattr(snapshot, "set")
    assert not hasattr(snapshot, "add")
    with pytest.raises(TypeError):
        snapshot._keys = ()  # type: ignore[misc]
    with pytest.raises(TypeError):
        del snapshot._keys  # type: ignore[attr-defined]

    # Read views are fresh copies.
    view = snapshot.get_all_balances()
    view[(ALICE, ASSET_A)] = 0
    assert snapshot.get(ALICE, ASSET_A) == 5
    assert snapshot.get_balances_for_asset(ASSET_A) == {ALICE: 5}
    assert snapshot.verify_non_negative() is True
    assert copy.copy(snapshot) is snapshot
    assert copy.deepcopy(snapshot) is snapshot


def test_balance_snapshot_equal_logical_state_regardless_of_insertion_order() -> None:
    first = BalanceTable()
    first.set(ALICE, ASSET_A, 1)
    first.set(BOB, ASSET_B, 2)
    second = BalanceTable()
    second.set(BOB, ASSET_B, 2)
    second.set(ALICE, ASSET_A, 1)
    second.set(ALICE, ASSET_B, 0)  # zero entries stay unrepresented

    left = snapshot_balances(first)
    right = snapshot_balances(second)
    assert left == right
    assert compute_state_root(balances=left, pools={}, lp_balances=LPTable()) == compute_state_root(
        balances=right, pools={}, lp_balances=LPTable(),
    )
    assert len(left) == 2
    assert snapshot_balances(left) is left
    assert left.to_table().get_all_balances() == first.get_all_balances()


def test_balance_snapshot_admission_mirrors_builder_rules() -> None:
    with pytest.raises(ValueError):
        BalanceSnapshot({(ALICE, ASSET_A): -1})
    with pytest.raises(TypeError):
        BalanceSnapshot({(ALICE, ASSET_A): True})
    with pytest.raises(TypeError):
        BalanceSnapshot({(ALICE, ASSET_A): "5"})
    with pytest.raises(TypeError):
        BalanceSnapshot({(1, ASSET_A): 5})
    with pytest.raises(TypeError):
        BalanceSnapshot({ALICE: 5})  # type: ignore[dict-item]
    assert BalanceSnapshot({(ALICE, ASSET_A): 0}).get_all_balances() == {}

    class HostileTable(BalanceTable):
        pass

    with pytest.raises(TypeError):
        snapshot_balances(HostileTable())
    with pytest.raises(TypeError):
        snapshot_balances({(ALICE, ASSET_A): 5})  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# STATE-ALIAS-003: LP balances and nested duration-risk rails
# ---------------------------------------------------------------------------


def _lp_builder() -> LPTable:
    table = LPTable()
    table.set(ALICE, POOL_ID, 10)
    table.set_last_mint_timestamp(ALICE, POOL_ID, 100)
    table.set_last_remove_timestamp(ALICE, POOL_ID, 90)
    table.set_churn_tier(ALICE, POOL_ID, 2)
    table.set_last_churn_update_timestamp(ALICE, POOL_ID, 95)
    # Metadata-only key: a fully removed position keeps its remove timestamp.
    table.set_last_remove_timestamp(BOB, POOL_ID, 50)
    table.set_churn_tier(BOB, POOL_ID, 1)
    return table


def test_lp_snapshot_preserves_every_rail_and_rejects_mutation() -> None:
    builder = _lp_builder()
    snapshot = snapshot_lp_table(builder)
    assert type(snapshot) is LPSnapshot

    for name in (
        "get_all_balances",
        "get_all_last_mint_timestamps",
        "get_all_last_remove_timestamps",
        "get_all_churn_tiers",
        "get_all_last_churn_update_timestamps",
        "get_all_duration_risk_metadata",
    ):
        assert getattr(snapshot, name)() == getattr(builder, name)(), name
    assert snapshot.get(ALICE, POOL_ID) == 10
    assert snapshot.get(BOB, POOL_ID) == 0
    assert snapshot.get_last_mint_timestamp(ALICE, POOL_ID) == 100
    assert snapshot.get_last_remove_timestamp(BOB, POOL_ID) == 50
    assert snapshot.get_churn_tier(BOB, POOL_ID) == 1
    assert snapshot.get_churn_tier("nobody", POOL_ID) == 0
    assert snapshot.get_duration_risk_metadata("nobody", POOL_ID) == LPDurationRiskMetadata()

    builder.set(ALICE, POOL_ID, 1)
    builder.clear_last_mint_timestamp(ALICE, POOL_ID)
    assert snapshot.get(ALICE, POOL_ID) == 10
    assert snapshot.get_last_mint_timestamp(ALICE, POOL_ID) == 100

    for name in ("set", "add", "subtract", "set_last_mint_timestamp", "set_churn_tier"):
        assert not hasattr(snapshot, name), name
    with pytest.raises(TypeError):
        snapshot._rows = ()  # type: ignore[misc]

    rebuilt = snapshot.to_table()
    assert isinstance(rebuilt, LPTable)
    assert snapshot_lp_table(rebuilt) == snapshot
    assert rebuilt.get_all_duration_risk_metadata() == _lp_builder().get_all_duration_risk_metadata()


def test_lp_snapshot_rejects_mint_timestamp_for_empty_balance_and_bad_rows() -> None:
    with pytest.raises(ValueError):
        LPPositionRow(amount=0, duration_risk=LPDurationRiskMetadata(last_mint_timestamp=1))
    with pytest.raises(TypeError):
        LPPositionRow(amount=True, duration_risk=LPDurationRiskMetadata())
    with pytest.raises(TypeError):
        LPSnapshot(balances={(ALICE, POOL_ID): 1}, duration_risk={(ALICE, POOL_ID): {"churn_tier": 1}})  # type: ignore[dict-item]
    with pytest.raises(TypeError):
        snapshot_lp_table(BalanceTable())  # type: ignore[arg-type]
    assert LPSnapshot(balances={(ALICE, POOL_ID): 0}).get_all_balances() == {}


# ---------------------------------------------------------------------------
# STATE-ALIAS-004: nonce/replay state
# ---------------------------------------------------------------------------


def test_nonce_snapshot_keeps_zero_entries_canonical_keys_and_u32_bounds() -> None:
    builder = NonceTable()
    builder.set_last(ALICE, 0)
    builder.set_last("0x" + "BB" * 48, U32_MAX)

    snapshot = snapshot_nonces(builder)
    assert type(snapshot) is NonceSnapshot
    assert snapshot.get_last(ALICE) == 0
    assert snapshot.get_last(BOB) == U32_MAX
    assert snapshot.get(BOB) == U32_MAX
    assert snapshot.get_all() == {ALICE: 0, BOB: U32_MAX}
    assert len(snapshot) == 2

    builder.set_last(ALICE, 9)
    assert snapshot.get_last(ALICE) == 0
    assert not hasattr(snapshot, "set_last")
    assert not hasattr(snapshot, "apply_accept")
    with pytest.raises(TypeError):
        snapshot._pubkeys = ()  # type: ignore[misc]
    with pytest.raises((TypeError, ValueError)):
        snapshot.get_last("not-a-pubkey")

    assert snapshot.to_table().get_all() == builder.get_all() | {ALICE: 0}
    assert snapshot_nonces(snapshot.to_table()) == snapshot

    with pytest.raises(TypeError):
        NonceSnapshot({ALICE: U32_MAX + 1})
    with pytest.raises(TypeError):
        NonceSnapshot({ALICE: -1})
    with pytest.raises(TypeError):
        NonceSnapshot({ALICE: True})
    with pytest.raises(ValueError):
        NonceSnapshot({ALICE: 1, "0x" + "AA" * 48: 2})
    with pytest.raises(TypeError):
        snapshot_nonces({ALICE: 1})  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# STATE-ALIAS-002: pool values and the pool mapping
# ---------------------------------------------------------------------------


def test_pool_snapshot_shares_builder_normalization_and_is_frozen() -> None:
    builder = _pool(asset0="0x" + "AA" * 32, asset1="0x" + "BB" * 32, curve_tag="cpmm")
    snapshot = snapshot_pool(builder)
    assert type(snapshot) is PoolSnapshot
    assert snapshot.asset0 == "0x" + "aa" * 32
    assert snapshot.asset1 == "0x" + "bb" * 32
    assert snapshot.curve_tag == "CPMM"
    assert snapshot.get_reserve(snapshot.asset1) == 2_000
    assert snapshot.get_constant_product() == builder.get_constant_product()
    assert snapshot.verify_invariant(builder.get_constant_product()) is True
    with pytest.raises(ValueError):
        snapshot.get_reserve(POOL_ID)

    with pytest.raises(FrozenInstanceError):
        snapshot.reserve0 = 1  # type: ignore[misc]
    builder.reserve0 += 5
    assert snapshot.reserve0 == 1_000

    rebuilt = copy_pool_state(snapshot)
    assert type(rebuilt) is PoolState
    assert snapshot_pool(rebuilt) == snapshot
    assert snapshot.to_pool_state() is not rebuilt
    assert snapshot_pool(snapshot) is snapshot

    with pytest.raises(TypeError):
        snapshot_pool(_pool(status="ACTIVE"))
    with pytest.raises(ValueError):
        PoolSnapshot(**{**builder.__dict__, "fee_bps": 10_001})

    class HostilePool(PoolState):
        pass

    with pytest.raises(TypeError):
        snapshot_pool(HostilePool(**builder.__dict__))
    with pytest.raises(TypeError):
        copy_pool_state(HostilePool(**builder.__dict__))


def test_pool_table_snapshot_is_an_owned_read_only_mapping() -> None:
    source = {POOL_ID: _pool()}
    table = snapshot_pool_table(source)
    assert type(table) is PoolTableSnapshot
    assert type(table[POOL_ID]) is PoolSnapshot
    assert POOL_ID in table
    assert 5 not in table  # type: ignore[comparison-overlap]
    assert list(table) == [POOL_ID]
    assert len(table) == 1
    assert table.get("missing") is None
    with pytest.raises(KeyError):
        table["missing"]

    # Mapping mutation surface is absent.
    with pytest.raises(TypeError):
        table[POOL_ID] = _pool()  # type: ignore[index]
    with pytest.raises(TypeError):
        del table[POOL_ID]  # type: ignore[attr-defined]
    for name in ("pop", "update", "clear", "setdefault"):
        assert not hasattr(table, name), name

    # The source dict and its pool builder are not aliased.
    source[POOL_ID].reserve0 = 1
    source["other"] = _pool(pool_id="0x" + "dd" * 32)
    assert table[POOL_ID].reserve0 == 1_000
    assert "other" not in table

    assert table == {POOL_ID: snapshot_pool(_pool())}
    assert table == snapshot_pool_table({POOL_ID: _pool()})
    assert table != {}
    assert snapshot_pool_table(table) is table
    assert dict(table) == {POOL_ID: table[POOL_ID]}
    rebuilt = table.to_table()
    assert type(rebuilt[POOL_ID]) is PoolState
    with pytest.raises(TypeError):
        snapshot_pool_table({1: _pool()})  # type: ignore[dict-item]
    with pytest.raises(TypeError):
        snapshot_pool_table([_pool()])  # type: ignore[arg-type]


def test_pool_snapshot_requires_owned_exact_string_fields() -> None:
    class StringValue(str):
        pass

    values = dict(vars(_pool()))
    for name in ("pool_id", "asset0", "asset1", "curve_tag", "curve_params"):
        with pytest.raises(TypeError, match=f"{name} must be an exact str"):
            PoolSnapshot(**{**values, name: StringValue(values[name])})


def test_lp_position_owns_normalized_duration_metadata() -> None:
    class IntegerValue(int):
        pass

    metadata = LPDurationRiskMetadata(
        last_mint_timestamp=IntegerValue(10),
        last_remove_timestamp=IntegerValue(9),
        churn_tier=IntegerValue(2),
        last_churn_update_timestamp=IntegerValue(8),
    )
    row = LPPositionRow(amount=5, duration_risk=metadata)
    assert row.duration_risk == metadata
    assert row.duration_risk is not metadata
    for name in (
        "last_mint_timestamp", "last_remove_timestamp", "churn_tier", "last_churn_update_timestamp",
    ):
        assert type(getattr(row.duration_risk, name)) is int


# ---------------------------------------------------------------------------
# Differential oracle: encoder parity between builders and committed snapshots
# ---------------------------------------------------------------------------


def _random_builders(rng: random.Random) -> tuple[BalanceTable, dict[str, PoolState], LPTable, NonceTable]:
    pubkeys = ["0x" + f"{i:02x}" * 48 for i in range(1, 5)]
    assets = ["0x" + f"{i:02x}" * 32 for i in range(1, 4)]
    balances = BalanceTable()
    for _ in range(rng.randint(0, 8)):
        balances.set(rng.choice(pubkeys), rng.choice(assets), rng.choice([0, 1, 2**32, 2**64 - 1, 2**70]))
    pools: dict[str, PoolState] = {}
    for index in range(rng.randint(0, 3)):
        pool_id = "0x" + f"{0xf0 + index:02x}" * 32
        pools[pool_id] = PoolState(
            pool_id=pool_id,
            asset0=assets[0],
            asset1=assets[1 + (index % 2)],
            reserve0=rng.randint(0, 2**64),
            reserve1=rng.randint(0, 2**64),
            fee_bps=rng.randint(0, 10_000),
            lp_supply=rng.randint(0, 2**64),
            status=rng.choice(list(PoolStatus)),
            created_at=rng.randint(0, 2**32),
        )
    lp = LPTable()
    for pool_id in pools:
        for pubkey in pubkeys:
            if rng.random() < 0.5:
                lp.set(pubkey, pool_id, rng.randint(1, 2**64))
                if rng.random() < 0.5:
                    lp.set_last_mint_timestamp(pubkey, pool_id, rng.randint(0, 2**32))
            if rng.random() < 0.3:
                lp.set_last_remove_timestamp(pubkey, pool_id, rng.randint(0, 2**32))
            if rng.random() < 0.3:
                lp.set_churn_tier(pubkey, pool_id, rng.randint(0, 5))
                lp.set_last_churn_update_timestamp(pubkey, pool_id, rng.randint(0, 2**32))
    nonces = NonceTable()
    for pubkey in pubkeys:
        if rng.random() < 0.6:
            nonces.set_last(pubkey, rng.choice([0, 1, U32_MAX]))
    return balances, pools, lp, nonces


def test_state_root_is_identical_for_builders_snapshots_and_round_trips() -> None:
    rng = random.Random(20260928)
    for _ in range(40):
        balances, pools, lp, nonces = _random_builders(rng)
        builder_root = compute_state_root(balances=balances, pools=pools, lp_balances=lp, nonces=nonces)

        snap_balances = snapshot_balances(balances)
        snap_pools = snapshot_pool_table(pools)
        snap_lp = snapshot_lp_table(lp)
        snap_nonces = snapshot_nonces(nonces)
        snapshot_root = compute_state_root(
            balances=snap_balances,
            pools=snap_pools,
            lp_balances=snap_lp,
            nonces=snap_nonces,
        )
        assert snapshot_root == builder_root

        round_trip_root = compute_state_root(
            balances=snap_balances.to_table(),
            pools=snap_pools.to_table(),
            lp_balances=snap_lp.to_table(),
            nonces=snap_nonces.to_table(),
        )
        assert round_trip_root == builder_root

        # Snapshotting is idempotent and value-equal across independent copies.
        assert snapshot_balances(snap_balances.to_table()) == snap_balances
        assert snapshot_lp_table(snap_lp.to_table()) == snap_lp
        assert snapshot_nonces(snap_nonces.to_table()) == snap_nonces
        assert snapshot_pool_table(snap_pools.to_table()) == snap_pools


def test_state_root_still_rejects_wrong_table_types() -> None:
    with pytest.raises(TypeError):
        compute_state_root(balances={}, pools={}, lp_balances=LPTable())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances={})  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=LPTable(), nonces={})  # type: ignore[arg-type]
