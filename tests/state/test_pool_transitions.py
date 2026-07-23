from __future__ import annotations

from itertools import permutations
from types import MappingProxyType
from typing import cast

import pytest
from hypothesis import assume, given, settings
from hypothesis import strategies as st

from src.core.batch_clearing import apply_settlement_pure
from src.core.settlement import LPDelta, ReserveDelta, Settlement
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.owned_collections import OwnedMapV1
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshot_values import CommittedPoolStateV1
from src.state.state_snapshots import snapshot_pool, snapshot_pool_map
from src.state.state_transitions import (
    CanonicalPoolPatchV1,
    PoolPatchApplyOkV1,
    PoolPatchBuildOkV1,
    PoolPatchCodeV1,
    PoolPatchRejectV1,
    PoolReserveDeltaV1,
    PoolSupplyDeltaV1,
    PoolWriteV1,
    apply_canonical_pool_patch_v1,
    apply_pool_deltas_v1,
    build_canonical_pool_patch_v1,
)


def _legacy_pool(
    index: int,
    *,
    reserve0: int = 100,
    reserve1: int = 200,
    lp_supply: int = 50,
) -> PoolState:
    asset0 = "0x" + f"{index + 1:02x}" * 32
    asset1 = "0x" + f"{index + 129:02x}" * 32
    pool_id = compute_pool_id(asset0, asset1, 30)
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=30,
        lp_supply=lp_supply,
        status=PoolStatus.ACTIVE,
        created_at=index,
    )


def _committed_pool(
    index: int,
    *,
    reserve0: int = 100,
    reserve1: int = 200,
    lp_supply: int = 50,
) -> CommittedPoolStateV1:
    return snapshot_pool(
        _legacy_pool(
            index,
            reserve0=reserve0,
            reserve1=reserve1,
            lp_supply=lp_supply,
        )
    )


def _evolve_pool(
    pool: CommittedPoolStateV1,
    *,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
) -> CommittedPoolStateV1:
    return CommittedPoolStateV1(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=lp_supply,
        status=pool.status,
        created_at=pool.created_at,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )


def _state(*pools: PoolState) -> OwnedMapV1[str, CommittedPoolStateV1]:
    return snapshot_pool_map({pool.pool_id: pool for pool in pools})


def _patch(*writes: PoolWriteV1) -> CanonicalPoolPatchV1:
    result = build_canonical_pool_patch_v1(writes)
    if type(result) is not PoolPatchBuildOkV1:
        raise AssertionError(f"test pool patch construction failed: {result!r}")
    return result.patch


def test_pool_patch_builder_is_permutation_invariant() -> None:
    existing0 = _committed_pool(0)
    existing1 = _committed_pool(1)
    inserted = _committed_pool(2)
    writes = (
        PoolWriteV1(
            existing1.pool_id,
            existing1,
            _evolve_pool(existing1, reserve0=101, reserve1=199, lp_supply=50),
        ),
        PoolWriteV1(inserted.pool_id, None, inserted),
        PoolWriteV1(existing0.pool_id, existing0, None),
    )

    built = tuple(_patch(*ordering) for ordering in permutations(writes))

    assert all(candidate == built[0] for candidate in built)
    assert tuple(write.pool_id for write in built[0].writes) == tuple(
        sorted((existing0.pool_id, existing1.pool_id, inserted.pool_id))
    )


def test_pool_patch_builder_rejects_duplicate_noop_and_empty_writes() -> None:
    pool = _committed_pool(0)
    replacement = _evolve_pool(pool, reserve0=101, reserve1=199, lp_supply=50)
    left = PoolWriteV1(pool.pool_id, pool, replacement)
    right = PoolWriteV1(pool.pool_id, pool, None)

    duplicate_results = tuple(
        build_canonical_pool_patch_v1(ordering) for ordering in ((left, right), (right, left))
    )

    assert duplicate_results == (
        PoolPatchRejectV1(
            PoolPatchCodeV1.DUPLICATE_WRITE,
            ("writes", "pool_id", pool.pool_id),
        ),
        PoolPatchRejectV1(
            PoolPatchCodeV1.DUPLICATE_WRITE,
            ("writes", "pool_id", pool.pool_id),
        ),
    )
    assert build_canonical_pool_patch_v1((PoolWriteV1(pool.pool_id, pool, pool),)) == (
        PoolPatchRejectV1(PoolPatchCodeV1.NO_OP_WRITE, ("writes", 0))
    )
    assert build_canonical_pool_patch_v1(()) == PoolPatchRejectV1(
        PoolPatchCodeV1.EMPTY_PATCH,
        ("writes",),
    )


def test_pool_write_constructor_requires_exact_key_binding() -> None:
    pool = _committed_pool(0)
    with pytest.raises(TypeError, match="exact string"):
        PoolWriteV1(cast(str, True), None, pool)
    with pytest.raises(ValueError, match="not canonical"):
        PoolWriteV1("", None, pool)
    with pytest.raises(ValueError, match="does not bind"):
        PoolWriteV1(_committed_pool(1).pool_id, None, pool)


def test_pool_patch_builder_rejects_corrupted_exact_pool() -> None:
    pool = _committed_pool(0)
    object.__setattr__(pool, "reserve0", True)
    write = PoolWriteV1(pool.pool_id, None, pool)

    result = build_canonical_pool_patch_v1((write,))

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.INVALID_POOL_STATE,
        ("writes", 0, "replacement", "reserve0"),
    )


def test_pool_patch_builder_owns_replacement_before_returning() -> None:
    replacement = _committed_pool(0)
    patch = _patch(PoolWriteV1(replacement.pool_id, None, replacement))
    owned_replacement = patch.writes[0].replacement
    if owned_replacement is None:
        raise AssertionError("test insertion must retain an owned replacement")

    object.__setattr__(replacement, "reserve0", 999)

    assert owned_replacement is not replacement
    assert owned_replacement.reserve0 == 100


def test_apply_pool_patch_inserts_updates_and_deletes_atomically() -> None:
    legacy0 = _legacy_pool(0)
    legacy1 = _legacy_pool(1)
    pre = _state(legacy0, legacy1)
    before = pre.entries
    pool0 = pre[legacy0.pool_id]
    pool1 = pre[legacy1.pool_id]
    inserted = _committed_pool(2, reserve0=7, reserve1=9, lp_supply=3)
    replacement = _evolve_pool(pool1, reserve0=190, reserve1=215, lp_supply=55)
    patch = _patch(
        PoolWriteV1(inserted.pool_id, None, inserted),
        PoolWriteV1(pool0.pool_id, pool0, None),
        PoolWriteV1(pool1.pool_id, pool1, replacement),
    )

    result = apply_canonical_pool_patch_v1(pre, patch)

    assert type(result) is PoolPatchApplyOkV1
    assert result.state is not pre
    assert pre.entries == before
    assert tuple(pool_id for pool_id, _pool in result.state.entries) == tuple(
        sorted((pool1.pool_id, inserted.pool_id))
    )
    assert result.state[pool1.pool_id].reserve0 == 190
    assert result.state[pool1.pool_id].reserve1 == 215
    assert result.state[pool1.pool_id].lp_supply == 55
    assert result.state[inserted.pool_id] == inserted


def test_apply_pool_expected_mismatch_returns_no_candidate() -> None:
    legacy = _legacy_pool(0)
    pre = _state(legacy)
    actual = pre[legacy.pool_id]
    wrong_expected = _evolve_pool(actual, reserve0=99, reserve1=200, lp_supply=50)
    patch = _patch(PoolWriteV1(actual.pool_id, wrong_expected, None))
    before = pre.entries

    result = apply_canonical_pool_patch_v1(pre, patch)

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.EXPECTED_OLD_MISMATCH,
        ("writes", 0, "expected"),
    )
    assert not hasattr(result, "state")
    assert pre.entries == before


def test_apply_pool_revalidates_corrupted_patch_and_prestate() -> None:
    legacy = _legacy_pool(0)
    pre = _state(legacy)
    pool = pre[legacy.pool_id]
    patch = _patch(PoolWriteV1(pool.pool_id, pool, None))
    object.__setattr__(patch, "writes", ("corrupt",))

    assert apply_canonical_pool_patch_v1(pre, patch) == PoolPatchRejectV1(
        PoolPatchCodeV1.NONCANONICAL_PATCH,
        ("writes", 0),
    )

    clean_patch = _patch(PoolWriteV1(pool.pool_id, pool, None))
    object.__setattr__(pre, "_index", MappingProxyType({pool.pool_id: 999}))
    assert apply_canonical_pool_patch_v1(pre, clean_patch) == PoolPatchRejectV1(
        PoolPatchCodeV1.INVALID_PRESTATE,
        ("state",),
    )


def test_apply_pool_rejects_patch_and_prestate_subclasses() -> None:
    pre = _state()
    pool = _committed_pool(0)
    patch = _patch(PoolWriteV1(pool.pool_id, None, pool))
    patch_subclass = type("_PoolPatchSubclass", (CanonicalPoolPatchV1,), {})
    subclass = patch_subclass(patch.writes)

    assert apply_canonical_pool_patch_v1(
        pre,
        cast(CanonicalPoolPatchV1, subclass),
    ) == PoolPatchRejectV1(PoolPatchCodeV1.WRONG_EXACT_TYPE, ())

    map_subclass = type("_PoolMapSubclass", (OwnedMapV1,), {})
    subclass_map: object = object.__new__(map_subclass)
    for field_name in ("_schema_revision", "_schema_id", "_entries", "_index"):
        object.__setattr__(
            subclass_map,
            field_name,
            object.__getattribute__(pre, field_name),
        )
    assert apply_canonical_pool_patch_v1(
        cast(OwnedMapV1[str, CommittedPoolStateV1], subclass_map),
        patch,
    ) == PoolPatchRejectV1(PoolPatchCodeV1.WRONG_EXACT_TYPE, ())


def test_pool_patch_replays_legacy_settlement_pool_projection() -> None:
    legacy = _legacy_pool(0, reserve0=100, reserve1=200, lp_supply=50)
    pre = _state(legacy)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[
            ReserveDelta(legacy.pool_id, legacy.asset0, delta_add=9, delta_sub=0),
            ReserveDelta(legacy.pool_id, legacy.asset1, delta_add=0, delta_sub=4),
        ],
        lp_deltas=[LPDelta("alice", legacy.pool_id, delta_add=3, delta_sub=0)],
    )

    _balances, legacy_pools, _lp = apply_settlement_pure(
        settlement,
        BalanceTable(),
        {legacy.pool_id: legacy},
        LPTable(),
    )
    expected = snapshot_pool_map(legacy_pools)
    before_pool = pre[legacy.pool_id]
    after_pool = expected[legacy.pool_id]
    result = apply_canonical_pool_patch_v1(
        pre,
        _patch(PoolWriteV1(legacy.pool_id, before_pool, after_pool)),
    )

    assert type(result) is PoolPatchApplyOkV1
    assert result.state.entries == expected.entries
    assert pre[legacy.pool_id].reserve0 == 100
    assert pre[legacy.pool_id].reserve1 == 200
    assert pre[legacy.pool_id].lp_supply == 50


def test_pool_delta_reduction_is_permutation_invariant() -> None:
    legacy = _legacy_pool(0, reserve0=100, reserve1=200, lp_supply=50)
    pre = _state(legacy)
    reserve_deltas = (
        PoolReserveDeltaV1(legacy.pool_id, legacy.asset0, 11),
        PoolReserveDeltaV1(legacy.pool_id, legacy.asset0, -2),
        PoolReserveDeltaV1(legacy.pool_id, legacy.asset1, -5),
        PoolReserveDeltaV1(legacy.pool_id, legacy.asset1, 1),
    )
    supply_deltas = (
        PoolSupplyDeltaV1(legacy.pool_id, 3),
        PoolSupplyDeltaV1(legacy.pool_id, -1),
    )

    results = tuple(
        apply_pool_deltas_v1(pre, reserve_order, supply_order)
        for reserve_order in permutations(reserve_deltas)
        for supply_order in permutations(supply_deltas)
    )

    assert all(type(result) is PoolPatchApplyOkV1 for result in results)
    states = tuple(cast(PoolPatchApplyOkV1, result).state for result in results)
    assert all(state.entries == states[0].entries for state in states)
    candidate = states[0][legacy.pool_id]
    assert candidate.reserve0 == 109
    assert candidate.reserve1 == 196
    assert candidate.lp_supply == 52
    assert pre[legacy.pool_id].reserve0 == 100
    assert pre[legacy.pool_id].reserve1 == 200
    assert pre[legacy.pool_id].lp_supply == 50


def test_pool_delta_replays_legacy_settlement_pool_projection() -> None:
    legacy = _legacy_pool(0, reserve0=100, reserve1=200, lp_supply=50)
    pre = _state(legacy)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[
            ReserveDelta(legacy.pool_id, legacy.asset0, delta_add=9, delta_sub=0),
            ReserveDelta(legacy.pool_id, legacy.asset1, delta_add=0, delta_sub=4),
        ],
        lp_deltas=[LPDelta("alice", legacy.pool_id, delta_add=3, delta_sub=0)],
    )

    _balances, legacy_pools, _lp = apply_settlement_pure(
        settlement,
        BalanceTable(),
        {legacy.pool_id: legacy},
        LPTable(),
    )
    result = apply_pool_deltas_v1(
        pre,
        (
            PoolReserveDeltaV1(legacy.pool_id, legacy.asset0, 9),
            PoolReserveDeltaV1(legacy.pool_id, legacy.asset1, -4),
        ),
        (PoolSupplyDeltaV1(legacy.pool_id, 3),),
    )

    assert type(result) is PoolPatchApplyOkV1
    assert result.state.entries == snapshot_pool_map(legacy_pools).entries


def test_pool_delta_validates_references_before_cancellation() -> None:
    legacy = _legacy_pool(0)
    pre = _state(legacy)

    unknown_reserve = apply_pool_deltas_v1(
        pre,
        (
            PoolReserveDeltaV1("missing", "asset", 1),
            PoolReserveDeltaV1("missing", "asset", -1),
        ),
        (),
    )
    unknown_supply = apply_pool_deltas_v1(
        pre,
        (),
        (
            PoolSupplyDeltaV1("missing", 1),
            PoolSupplyDeltaV1("missing", -1),
        ),
    )
    wrong_asset = apply_pool_deltas_v1(
        pre,
        (
            PoolReserveDeltaV1(legacy.pool_id, "wrong-asset", 1),
            PoolReserveDeltaV1(legacy.pool_id, "wrong-asset", -1),
        ),
        (),
    )

    assert unknown_reserve == PoolPatchRejectV1(
        PoolPatchCodeV1.UNKNOWN_POOL,
        ("pools", "missing"),
    )
    assert unknown_supply == unknown_reserve
    assert wrong_asset == PoolPatchRejectV1(
        PoolPatchCodeV1.ASSET_MISMATCH,
        ("pools", legacy.pool_id, "asset"),
    )
    assert all(
        not hasattr(result, "state") for result in (unknown_reserve, unknown_supply, wrong_asset)
    )
    assert pre[legacy.pool_id].reserve0 == 100
    assert pre[legacy.pool_id].reserve1 == 200
    assert pre[legacy.pool_id].lp_supply == 50


@pytest.mark.parametrize("kind", ("reserve", "supply"))
def test_pool_delta_rejects_out_of_range_without_candidate_or_prestate_mutation(
    kind: str,
) -> None:
    pre = _legacy_pool(0, reserve0=0, lp_supply=0)
    committed = _state(pre)
    before = committed.entries
    reserve_atoms = (PoolReserveDeltaV1(pre.pool_id, pre.asset0, -1),) if kind == "reserve" else ()
    supply_atoms = (PoolSupplyDeltaV1(pre.pool_id, -1),) if kind == "supply" else ()

    result = apply_pool_deltas_v1(committed, reserve_atoms, supply_atoms)

    assert result == PoolPatchRejectV1(
        PoolPatchCodeV1.OUT_OF_RANGE,
        ("pools", pre.pool_id),
    )
    assert not hasattr(result, "state")
    assert committed.entries == before


def test_pool_delta_constructor_and_application_reject_nonexact_values() -> None:
    legacy = _legacy_pool(0)
    with pytest.raises(TypeError, match="exact integer"):
        PoolReserveDeltaV1(legacy.pool_id, legacy.asset0, True)
    with pytest.raises(ValueError, match="nonzero"):
        PoolSupplyDeltaV1(legacy.pool_id, 0)

    delta = PoolReserveDeltaV1(legacy.pool_id, legacy.asset0, 1)
    object.__setattr__(delta, "net_delta", True)
    assert apply_pool_deltas_v1(_state(legacy), (delta,), ()) == PoolPatchRejectV1(
        PoolPatchCodeV1.WRONG_EXACT_TYPE,
        ("reserve_deltas", "net_delta"),
    )


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=0, max_value=10),
        values=st.tuples(
            st.integers(min_value=0, max_value=10_000),
            st.integers(min_value=0, max_value=10_000),
            st.integers(min_value=0, max_value=10_000),
        ),
        max_size=7,
    ),
    replacements=st.dictionaries(
        keys=st.integers(min_value=0, max_value=10),
        values=st.one_of(
            st.none(),
            st.tuples(
                st.integers(min_value=0, max_value=10_000),
                st.integers(min_value=0, max_value=10_000),
                st.integers(min_value=0, max_value=10_000),
            ),
        ),
        min_size=1,
        max_size=7,
    ),
)
def test_pool_patch_matches_logical_map_and_legacy_reference(
    pre_values: dict[int, tuple[int, int, int]],
    replacements: dict[int, tuple[int, int, int] | None],
) -> None:
    legacy_pre = {
        index: _legacy_pool(
            index,
            reserve0=values[0],
            reserve1=values[1],
            lp_supply=values[2],
        )
        for index, values in pre_values.items()
    }
    pre = _state(*legacy_pre.values())
    before = pre.entries
    by_index = {index: pre[pool.pool_id] for index, pool in legacy_pre.items()}
    writes: list[PoolWriteV1] = []
    expected_legacy = dict(legacy_pre)
    for index, replacement_values in replacements.items():
        expected = by_index.get(index)
        if replacement_values is None:
            replacement = None
            expected_legacy.pop(index, None)
        else:
            replacement = _committed_pool(
                index,
                reserve0=replacement_values[0],
                reserve1=replacement_values[1],
                lp_supply=replacement_values[2],
            )
            expected_legacy[index] = _legacy_pool(
                index,
                reserve0=replacement_values[0],
                reserve1=replacement_values[1],
                lp_supply=replacement_values[2],
            )
        if expected == replacement:
            continue
        if expected is not None:
            pool_id = expected.pool_id
        elif replacement is not None:
            pool_id = replacement.pool_id
        else:
            raise AssertionError("non-noop pool write must contain a pool value")
        writes.append(PoolWriteV1(pool_id, expected, replacement))
    if not writes:
        return

    patch_result = build_canonical_pool_patch_v1(tuple(reversed(writes)))
    assert type(patch_result) is PoolPatchBuildOkV1
    result = apply_canonical_pool_patch_v1(pre, patch_result.patch)

    assert type(result) is PoolPatchApplyOkV1
    expected = snapshot_pool_map({pool.pool_id: pool for pool in expected_legacy.values()})
    assert result.state.entries == expected.entries
    assert pre.entries == before


@settings(max_examples=100, deadline=None)
@given(
    reserve0=st.integers(min_value=0, max_value=10_000),
    reserve1=st.integers(min_value=0, max_value=10_000),
    lp_supply=st.integers(min_value=0, max_value=10_000),
    reserve0_delta=st.integers(min_value=-100, max_value=100),
    reserve1_delta=st.integers(min_value=-100, max_value=100),
    supply_delta=st.integers(min_value=-100, max_value=100),
)
def test_pool_delta_reduction_matches_legacy_reference(
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    reserve0_delta: int,
    reserve1_delta: int,
    supply_delta: int,
) -> None:
    assume(any(delta != 0 for delta in (reserve0_delta, reserve1_delta, supply_delta)))
    assume(reserve0 + reserve0_delta >= 0)
    assume(reserve1 + reserve1_delta >= 0)
    assume(lp_supply + supply_delta >= 0)
    legacy = _legacy_pool(
        0,
        reserve0=reserve0,
        reserve1=reserve1,
        lp_supply=lp_supply,
    )
    pre = _state(legacy)
    reserve_atoms = tuple(
        PoolReserveDeltaV1(legacy.pool_id, asset, delta)
        for asset, delta in (
            (legacy.asset0, reserve0_delta),
            (legacy.asset1, reserve1_delta),
        )
        if delta != 0
    )
    supply_atoms = (PoolSupplyDeltaV1(legacy.pool_id, supply_delta),) if supply_delta != 0 else ()
    legacy_lp = LPTable()
    if lp_supply > 0:
        legacy_lp.set("alice", legacy.pool_id, lp_supply)
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[
            ReserveDelta(
                legacy.pool_id,
                asset,
                delta_add=max(delta, 0),
                delta_sub=max(-delta, 0),
            )
            for asset, delta in (
                (legacy.asset0, reserve0_delta),
                (legacy.asset1, reserve1_delta),
            )
            if delta != 0
        ],
        lp_deltas=(
            [
                LPDelta(
                    "alice",
                    legacy.pool_id,
                    delta_add=max(supply_delta, 0),
                    delta_sub=max(-supply_delta, 0),
                )
            ]
            if supply_delta != 0
            else []
        ),
    )

    result = apply_pool_deltas_v1(pre, reserve_atoms, supply_atoms)
    _balances, legacy_pools, _lp = apply_settlement_pure(
        settlement,
        BalanceTable(),
        {legacy.pool_id: legacy},
        legacy_lp,
    )

    assert type(result) is PoolPatchApplyOkV1
    assert result.state.entries == snapshot_pool_map(legacy_pools).entries
