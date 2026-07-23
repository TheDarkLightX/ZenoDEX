from __future__ import annotations

from itertools import permutations
from types import MappingProxyType
from typing import cast

import pytest
from hypothesis import assume, given, settings
from hypothesis import strategies as st

from src.state.lp import LPTable
from src.state.state_snapshot_values import CommittedLPTableV1
from src.state.state_snapshots import snapshot_lp_table
from src.state.state_transitions import (
    CanonicalLPPositionPatchV1,
    LPPositionDeltaV1,
    LPPositionPatchApplyOkV1,
    LPPositionPatchBuildOkV1,
    LPPositionPatchCodeV1,
    LPPositionPatchRejectV1,
    LPPositionValueV1,
    LPPositionWriteV1,
    apply_canonical_lp_position_patch_v1,
    apply_lp_position_deltas_v1,
    build_canonical_lp_position_patch_v1,
)

_EMPTY = LPPositionValueV1()


def _set_legacy_position(
    table: LPTable,
    key: tuple[str, str],
    value: LPPositionValueV1,
) -> None:
    pubkey, pool_id = key
    table.set(pubkey, pool_id, value.balance)
    if value.last_mint_timestamp is None:
        table.clear_last_mint_timestamp(pubkey, pool_id)
    else:
        table.set_last_mint_timestamp(pubkey, pool_id, value.last_mint_timestamp)
    if value.last_remove_timestamp is None:
        table.clear_last_remove_timestamp(pubkey, pool_id)
    else:
        table.set_last_remove_timestamp(pubkey, pool_id, value.last_remove_timestamp)
    table.set_churn_tier(pubkey, pool_id, value.churn_tier)
    if value.last_churn_update_timestamp is None:
        table.clear_last_churn_update_timestamp(pubkey, pool_id)
    else:
        table.set_last_churn_update_timestamp(
            pubkey,
            pool_id,
            value.last_churn_update_timestamp,
        )


def _state(
    *positions: tuple[tuple[str, str], LPPositionValueV1],
) -> CommittedLPTableV1:
    source = LPTable()
    for key, value in positions:
        _set_legacy_position(source, key, value)
    return snapshot_lp_table(source)


def _patch(*writes: LPPositionWriteV1) -> CanonicalLPPositionPatchV1:
    result = build_canonical_lp_position_patch_v1(writes)
    if type(result) is not LPPositionPatchBuildOkV1:
        raise AssertionError(f"test LP patch construction failed: {result!r}")
    return result.patch


def _all_entries(
    table: CommittedLPTableV1,
) -> tuple[tuple[tuple[object, object], ...], ...]:
    return (
        table.balance_entries,
        table.last_mint_entries,
        table.last_remove_entries,
        table.churn_tier_entries,
        table.last_churn_update_entries,
    )


def test_lp_patch_builder_is_permutation_invariant() -> None:
    writes = (
        LPPositionWriteV1(
            ("carol", "pool-b"),
            _EMPTY,
            LPPositionValueV1(balance=9, last_mint_timestamp=4),
        ),
        LPPositionWriteV1(
            ("alice", "pool-a"),
            LPPositionValueV1(balance=7),
            LPPositionValueV1(balance=3, churn_tier=1),
        ),
        LPPositionWriteV1(
            ("bob", "pool-a"),
            LPPositionValueV1(last_remove_timestamp=8),
            _EMPTY,
        ),
    )

    built = tuple(_patch(*ordering) for ordering in permutations(writes))

    assert all(candidate == built[0] for candidate in built)
    assert tuple(write.key for write in built[0].writes) == (
        ("alice", "pool-a"),
        ("bob", "pool-a"),
        ("carol", "pool-b"),
    )


def test_lp_patch_builder_rejects_duplicate_and_noop_writes_canonically() -> None:
    left = LPPositionWriteV1(
        ("alice", "pool"),
        _EMPTY,
        LPPositionValueV1(balance=1),
    )
    right = LPPositionWriteV1(
        ("alice", "pool"),
        _EMPTY,
        LPPositionValueV1(last_remove_timestamp=1),
    )
    duplicates = tuple(
        build_canonical_lp_position_patch_v1(ordering)
        for ordering in ((left, right), (right, left))
    )

    assert duplicates == (
        LPPositionPatchRejectV1(
            LPPositionPatchCodeV1.DUPLICATE_WRITE,
            ("writes", "key", "alice", "pool"),
        ),
        LPPositionPatchRejectV1(
            LPPositionPatchCodeV1.DUPLICATE_WRITE,
            ("writes", "key", "alice", "pool"),
        ),
    )
    assert build_canonical_lp_position_patch_v1(
        (LPPositionWriteV1(("alice", "pool"), _EMPTY, _EMPTY),)
    ) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.NO_OP_WRITE,
        ("writes", 0),
    )
    assert build_canonical_lp_position_patch_v1(()) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.EMPTY_PATCH,
        ("writes",),
    )


def test_lp_position_value_and_write_enforce_exact_domain() -> None:
    with pytest.raises(TypeError, match="exact integer"):
        LPPositionValueV1(balance=True)
    with pytest.raises(ValueError, match="outside the committed domain"):
        LPPositionValueV1(balance=-1)
    with pytest.raises(TypeError, match="last_remove_timestamp"):
        LPPositionValueV1(last_remove_timestamp=True)
    with pytest.raises(ValueError, match="last_remove_timestamp"):
        LPPositionValueV1(last_remove_timestamp=-1)
    with pytest.raises(TypeError, match="churn_tier"):
        LPPositionValueV1(churn_tier=True)
    with pytest.raises(ValueError, match="churn_tier"):
        LPPositionValueV1(churn_tier=-1)
    with pytest.raises(ValueError, match="positive LP balance"):
        LPPositionValueV1(last_mint_timestamp=0)
    with pytest.raises(ValueError, match="not canonical"):
        LPPositionWriteV1(("", "pool"), _EMPTY, LPPositionValueV1(balance=1))
    with pytest.raises(ValueError, match="not canonical"):
        LPPositionWriteV1(("\ud800", "pool"), _EMPTY, LPPositionValueV1(balance=1))


def test_apply_lp_patch_updates_all_five_maps_atomically() -> None:
    alice_before = LPPositionValueV1(
        balance=10,
        last_mint_timestamp=2,
        last_remove_timestamp=3,
        churn_tier=1,
        last_churn_update_timestamp=4,
    )
    bob_before = LPPositionValueV1(
        last_remove_timestamp=5,
        churn_tier=2,
        last_churn_update_timestamp=6,
    )
    pre = _state(
        (("alice", "pool-a"), alice_before),
        (("bob", "pool-b"), bob_before),
    )
    before = _all_entries(pre)
    alice_after = LPPositionValueV1(
        balance=7,
        last_mint_timestamp=10,
        last_remove_timestamp=11,
        churn_tier=3,
        last_churn_update_timestamp=12,
    )
    carol_after = LPPositionValueV1(
        balance=4,
        last_mint_timestamp=13,
        last_remove_timestamp=14,
        last_churn_update_timestamp=15,
    )
    patch = _patch(
        LPPositionWriteV1(("carol", "pool-c"), _EMPTY, carol_after),
        LPPositionWriteV1(("bob", "pool-b"), bob_before, _EMPTY),
        LPPositionWriteV1(("alice", "pool-a"), alice_before, alice_after),
    )

    result = apply_canonical_lp_position_patch_v1(pre, patch)

    assert type(result) is LPPositionPatchApplyOkV1
    assert result.patch is patch
    assert result.state is not pre
    assert type(result.state) is CommittedLPTableV1
    assert _all_entries(pre) == before
    assert result.state.balance_entries == (
        (("alice", "pool-a"), 7),
        (("carol", "pool-c"), 4),
    )
    assert result.state.last_mint_entries == (
        (("alice", "pool-a"), 10),
        (("carol", "pool-c"), 13),
    )
    assert result.state.last_remove_entries == (
        (("alice", "pool-a"), 11),
        (("carol", "pool-c"), 14),
    )
    assert result.state.churn_tier_entries == ((("alice", "pool-a"), 3),)
    assert result.state.last_churn_update_entries == (
        (("alice", "pool-a"), 12),
        (("carol", "pool-c"), 15),
    )


def test_apply_lp_patch_preserves_valid_metadata_only_position() -> None:
    pre = _state()
    metadata_only = LPPositionValueV1(
        last_remove_timestamp=7,
        churn_tier=2,
        last_churn_update_timestamp=8,
    )

    result = apply_canonical_lp_position_patch_v1(
        pre,
        _patch(LPPositionWriteV1(("alice", "pool"), _EMPTY, metadata_only)),
    )

    assert type(result) is LPPositionPatchApplyOkV1
    assert result.state.balance_entries == ()
    assert result.state.last_mint_entries == ()
    assert result.state.last_remove_entries == ((("alice", "pool"), 7),)
    assert result.state.churn_tier_entries == ((("alice", "pool"), 2),)
    assert result.state.last_churn_update_entries == ((("alice", "pool"), 8),)


def test_lp_delta_reduction_is_permutation_invariant_and_preserves_metadata() -> None:
    before = LPPositionValueV1(
        balance=10,
        last_mint_timestamp=2,
        last_remove_timestamp=3,
        churn_tier=1,
        last_churn_update_timestamp=4,
    )
    pre = _state((("alice", "pool"), before))
    deltas = (
        LPPositionDeltaV1(("alice", "pool"), -4),
        LPPositionDeltaV1(("alice", "pool"), 1),
        LPPositionDeltaV1(("bob", "pool"), 5),
    )

    results = tuple(apply_lp_position_deltas_v1(pre, ordering) for ordering in permutations(deltas))

    assert all(type(result) is LPPositionPatchApplyOkV1 for result in results)
    states = tuple(cast(LPPositionPatchApplyOkV1, result).state for result in results)
    assert all(_all_entries(state) == _all_entries(states[0]) for state in states)
    assert states[0].balance_entries == (
        (("alice", "pool"), 7),
        (("bob", "pool"), 5),
    )
    assert states[0].last_mint_entries == ((("alice", "pool"), 2),)
    assert states[0].last_remove_entries == ((("alice", "pool"), 3),)
    assert states[0].churn_tier_entries == ((("alice", "pool"), 1),)
    assert states[0].last_churn_update_entries == ((("alice", "pool"), 4),)


def test_lp_delta_burn_to_zero_clears_only_last_mint_metadata() -> None:
    before = LPPositionValueV1(
        balance=4,
        last_mint_timestamp=2,
        last_remove_timestamp=3,
        churn_tier=1,
        last_churn_update_timestamp=4,
    )
    pre = _state((("alice", "pool"), before))

    result = apply_lp_position_deltas_v1(
        pre,
        (LPPositionDeltaV1(("alice", "pool"), -4),),
    )

    assert type(result) is LPPositionPatchApplyOkV1
    assert result.state.balance_entries == ()
    assert result.state.last_mint_entries == ()
    assert result.state.last_remove_entries == ((("alice", "pool"), 3),)
    assert result.state.churn_tier_entries == ((("alice", "pool"), 1),)
    assert result.state.last_churn_update_entries == ((("alice", "pool"), 4),)


def test_lp_delta_rejects_out_of_range_without_candidate_or_prestate_mutation() -> None:
    pre = _state((("alice", "pool"), LPPositionValueV1(balance=2)))
    before = _all_entries(pre)

    result = apply_lp_position_deltas_v1(
        pre,
        (LPPositionDeltaV1(("alice", "pool"), -3),),
    )

    assert result == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.OUT_OF_RANGE,
        ("deltas", "net_delta"),
    )
    assert not hasattr(result, "state")
    assert _all_entries(pre) == before


def test_lp_delta_constructor_and_application_reject_nonexact_values() -> None:
    with pytest.raises(TypeError, match="exact integer"):
        LPPositionDeltaV1(("alice", "pool"), True)
    with pytest.raises(ValueError, match="nonzero"):
        LPPositionDeltaV1(("alice", "pool"), 0)

    delta = LPPositionDeltaV1(("alice", "pool"), 1)
    object.__setattr__(delta, "net_delta", True)
    assert apply_lp_position_deltas_v1(_state(), (delta,)) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.WRONG_EXACT_TYPE,
        ("deltas", "net_delta"),
    )


def test_apply_lp_expected_mismatch_returns_no_candidate() -> None:
    actual = LPPositionValueV1(balance=5, last_mint_timestamp=2)
    pre = _state((("alice", "pool"), actual))
    before = _all_entries(pre)
    patch = _patch(
        LPPositionWriteV1(
            ("alice", "pool"),
            LPPositionValueV1(balance=5, last_mint_timestamp=3),
            LPPositionValueV1(balance=4, last_mint_timestamp=3),
        )
    )

    result = apply_canonical_lp_position_patch_v1(pre, patch)

    assert result == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.EXPECTED_OLD_MISMATCH,
        ("writes", 0, "expected"),
    )
    assert not hasattr(result, "state")
    assert _all_entries(pre) == before


def test_apply_lp_revalidates_corrupted_patch_and_prestate() -> None:
    value = LPPositionValueV1(balance=5, last_mint_timestamp=2)
    pre = _state((("alice", "pool"), value))
    patch = _patch(
        LPPositionWriteV1(
            ("alice", "pool"),
            value,
            LPPositionValueV1(balance=4, last_mint_timestamp=2),
        )
    )
    object.__setattr__(patch, "writes", ("corrupt",))

    assert apply_canonical_lp_position_patch_v1(pre, patch) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.NONCANONICAL_PATCH,
        ("writes", 0),
    )

    clean_patch = _patch(
        LPPositionWriteV1(
            ("alice", "pool"),
            value,
            LPPositionValueV1(balance=4, last_mint_timestamp=2),
        )
    )
    owned_balances = object.__getattribute__(pre, "_balances")
    object.__setattr__(owned_balances, "_entries", ((("alice", "pool"), True),))
    assert apply_canonical_lp_position_patch_v1(
        pre,
        clean_patch,
    ) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.INVALID_PRESTATE,
        ("state", "_balances"),
    )


def test_apply_lp_rejects_subclass_and_corrupt_owned_index() -> None:
    pre = _state()
    patch = _patch(
        LPPositionWriteV1(
            ("alice", "pool"),
            _EMPTY,
            LPPositionValueV1(balance=1),
        )
    )
    patch_subclass = type("_LPPatchSubclass", (CanonicalLPPositionPatchV1,), {})
    subclass = patch_subclass(patch.writes)

    assert apply_canonical_lp_position_patch_v1(
        pre,
        cast(CanonicalLPPositionPatchV1, subclass),
    ) == LPPositionPatchRejectV1(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ())

    owned_balances = object.__getattribute__(pre, "_balances")
    object.__setattr__(owned_balances, "_index", MappingProxyType({("hostile", "key"): 1}))
    assert apply_canonical_lp_position_patch_v1(
        pre,
        patch,
    ) == LPPositionPatchRejectV1(
        LPPositionPatchCodeV1.INVALID_PRESTATE,
        ("state", "_balances"),
    )


@st.composite
def _position_values(draw: st.DrawFn) -> LPPositionValueV1:
    balance = draw(st.integers(min_value=0, max_value=1_000))
    optional_timestamp = st.one_of(st.none(), st.integers(min_value=0, max_value=1_000))
    return LPPositionValueV1(
        balance=balance,
        last_mint_timestamp=(draw(optional_timestamp) if balance > 0 else None),
        last_remove_timestamp=draw(optional_timestamp),
        churn_tier=draw(st.integers(min_value=0, max_value=5)),
        last_churn_update_timestamp=draw(optional_timestamp),
    )


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=0, max_value=12),
        values=_position_values(),
        max_size=8,
    ),
    replacements=st.dictionaries(
        keys=st.integers(min_value=0, max_value=12),
        values=_position_values(),
        min_size=1,
        max_size=8,
    ),
)
def test_lp_patch_matches_logical_map_and_legacy_reference(
    pre_values: dict[int, LPPositionValueV1],
    replacements: dict[int, LPPositionValueV1],
) -> None:
    def key(index: int) -> tuple[str, str]:
        return (f"account-{index:02d}", "pool")

    pre = _state(*((key(index), value) for index, value in pre_values.items()))
    before = _all_entries(pre)
    writes = tuple(
        LPPositionWriteV1(
            key(index),
            pre_values.get(index, _EMPTY),
            replacement,
        )
        for index, replacement in replacements.items()
        if replacement != pre_values.get(index, _EMPTY)
    )
    if not writes:
        return
    patch_result = build_canonical_lp_position_patch_v1(writes)
    assert type(patch_result) is LPPositionPatchBuildOkV1

    result = apply_canonical_lp_position_patch_v1(pre, patch_result.patch)

    assert type(result) is LPPositionPatchApplyOkV1
    legacy = LPTable()
    for index, value in pre_values.items():
        _set_legacy_position(legacy, key(index), value)
    for index, replacement in replacements.items():
        _set_legacy_position(legacy, key(index), replacement)
    assert _all_entries(result.state) == _all_entries(snapshot_lp_table(legacy))
    assert _all_entries(pre) == before


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=0, max_value=12),
        values=_position_values(),
        max_size=8,
    ),
    delta_by=st.dictionaries(
        keys=st.integers(min_value=0, max_value=12),
        values=st.integers(min_value=-20, max_value=20).filter(lambda value: value != 0),
        min_size=1,
        max_size=8,
    ),
)
def test_lp_delta_reduction_matches_legacy_reference(
    pre_values: dict[int, LPPositionValueV1],
    delta_by: dict[int, int],
) -> None:
    def key(index: int) -> tuple[str, str]:
        return (f"account-{index:02d}", "pool")

    assume(
        all(
            0 <= pre_values.get(index, _EMPTY).balance + delta <= 1_000
            for index, delta in delta_by.items()
        )
    )
    pre = _state(*((key(index), value) for index, value in pre_values.items()))
    before = _all_entries(pre)
    deltas = tuple(LPPositionDeltaV1(key(index), delta) for index, delta in delta_by.items())

    result = apply_lp_position_deltas_v1(pre, deltas)

    assert type(result) is LPPositionPatchApplyOkV1
    legacy = LPTable()
    for index, value in pre_values.items():
        _set_legacy_position(legacy, key(index), value)
    for index, delta in delta_by.items():
        pubkey, pool_id = key(index)
        if delta > 0:
            legacy.add(pubkey, pool_id, delta)
        else:
            legacy.subtract(pubkey, pool_id, -delta)
    assert _all_entries(result.state) == _all_entries(snapshot_lp_table(legacy))
    assert _all_entries(pre) == before
