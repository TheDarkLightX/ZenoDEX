from __future__ import annotations

from itertools import permutations
from types import MappingProxyType
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.state.snapshot_combinators import (
    MAX_CANONICAL_BYTES_V1,
    AdmissionLimitsV1,
    AdmitOk,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)
from src.state.state_admission_profile import admit
from src.state.state_snapshot_schema import BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1
from src.state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    CommittedBalanceTableV1,
    _BalanceSourceV1,
)
from src.state.state_transitions import (
    BalanceDeltaV1,
    BalancePatchApplyOkV1,
    BalancePatchBuildOkV1,
    BalancePatchCodeV1,
    BalancePatchRejectV1,
    BalanceWriteV1,
    CanonicalBalancePatchV1,
    apply_balance_deltas_v1,
    apply_canonical_balance_patch_v1,
    build_canonical_balance_patch_v1,
)


def _limits() -> ValidatedAdmissionLimitsV1:
    result = build_admission_limits_v1(
        AdmissionLimitsV1(
            max_depth=64,
            max_nodes=200_000,
            max_canonical_bytes=4_000_000,
            max_collection_items=200_000,
        )
    )
    if type(result) is not ValidatedAdmissionLimitsV1:
        raise AssertionError("test admission limits must be valid")
    return result


def _state(*entries: tuple[tuple[str, str], int]) -> CommittedBalanceTableV1:
    admitted = admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        _limits(),
        _BalanceSourceV1({key: amount for key, amount in entries}),
    )
    if type(admitted) is not AdmitOk:
        raise AssertionError(f"test balance state admission failed: {admitted!r}")
    if type(admitted.value) is not CommittedBalanceTableV1:
        raise AssertionError("test admission returned the wrong committed type")
    return admitted.value


def _built(*writes: BalanceWriteV1) -> CanonicalBalancePatchV1:
    result = build_canonical_balance_patch_v1(writes)
    if type(result) is not BalancePatchBuildOkV1:
        raise AssertionError(f"test patch construction failed: {result!r}")
    return result.patch


def test_patch_builder_canonicalizes_every_input_permutation() -> None:
    writes = (
        BalanceWriteV1(("carol", "asset-b"), 0, 9),
        BalanceWriteV1(("alice", "asset-a"), 7, 3),
        BalanceWriteV1(("bob", "asset-a"), 5, None),
    )

    built = tuple(_built(*ordering) for ordering in permutations(writes))

    assert all(candidate == built[0] for candidate in built)
    assert tuple(write.key for write in built[0].writes) == (
        ("alice", "asset-a"),
        ("bob", "asset-a"),
        ("carol", "asset-b"),
    )


def test_patch_builder_rejects_duplicate_cell_independent_of_input_order() -> None:
    left = BalanceWriteV1(("alice", "asset"), 5, 4)
    right = BalanceWriteV1(("alice", "asset"), 5, 3)

    results = tuple(
        build_canonical_balance_patch_v1(ordering) for ordering in ((left, right), (right, left))
    )

    assert all(type(result) is BalancePatchRejectV1 for result in results)
    assert {
        (cast(BalancePatchRejectV1, result).code, cast(BalancePatchRejectV1, result).path)
        for result in results
    } == {(BalancePatchCodeV1.DUPLICATE_WRITE, ("writes", "key", "alice", "asset"))}


def test_patch_builder_selects_noop_rejection_in_canonical_key_order() -> None:
    alice = BalanceWriteV1(("alice", "asset"), 4, 4)
    bob = BalanceWriteV1(("bob", "asset"), 0, None)

    results = tuple(
        build_canonical_balance_patch_v1(ordering) for ordering in ((alice, bob), (bob, alice))
    )

    assert results == (
        BalancePatchRejectV1(BalancePatchCodeV1.NO_OP_WRITE, ("writes", 0)),
        BalancePatchRejectV1(BalancePatchCodeV1.NO_OP_WRITE, ("writes", 0)),
    )


@pytest.mark.parametrize(
    "write",
    [
        BalanceWriteV1(("alice", "asset"), 0, None),
        BalanceWriteV1(("alice", "asset"), 4, 4),
    ],
)
def test_patch_builder_rejects_noncanonical_noop_write(write: BalanceWriteV1) -> None:
    result = build_canonical_balance_patch_v1((write,))

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.NO_OP_WRITE,
        ("writes", 0),
    )


def test_patch_builder_rejects_empty_patch() -> None:
    assert build_canonical_balance_patch_v1(()) == BalancePatchRejectV1(
        BalancePatchCodeV1.EMPTY_PATCH,
        ("writes",),
    )


def test_balance_write_constructor_rejects_inexact_and_noncanonical_fields() -> None:
    with pytest.raises(TypeError, match="exact nonnegative integer"):
        BalanceWriteV1(("alice", "asset"), True, 1)
    with pytest.raises(TypeError, match="positive integer or None"):
        BalanceWriteV1(("alice", "asset"), 0, 0)
    with pytest.raises(ValueError, match="nonempty"):
        BalanceWriteV1(("", "asset"), 0, 1)
    with pytest.raises(ValueError, match="Unicode scalar"):
        BalanceWriteV1(("\ud800", "asset"), 0, 1)


def test_apply_two_cell_patch_is_atomic_and_preserves_prestate() -> None:
    pre = _state((("alice", "asset"), 10), (("bob", "asset"), 2))
    before = pre.entries
    patch = _built(
        BalanceWriteV1(("bob", "asset"), 2, 6),
        BalanceWriteV1(("alice", "asset"), 10, 6),
    )

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert type(result) is BalancePatchApplyOkV1
    assert result.state is not pre
    assert pre.entries == before
    assert result.state.entries == (
        (("alice", "asset"), 6),
        (("bob", "asset"), 6),
    )
    assert sum(value for _key, value in result.state.entries) == sum(
        value for _key, value in pre.entries
    )


def test_apply_expected_old_mismatch_returns_no_candidate() -> None:
    pre = _state((("alice", "asset"), 10), (("bob", "asset"), 2))
    before = pre.entries
    patch = _built(
        BalanceWriteV1(("alice", "asset"), 10, 6),
        BalanceWriteV1(("bob", "asset"), 999, 6),
    )

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.EXPECTED_OLD_MISMATCH,
        ("writes", 1, "expected_old"),
    )
    assert not hasattr(result, "state")
    assert pre.entries == before


def test_apply_delete_and_insert_returns_one_canonical_sparse_state() -> None:
    pre = _state((("bob", "asset"), 3), (("carol", "asset"), 8))
    patch = _built(
        BalanceWriteV1(("alice", "asset"), 0, 5),
        BalanceWriteV1(("carol", "asset"), 8, None),
    )

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert type(result) is BalancePatchApplyOkV1
    assert result.state.entries == (
        (("alice", "asset"), 5),
        (("bob", "asset"), 3),
    )


def test_apply_revalidates_corrupted_patch_before_reading_writes() -> None:
    pre = _state((("alice", "asset"), 4))
    patch = _built(BalanceWriteV1(("alice", "asset"), 4, 3))
    object.__setattr__(patch, "writes", ("malformed",))

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.NONCANONICAL_PATCH,
        ("writes", 0),
    )
    assert pre.entries == ((("alice", "asset"), 4),)


def test_apply_rejects_behavior_compatible_patch_subclass() -> None:
    patch_subclass = type("_PatchSubclass", (CanonicalBalancePatchV1,), {})
    exact_patch = _built(BalanceWriteV1(("alice", "asset"), 0, 3))
    subclass = patch_subclass(exact_patch.writes)

    result = apply_canonical_balance_patch_v1(
        _state(),
        cast(CanonicalBalancePatchV1, subclass),
    )

    assert result == BalancePatchRejectV1(BalancePatchCodeV1.WRONG_EXACT_TYPE, ())


def test_apply_revalidates_corrupted_committed_prestate() -> None:
    pre = _state((("alice", "asset"), 4))
    owned_map = object.__getattribute__(pre, "_balances")
    object.__setattr__(owned_map, "_entries", ((("alice", "asset"), True),))
    patch = _built(BalanceWriteV1(("alice", "asset"), 4, 3))

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.INVALID_PRESTATE,
        ("state", "balances", 0, "value"),
    )


def test_apply_rejects_corrupt_index_without_invoking_hostile_equality() -> None:
    class _HostileIndexValue:
        def __hash__(self) -> int:
            return 0

        def __eq__(self, _other: object) -> bool:
            raise AssertionError("corrupt index equality must not execute")

    pre = _state((("alice", "asset"), 4))
    owned_map = object.__getattribute__(pre, "_balances")
    hostile = _HostileIndexValue()
    object.__setattr__(owned_map, "_index", MappingProxyType({hostile: hostile}))
    patch = _built(BalanceWriteV1(("alice", "asset"), 4, 3))

    result = apply_canonical_balance_patch_v1(pre, patch)

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.INVALID_PRESTATE,
        ("state", "balances", "index"),
    )


def test_patch_constructor_rejects_noncanonical_direct_order() -> None:
    with pytest.raises(ValueError, match="canonical"):
        CanonicalBalancePatchV1(
            (
                BalanceWriteV1(("bob", "asset"), 0, 2),
                BalanceWriteV1(("alice", "asset"), 0, 1),
            )
        )


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=0, max_value=20),
        values=st.integers(min_value=1, max_value=1_000_000),
        max_size=10,
    ),
    patch_cells=st.sets(
        st.integers(min_value=0, max_value=20),
        min_size=1,
        max_size=10,
    ),
)
def test_patch_application_matches_logical_map_reference(
    pre_values: dict[int, int],
    patch_cells: set[int],
) -> None:
    def key(cell: int) -> tuple[str, str]:
        return (f"account-{cell:02d}", "asset")

    pre = _state(*((key(cell), amount) for cell, amount in pre_values.items()))
    before = pre.entries
    writes: list[BalanceWriteV1] = []
    expected_reference = {entry_key: amount for entry_key, amount in pre.entries}
    for cell in sorted(patch_cells, reverse=True):
        cell_key = key(cell)
        current = expected_reference.get(cell_key, 0)
        replacement = None if current > 0 and cell % 3 == 0 else current + cell + 1
        writes.append(BalanceWriteV1(cell_key, current, replacement))
        if replacement is None:
            expected_reference.pop(cell_key)
        else:
            expected_reference[cell_key] = replacement

    patch_result = build_canonical_balance_patch_v1(tuple(writes))
    assert type(patch_result) is BalancePatchBuildOkV1
    apply_result = apply_canonical_balance_patch_v1(pre, patch_result.patch)

    assert type(apply_result) is BalancePatchApplyOkV1
    assert apply_result.state.entries == tuple(sorted(expected_reference.items()))
    assert pre.entries == before


def test_delta_reduction_is_permutation_invariant_and_aggregates_duplicate_keys() -> None:
    pre = _state((("alice", "asset"), 10), (("bob", "asset"), 5))
    deltas = (
        BalanceDeltaV1(("alice", "asset"), -3),
        BalanceDeltaV1(("bob", "asset"), 4),
        BalanceDeltaV1(("alice", "asset"), 1),
    )

    results = tuple(apply_balance_deltas_v1(pre, order) for order in permutations(deltas))

    assert all(type(result) is BalancePatchApplyOkV1 for result in results)
    assert {
        cast(BalancePatchApplyOkV1, result).state.entries for result in results
    } == {((('alice', 'asset'), 8), (('bob', 'asset'), 9))}
    assert pre.entries == ((('alice', 'asset'), 10), (('bob', 'asset'), 5))


def test_delta_reduction_cancellation_returns_validated_prestate_without_patch() -> None:
    pre = _state((("alice", "asset"), 10))
    result = apply_balance_deltas_v1(
        pre,
        (
            BalanceDeltaV1(("alice", "asset"), 5),
            BalanceDeltaV1(("alice", "asset"), -5),
        ),
    )

    assert result == BalancePatchApplyOkV1(pre)
    assert result.state is pre


def test_delta_reduction_rejects_negative_successor_without_candidate() -> None:
    pre = _state((("alice", "asset"), 3))

    result = apply_balance_deltas_v1(
        pre,
        (BalanceDeltaV1(("alice", "asset"), -4),),
    )

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.OUT_OF_RANGE,
        ("deltas", "net_delta"),
    )
    assert pre.entries == ((('alice', 'asset'), 3),)


def test_delta_reduction_enforces_aggregate_work_byte_budget_before_reduction() -> None:
    pre = _state()
    oversized = 1 << (MAX_CANONICAL_BYTES_V1 * 8)

    result = apply_balance_deltas_v1(
        pre,
        (BalanceDeltaV1(("alice", "asset"), oversized),),
    )

    assert result == BalancePatchRejectV1(
        BalancePatchCodeV1.BYTE_LIMIT,
        ("deltas",),
    )


@pytest.mark.parametrize("net_delta", [True, 0])
def test_balance_delta_constructor_rejects_inexact_or_zero_amount(net_delta: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        BalanceDeltaV1(("alice", "asset"), net_delta)  # type: ignore[arg-type]


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=0, max_value=10),
        values=st.integers(min_value=1, max_value=1_000),
        max_size=8,
    ),
    raw_deltas=st.lists(
        st.tuples(
            st.integers(min_value=0, max_value=10),
            st.integers(min_value=-100, max_value=100).filter(lambda value: value != 0),
        ),
        max_size=20,
    ),
)
def test_delta_reduction_matches_exact_logical_map_reference(
    pre_values: dict[int, int],
    raw_deltas: list[tuple[int, int]],
) -> None:
    def key(cell: int) -> tuple[str, str]:
        return (f"account-{cell:02d}", "asset")

    pre = _state(*((key(cell), amount) for cell, amount in pre_values.items()))
    deltas = tuple(BalanceDeltaV1(key(cell), amount) for cell, amount in raw_deltas)
    aggregate: dict[tuple[str, str], int] = {}
    for cell, amount in raw_deltas:
        cell_key = key(cell)
        aggregate[cell_key] = aggregate.get(cell_key, 0) + amount
    expected = {key(cell): amount for cell, amount in pre_values.items()}
    invalid = any(expected.get(cell_key, 0) + net < 0 for cell_key, net in aggregate.items())

    forward = apply_balance_deltas_v1(pre, deltas)
    reverse = apply_balance_deltas_v1(pre, tuple(reversed(deltas)))

    if invalid:
        expected_reject = BalancePatchRejectV1(
            BalancePatchCodeV1.OUT_OF_RANGE,
            ("deltas", "net_delta"),
        )
        assert forward == reverse == expected_reject
        return

    for cell_key, net in aggregate.items():
        replacement = expected.get(cell_key, 0) + net
        if replacement == 0:
            expected.pop(cell_key, None)
        else:
            expected[cell_key] = replacement
    assert type(forward) is BalancePatchApplyOkV1
    assert type(reverse) is BalancePatchApplyOkV1
    expected_entries = tuple(sorted(expected.items()))
    assert forward.state.entries == reverse.state.entries == expected_entries
