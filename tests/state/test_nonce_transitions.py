from __future__ import annotations

from itertools import permutations
from types import MappingProxyType
from typing import cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.state.nonces import NonceTable
from src.state.state_snapshot_values import MAX_U32_V1, CommittedNonceTableV1
from src.state.state_snapshots import snapshot_nonce_table
from src.state.state_transitions import (
    CanonicalNoncePatchV1,
    NonceAdvanceV1,
    NoncePatchApplyOkV1,
    NoncePatchBuildOkV1,
    NoncePatchCodeV1,
    NoncePatchRejectV1,
    apply_canonical_nonce_patch_v1,
    build_canonical_nonce_patch_v1,
)


def _pubkey(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 48


def _state(*entries: tuple[str, int]) -> CommittedNonceTableV1:
    source = NonceTable()
    for pubkey, nonce in entries:
        source.set_last(pubkey, nonce)
    return snapshot_nonce_table(source)


def _patch(*advances: NonceAdvanceV1) -> CanonicalNoncePatchV1:
    result = build_canonical_nonce_patch_v1(advances)
    if type(result) is not NoncePatchBuildOkV1:
        raise AssertionError(f"test nonce patch construction failed: {result!r}")
    return result.patch


def test_nonce_patch_builder_is_permutation_invariant() -> None:
    advances = (
        NonceAdvanceV1(_pubkey(3), 0, 1),
        NonceAdvanceV1(_pubkey(1), 4, 6),
        NonceAdvanceV1(_pubkey(2), 9, 10),
    )

    built = tuple(_patch(*ordering) for ordering in permutations(advances))

    assert all(candidate == built[0] for candidate in built)
    assert tuple(advance.pubkey for advance in built[0].advances) == (
        _pubkey(1),
        _pubkey(2),
        _pubkey(3),
    )


def test_nonce_patch_builder_rejects_duplicate_sender_independent_of_order() -> None:
    left = NonceAdvanceV1(_pubkey(1), 3, 4)
    right = NonceAdvanceV1(_pubkey(1), 3, 5)

    results = tuple(
        build_canonical_nonce_patch_v1(ordering) for ordering in ((left, right), (right, left))
    )

    assert results == (
        NoncePatchRejectV1(
            NoncePatchCodeV1.DUPLICATE_ADVANCE,
            ("advances", "pubkey", _pubkey(1)),
        ),
        NoncePatchRejectV1(
            NoncePatchCodeV1.DUPLICATE_ADVANCE,
            ("advances", "pubkey", _pubkey(1)),
        ),
    )


def test_nonce_advance_constructor_enforces_exact_canonical_monotone_u32() -> None:
    with pytest.raises(TypeError, match="expected_last"):
        NonceAdvanceV1(_pubkey(1), True, 2)
    with pytest.raises(TypeError, match="new_last"):
        NonceAdvanceV1(_pubkey(1), 0, MAX_U32_V1 + 1)
    with pytest.raises(ValueError, match="strictly advance"):
        NonceAdvanceV1(_pubkey(1), 2, 2)
    with pytest.raises(ValueError, match="canonical fixed-width hex"):
        NonceAdvanceV1(_pubkey(0xAB).upper().replace("0X", "0x"), 0, 1)

    assert NonceAdvanceV1(_pubkey(1), MAX_U32_V1 - 1, MAX_U32_V1).new_last == MAX_U32_V1


def test_apply_nonce_patch_updates_existing_and_new_senders_without_mutating_prestate() -> None:
    pre = _state((_pubkey(1), 4), (_pubkey(2), 0))
    before = pre.entries
    patch = _patch(
        NonceAdvanceV1(_pubkey(3), 0, 1),
        NonceAdvanceV1(_pubkey(1), 4, 6),
        NonceAdvanceV1(_pubkey(2), 0, 2),
    )

    result = apply_canonical_nonce_patch_v1(pre, patch)

    assert type(result) is NoncePatchApplyOkV1
    assert result.patch is patch
    assert result.state is not pre
    assert result.state.entries == (
        (_pubkey(1), 6),
        (_pubkey(2), 2),
        (_pubkey(3), 1),
    )
    assert pre.entries == before


def test_nonce_expected_old_mismatch_rejects_without_candidate() -> None:
    pre = _state((_pubkey(1), 4), (_pubkey(2), 8))
    patch = _patch(
        NonceAdvanceV1(_pubkey(1), 4, 5),
        NonceAdvanceV1(_pubkey(2), 7, 9),
    )

    result = apply_canonical_nonce_patch_v1(pre, patch)

    assert result == NoncePatchRejectV1(
        NoncePatchCodeV1.EXPECTED_OLD_MISMATCH,
        ("advances", 1, "expected_last"),
    )
    assert not hasattr(result, "state")
    assert pre.entries == ((_pubkey(1), 4), (_pubkey(2), 8))


def test_nonce_patch_application_revalidates_patch_and_committed_prestate() -> None:
    pre = _state((_pubkey(1), 4))
    patch = _patch(NonceAdvanceV1(_pubkey(1), 4, 5))
    object.__setattr__(patch, "advances", ("corrupt",))

    assert apply_canonical_nonce_patch_v1(pre, patch) == NoncePatchRejectV1(
        NoncePatchCodeV1.NONCANONICAL_PATCH,
        ("advances", 0),
    )

    fresh_patch = _patch(NonceAdvanceV1(_pubkey(1), 4, 5))
    owned_map = object.__getattribute__(pre, "_last")
    object.__setattr__(owned_map, "_entries", ((_pubkey(1), True),))
    assert apply_canonical_nonce_patch_v1(pre, fresh_patch) == NoncePatchRejectV1(
        NoncePatchCodeV1.INVALID_PRESTATE,
        ("state", "nonces", 0, "nonce"),
    )


def test_nonce_patch_builder_rejects_corrupted_boolean_as_wrong_exact_type() -> None:
    advance = NonceAdvanceV1(_pubkey(1), 4, 5)
    object.__setattr__(advance, "new_last", True)

    assert build_canonical_nonce_patch_v1((advance,)) == NoncePatchRejectV1(
        NoncePatchCodeV1.WRONG_EXACT_TYPE,
        ("advances", 0, "new_last"),
    )


def test_nonce_patch_rejects_behavior_compatible_subclass_and_corrupt_index() -> None:
    pre = _state((_pubkey(1), 4))
    patch = _patch(NonceAdvanceV1(_pubkey(1), 4, 5))
    patch_subclass = type("_NoncePatchSubclass", (CanonicalNoncePatchV1,), {})
    subclass = patch_subclass(patch.advances)

    assert apply_canonical_nonce_patch_v1(
        pre,
        cast(CanonicalNoncePatchV1, subclass),
    ) == NoncePatchRejectV1(NoncePatchCodeV1.WRONG_EXACT_TYPE, ())

    owned_map = object.__getattribute__(pre, "_last")
    object.__setattr__(owned_map, "_index", MappingProxyType({_pubkey(1): 999}))
    assert apply_canonical_nonce_patch_v1(pre, patch) == NoncePatchRejectV1(
        NoncePatchCodeV1.INVALID_PRESTATE,
        ("state", "nonces", "index"),
    )


@settings(max_examples=100, deadline=None)
@given(
    pre_values=st.dictionaries(
        keys=st.integers(min_value=1, max_value=12),
        values=st.integers(min_value=0, max_value=1_000),
        max_size=8,
    ),
    advance_by=st.dictionaries(
        keys=st.integers(min_value=1, max_value=12),
        values=st.integers(min_value=1, max_value=20),
        min_size=1,
        max_size=8,
    ),
)
def test_nonce_patch_matches_logical_map_and_legacy_reference(
    pre_values: dict[int, int],
    advance_by: dict[int, int],
) -> None:
    pre = _state(*((_pubkey(sender), nonce) for sender, nonce in pre_values.items()))
    before = pre.entries
    advances = tuple(
        NonceAdvanceV1(
            _pubkey(sender),
            pre_values.get(sender, 0),
            pre_values.get(sender, 0) + delta,
        )
        for sender, delta in advance_by.items()
    )
    patch_result = build_canonical_nonce_patch_v1(advances)
    assert type(patch_result) is NoncePatchBuildOkV1

    result = apply_canonical_nonce_patch_v1(pre, patch_result.patch)

    assert type(result) is NoncePatchApplyOkV1
    expected = dict(pre.entries)
    legacy = NonceTable()
    for pubkey, nonce in pre.entries:
        legacy.set_last(pubkey, nonce)
    for advance in advances:
        expected[advance.pubkey] = advance.new_last
        legacy.set_last(advance.pubkey, advance.new_last)
    assert result.state.entries == tuple(sorted(expected.items()))
    assert result.state.entries == tuple(sorted(legacy.get_all().items()))
    assert pre.entries == before
