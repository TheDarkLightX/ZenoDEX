"""C04 exact sign-dual transport and rejection witnesses."""
from __future__ import annotations

import pytest

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
)
from src.core.fcis_entitlement_transport_v1 import (
    C04TransportCodeV1,
    C04TransportRejectV1,
    transport_agqe_to_srgd_v1,
    transport_srgd_to_agqe_v1,
)
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)


def _key(asset: str = "USDC") -> EntitlementKeyV1:
    return EntitlementKeyV1(
        "protocol-fees",
        asset,
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        FIXED_ROLE_ORDER_ID_V1,
    )


def _source_state() -> EntitlementStateV1:
    return EntitlementStateV1(
        _key(),
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        (
            EntitlementStateEntryV1("entry-0", (3, -1, -2)),
            EntitlementStateEntryV1("entry-1", (-4, 2, 2)),
        ),
    )


def _target_state(
    *,
    key: EntitlementKeyV1 | None = None,
    entries: tuple[EntitlementStateEntryV1, ...] | None = None,
    representation_id: str = AGQE_REPRESENTATION_PROFILE_ID_V1,
) -> EntitlementStateV1:
    return EntitlementStateV1(
        _key() if key is None else key,
        representation_id,
        (
            EntitlementStateEntryV1("entry-0", (-3, 1, 2)),
            EntitlementStateEntryV1("entry-1", (4, -2, -2)),
        )
        if entries is None
        else entries,
    )


def test_transport_negates_every_complete_entry_and_preserves_identity() -> None:
    source = _source_state()
    result = transport_srgd_to_agqe_v1(source)
    assert isinstance(result, EntitlementStateV1)
    assert result.key == source.key
    assert result.representation_id == AGQE_REPRESENTATION_PROFILE_ID_V1
    assert result.entries == _target_state().entries


def test_transport_is_involutive_on_complete_states() -> None:
    source = _source_state()
    target = transport_srgd_to_agqe_v1(source)
    assert isinstance(target, EntitlementStateV1)
    round_trip = transport_agqe_to_srgd_v1(target)
    assert round_trip == source
    checked = transport_srgd_to_agqe_v1(source, expected_target=target)
    assert checked == target


def test_expected_target_requires_complete_entry_identity_and_coordinates() -> None:
    source = _source_state()
    missing = _target_state(entries=(_target_state().entries[0],))
    assert transport_srgd_to_agqe_v1(source, expected_target=missing) == (
        C04TransportRejectV1(
            C04TransportCodeV1.ENTRY_SET_MISMATCH,
            ("expected_target", "entries"),
        )
    )

    surplus = _target_state(
        entries=(
            *_target_state().entries,
            EntitlementStateEntryV1("entry-2", (2, -1, -1)),
        )
    )
    assert transport_srgd_to_agqe_v1(source, expected_target=surplus) == (
        C04TransportRejectV1(
            C04TransportCodeV1.ENTRY_SET_MISMATCH,
            ("expected_target", "entries"),
        )
    )

    changed = _target_state(
        entries=(
            EntitlementStateEntryV1("entry-0", (-2, 0, 2)),
            _target_state().entries[1],
        )
    )
    assert transport_srgd_to_agqe_v1(source, expected_target=changed) == (
        C04TransportRejectV1(
            C04TransportCodeV1.COORDINATE_MISMATCH,
            ("expected_target", "entries", "0", "coordinates"),
        )
    )


def test_zero_initialized_target_is_rejected_as_history_reset() -> None:
    source = _source_state()
    zero_target = _target_state(
        entries=(
            EntitlementStateEntryV1("entry-0", (0, 0, 0)),
            EntitlementStateEntryV1("entry-1", (0, 0, 0)),
        )
    )
    assert transport_srgd_to_agqe_v1(source, expected_target=zero_target) == (
        C04TransportRejectV1(
            C04TransportCodeV1.ZERO_RESET,
            ("expected_target", "entries", "0", "coordinates"),
        )
    )


def test_semantic_key_and_fixed_role_order_are_preserved() -> None:
    source = _source_state()
    wrong_key = _target_state(key=_key("BTC"))
    assert transport_srgd_to_agqe_v1(source, expected_target=wrong_key) == (
        C04TransportRejectV1(
            C04TransportCodeV1.KEY_MISMATCH,
            ("expected_target", "key"),
        )
    )
    wrong_representation = _target_state(
        representation_id=SRGD_REPRESENTATION_PROFILE_ID_V1,
    )
    assert transport_srgd_to_agqe_v1(
        source,
        expected_target=wrong_representation,
    ) == C04TransportRejectV1(
        C04TransportCodeV1.TARGET_REPRESENTATION_MISMATCH,
        ("expected_target", "representation_id"),
    )


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    "source, expected_code",
    [
        (object(), C04TransportCodeV1.WRONG_EXACT_TYPE),
        (_target_state(), C04TransportCodeV1.SOURCE_REPRESENTATION_MISMATCH),
    ],
)
def test_invalid_source_is_fail_closed(
    source: object,
    expected_code: C04TransportCodeV1,
) -> None:
    result = transport_srgd_to_agqe_v1(source)
    assert isinstance(result, C04TransportRejectV1)
    assert result.code is expected_code


def test_invalid_target_type_is_fail_closed() -> None:
    result = transport_srgd_to_agqe_v1(_source_state(), expected_target=object())
    assert result == C04TransportRejectV1(
        C04TransportCodeV1.WRONG_EXACT_TYPE,
        ("expected_target",),
    )


def test_empty_state_transport_does_not_invent_entries() -> None:
    source = EntitlementStateV1(
        _key(),
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        (),
    )
    target = transport_srgd_to_agqe_v1(source)
    assert target == EntitlementStateV1(
        source.key,
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        (),
    )
