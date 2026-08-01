"""Typed unmounted sign-dual transport for M6 entitlement states.

The C04 transport is the executable refinement of the coordinate relation
``sigma_i = -d_i``.  It operates on complete C03 states and optionally checks
an independently supplied target state.  The target is evidence to compare;
it is not an authority witness and this module has no runtime mounting path.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast, final

from .fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
)
from .fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)


class C04TransportCodeV1(Enum):
    """Fail-closed C04 rejection classes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_SOURCE_STATE = "invalid_source_state"
    INVALID_TARGET_STATE = "invalid_target_state"
    SOURCE_REPRESENTATION_MISMATCH = "source_representation_mismatch"
    TARGET_REPRESENTATION_MISMATCH = "target_representation_mismatch"
    KEY_MISMATCH = "key_mismatch"
    ENTRY_SET_MISMATCH = "entry_set_mismatch"
    COORDINATE_MISMATCH = "coordinate_mismatch"
    ZERO_RESET = "zero_reset"


@final
@dataclass(frozen=True, slots=True)
class C04TransportRejectV1:
    """Typed rejection for a sign-dual transport or equality check."""

    code: C04TransportCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not C04TransportCodeV1:
            raise TypeError("C04 transport reject code must be exact")
        if type(self.path) is not tuple or any(
            type(part) is not str for part in self.path
        ):
            raise TypeError("C04 transport reject path must be an exact tuple")


C04TransportResultV1: TypeAlias = EntitlementStateV1 | C04TransportRejectV1


def _reject(
    code: C04TransportCodeV1,
    *path: str,
) -> C04TransportRejectV1:
    return C04TransportRejectV1(code, path)


def _validated_state(
    value: object,
    *,
    path: str,
    invalid_code: C04TransportCodeV1,
) -> EntitlementStateV1 | C04TransportRejectV1:
    if type(value) is not EntitlementStateV1:
        return _reject(C04TransportCodeV1.WRONG_EXACT_TYPE, path)
    state = cast(EntitlementStateV1, value)
    try:
        state.__post_init__()
    except (TypeError, ValueError):
        return _reject(invalid_code, path)
    return state


def _transport_state_v1(
    source: object,
    *,
    source_representation: str,
    target_representation: str,
    expected_target: object | None,
) -> C04TransportResultV1:
    source_result = _validated_state(
        source,
        path="source_state",
        invalid_code=C04TransportCodeV1.INVALID_SOURCE_STATE,
    )
    if type(source_result) is C04TransportRejectV1:
        return source_result
    source_state = source_result
    if source_state.representation_id != source_representation:
        return _reject(
            C04TransportCodeV1.SOURCE_REPRESENTATION_MISMATCH,
            "source_state",
            "representation_id",
        )

    if expected_target is None:
        target_state = EntitlementStateV1(
            source_state.key,
            target_representation,
            tuple(
                EntitlementStateEntryV1(
                    entry.entry_id,
                    tuple(-coordinate for coordinate in entry.coordinates),
                )
                for entry in source_state.entries
            ),
        )
        return target_state

    target_result = _validated_state(
        expected_target,
        path="expected_target",
        invalid_code=C04TransportCodeV1.INVALID_TARGET_STATE,
    )
    if type(target_result) is C04TransportRejectV1:
        return target_result
    target_state = target_result
    if target_state.representation_id != target_representation:
        return _reject(
            C04TransportCodeV1.TARGET_REPRESENTATION_MISMATCH,
            "expected_target",
            "representation_id",
        )
    if target_state.key != source_state.key:
        return _reject(C04TransportCodeV1.KEY_MISMATCH, "expected_target", "key")

    source_entry_ids = tuple(entry.entry_id for entry in source_state.entries)
    target_entry_ids = tuple(entry.entry_id for entry in target_state.entries)
    if target_entry_ids != source_entry_ids:
        return _reject(
            C04TransportCodeV1.ENTRY_SET_MISMATCH,
            "expected_target",
            "entries",
        )

    for index, (source_entry, target_entry) in enumerate(
        zip(source_state.entries, target_state.entries, strict=True)
    ):
        expected_coordinates = tuple(-x for x in source_entry.coordinates)
        if target_entry.coordinates != expected_coordinates:
            if (
                any(coordinate != 0 for coordinate in source_entry.coordinates)
                and all(coordinate == 0 for coordinate in target_entry.coordinates)
            ):
                return _reject(
                    C04TransportCodeV1.ZERO_RESET,
                    "expected_target",
                    "entries",
                    str(index),
                    "coordinates",
                )
            return _reject(
                C04TransportCodeV1.COORDINATE_MISMATCH,
                "expected_target",
                "entries",
                str(index),
                "coordinates",
            )
    return target_state


def transport_srgd_to_agqe_v1(
    source: object,
    *,
    expected_target: object | None = None,
) -> C04TransportResultV1:
    """Negate every complete SRGD coordinate into an AGQE state.

    When ``expected_target`` is supplied, the function returns that exact
    target only after key, representation, ordered entry identity, and every
    coordinate satisfy the transport relation.  Without a target it returns a
    deterministically derived candidate state for research comparison.
    """

    return _transport_state_v1(
        source,
        source_representation=SRGD_REPRESENTATION_PROFILE_ID_V1,
        target_representation=AGQE_REPRESENTATION_PROFILE_ID_V1,
        expected_target=expected_target,
    )


def transport_agqe_to_srgd_v1(
    source: object,
    *,
    expected_target: object | None = None,
) -> C04TransportResultV1:
    """Apply the inverse sign-dual map from AGQE back to SRGD."""

    return _transport_state_v1(
        source,
        source_representation=AGQE_REPRESENTATION_PROFILE_ID_V1,
        target_representation=SRGD_REPRESENTATION_PROFILE_ID_V1,
        expected_target=expected_target,
    )


__all__: Final[tuple[str, ...]] = (
    "C04TransportCodeV1",
    "C04TransportRejectV1",
    "C04TransportResultV1",
    "transport_agqe_to_srgd_v1",
    "transport_srgd_to_agqe_v1",
)
