"""Reconstruct one positive zUSD borrowing-fee occurrence from exact sources.

The request identity is verifier-owned by E01. The pre-state and principal are
hashed into the authenticated command projection, then the existing pure zUSD
Python core is replayed. Callers cannot supply the fee, post-state, debt delta,
or occurrence root.

This reference relation is research-only. It does not establish current-state
authority, balance issuance, fee allocation, atomic publication, or mounting.
"""

from __future__ import annotations

from typing import NamedTuple, cast
from weakref import WeakValueDictionary

from .fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    E01RequestIdentityV1,
    revalidate_request_identity_v1,
)
from .zusd import BPS_SCALE, MAX_AMOUNT_E8, ZUSDState
from .zusd_authenticated_borrow_fee_occurrence_kernel_v1 import (
    _derive_kernel_values_v1,
    _KernelValuesV1,
)
from .zusd_authenticated_borrow_fee_occurrence_roots_v1 import (
    _occurrence_root_from_values_v1,
    _occurrence_root_v1,
    _OccurrenceRootInputV1,
    _state_is_valid_v1,
    canonical_zusd_borrow_command_root_v1,
    canonical_zusd_state_root_v1,
)
from .zusd_authenticated_borrow_fee_occurrence_values_v1 import (
    MAX_BORROWER_ID_BYTES_V1,
    ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1,
    ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1,
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceResultV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
    _authenticated_borrow_fee_occurrence_v1,
    _OccurrenceConstructionV1,
)


class _AlignedSourceV1(NamedTuple):
    request_identity: E01RequestIdentityV1
    pre_state: ZUSDState
    principal_e8: int


def _reject_v1(
    code: ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
    *path: str,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    return ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1(code, tuple(path))


def _validated_source_v1(
    source: object,
) -> _AlignedSourceV1 | ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    if type(source) is not ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.WRONG_EXACT_TYPE,
            "source",
        )
    if not revalidate_request_identity_v1(source.request_identity):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_REQUEST_IDENTITY,
            "request_identity",
        )
    identity = cast(E01RequestIdentityV1, source.request_identity)
    if identity.command_family is not E01CommandFamilyV1.STATE_CHANGE:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.WRONG_COMMAND_FAMILY,
            "request_identity",
            "command_family",
        )
    if not _state_is_valid_v1(source.pre_state):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_PRE_STATE,
            "pre_state",
        )
    if type(source.principal_e8) is not int or not 1 <= source.principal_e8 <= MAX_AMOUNT_E8:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.INVALID_PRINCIPAL,
            "principal_e8",
        )
    pre_state = cast(ZUSDState, source.pre_state)
    expected_root = canonical_zusd_borrow_command_root_v1(
        borrower_id=identity.sender_id,
        principal_e8=source.principal_e8,
        pre_state=pre_state,
    )
    if identity.command_root != expected_root:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.COMMAND_ROOT_MISMATCH,
            "request_identity",
            "command_root",
        )
    return _AlignedSourceV1(identity, pre_state, source.principal_e8)


def _candidate_sources_valid_v1(value: ZUSDAuthenticatedBorrowFeeOccurrenceV1) -> bool:
    if not revalidate_request_identity_v1(value.request_identity):
        return False
    if value.request_identity.command_family is not E01CommandFamilyV1.STATE_CHANGE:
        return False
    if not _state_is_valid_v1(value.pre_state) or not _state_is_valid_v1(value.post_state):
        return False
    expected_root = canonical_zusd_borrow_command_root_v1(
        borrower_id=value.request_identity.sender_id,
        principal_e8=value.principal_e8,
        pre_state=value.pre_state,
    )
    return value.request_identity.command_root == expected_root


def _candidate_economics_valid_v1(value: ZUSDAuthenticatedBorrowFeeOccurrenceV1) -> bool:
    for field_value, minimum, maximum in (
        (value.principal_e8, 1, MAX_AMOUNT_E8),
        (value.fee_e8, 1, MAX_AMOUNT_E8),
        (value.fee_bps, 0, BPS_SCALE),
        (value.debt_delta_e8, 1, MAX_AMOUNT_E8),
    ):
        if type(field_value) is not int or not minimum <= field_value <= maximum:
            return False
    expected_fee = ((value.principal_e8 * value.fee_bps) + BPS_SCALE - 1) // BPS_SCALE
    return (
        value.debt_delta_e8 == value.principal_e8 + value.fee_e8
        and value.fee_e8 == expected_fee
        and value.post_state.debt_e8 - value.pre_state.debt_e8 == value.debt_delta_e8
        and value.post_state.free_debt_e8 - value.pre_state.free_debt_e8 == value.debt_delta_e8
        and value.post_state.protocol_revenue_zusd_cum_e8
        - value.pre_state.protocol_revenue_zusd_cum_e8
        == value.fee_e8
    )


def _validate_occurrence_fields_v1(value: ZUSDAuthenticatedBorrowFeeOccurrenceV1) -> None:
    if not _candidate_sources_valid_v1(value):
        raise ValueError("occurrence sources are invalid or crossed")
    if not _candidate_economics_valid_v1(value):
        raise ValueError("occurrence economic relation is invalid")
    if value.occurrence_root != _occurrence_root_v1(value):
        raise ValueError("occurrence root is not canonical")


_OCCURRENCES_V1: WeakValueDictionary[int, ZUSDAuthenticatedBorrowFeeOccurrenceV1] = (
    WeakValueDictionary()
)
_OCCURRENCE_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _occurrence_snapshot_v1(
    value: ZUSDAuthenticatedBorrowFeeOccurrenceV1,
) -> tuple[object, ...]:
    return (
        value.request_identity.request_identity_root,
        canonical_zusd_state_root_v1(value.pre_state),
        canonical_zusd_state_root_v1(value.post_state),
        value.principal_e8,
        value.fee_e8,
        value.fee_bps,
        value.debt_delta_e8,
        value.occurrence_root,
    )


def _register_occurrence_v1(
    value: ZUSDAuthenticatedBorrowFeeOccurrenceV1,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceV1:
    identity = id(value)
    _OCCURRENCES_V1[identity] = value
    _OCCURRENCE_SNAPSHOTS_V1[identity] = _occurrence_snapshot_v1(value)
    return value


def _construct_occurrence_v1(
    source: _AlignedSourceV1,
    kernel: _KernelValuesV1,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceV1:
    root_input = _OccurrenceRootInputV1(
        source.request_identity,
        source.pre_state,
        kernel.post_state,
        source.principal_e8,
        kernel.fee_e8,
        kernel.fee_bps,
        kernel.debt_delta_e8,
    )
    value = _authenticated_borrow_fee_occurrence_v1(
        _OccurrenceConstructionV1(
            source.request_identity,
            source.pre_state,
            kernel.post_state,
            source.principal_e8,
            kernel.fee_e8,
            kernel.fee_bps,
            kernel.debt_delta_e8,
            _occurrence_root_from_values_v1(root_input),
        )
    )
    _validate_occurrence_fields_v1(value)
    return value


def derive_zusd_authenticated_borrow_fee_occurrence_v1(
    source: object,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceResultV1:
    """Re-run the exact borrow transition and derive one positive fee occurrence."""

    aligned = _validated_source_v1(source)
    if type(aligned) is ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
        return aligned
    kernel = _derive_kernel_values_v1(
        pre_state=aligned.pre_state,
        principal_e8=aligned.principal_e8,
    )
    if type(kernel) is ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
        return kernel
    try:
        return _register_occurrence_v1(_construct_occurrence_v1(aligned, kernel))
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.MALFORMED_KERNEL_ACCEPT,
            "candidate",
        )


def revalidate_zusd_authenticated_borrow_fee_occurrence_v1(value: object) -> bool:
    """Re-run provenance, arithmetic, kernel replay, and snapshot checks."""

    if type(value) is not ZUSDAuthenticatedBorrowFeeOccurrenceV1:
        return False
    if _OCCURRENCES_V1.get(id(value)) is not value:
        return False
    try:
        _validate_occurrence_fields_v1(value)
        expected = derive_zusd_authenticated_borrow_fee_occurrence_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1(
                request_identity=value.request_identity,
                pre_state=value.pre_state,
                principal_e8=value.principal_e8,
            )
        )
        return (
            type(expected) is ZUSDAuthenticatedBorrowFeeOccurrenceV1
            and expected == value
            and _OCCURRENCE_SNAPSHOTS_V1.get(id(value)) == _occurrence_snapshot_v1(value)
        )
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return False


def verify_zusd_authenticated_borrow_fee_occurrence_v1(
    *,
    source: object,
    candidate: object,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceResultV1:
    """Independently rederive and require exact candidate equality."""

    expected = derive_zusd_authenticated_borrow_fee_occurrence_v1(source)
    if type(expected) is ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
        return expected
    if (
        type(candidate) is not ZUSDAuthenticatedBorrowFeeOccurrenceV1
        or not revalidate_zusd_authenticated_borrow_fee_occurrence_v1(candidate)
        or candidate != expected
    ):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.CANDIDATE_MISMATCH,
            "candidate",
        )
    return candidate


__all__ = (
    "MAX_BORROWER_ID_BYTES_V1",
    "ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1",
    "ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceResultV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceV1",
    "canonical_zusd_borrow_command_root_v1",
    "canonical_zusd_state_root_v1",
    "derive_zusd_authenticated_borrow_fee_occurrence_v1",
    "revalidate_zusd_authenticated_borrow_fee_occurrence_v1",
    "verify_zusd_authenticated_borrow_fee_occurrence_v1",
)
