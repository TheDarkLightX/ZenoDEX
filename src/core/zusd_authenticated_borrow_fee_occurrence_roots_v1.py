"""Canonical state, command, and occurrence roots for authenticated zUSD fees."""

from __future__ import annotations

from hashlib import sha256
from typing import NamedTuple, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_m6_e01_request_identity import E01RequestIdentityV1
from .zusd import MAX_AMOUNT_E8, ZUSD_STATE_FIELD_ORDER, ZUSDState, _state_root
from .zusd_authenticated_borrow_fee_occurrence_values_v1 import (
    MAX_BORROWER_ID_BYTES_V1,
    ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1,
    ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1,
    ZUSDAuthenticatedBorrowFeeOccurrenceV1,
)

_LOWER_HEX = frozenset("0123456789abcdef")


class _OccurrenceRootInputV1(NamedTuple):
    request_identity: E01RequestIdentityV1
    pre_state: ZUSDState
    post_state: ZUSDState
    principal_e8: int
    fee_e8: int
    fee_bps: int
    debt_delta_e8: int


def _text(value: object, name: str, *, maximum_bytes: int) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > maximum_bytes:
        raise ValueError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise ValueError(f"{name} contains a control character")
    return value


def _state_is_valid_v1(value: object) -> bool:
    if type(value) is not ZUSDState:
        return False
    state = cast(ZUSDState, value)
    try:
        for name in ZUSD_STATE_FIELD_ORDER:
            field_value = getattr(state, name)
            if name == "oracle_seen":
                if type(field_value) is not bool:
                    return False
            elif type(field_value) is not int:
                return False
        state.__post_init__()
        state_root = _state_root(state)
        return (
            type(state_root) is str
            and len(state_root) == 66
            and state_root.startswith("0x")
            and all(character in _LOWER_HEX for character in state_root[2:])
        )
    except (TypeError, ValueError, AttributeError, ArithmeticError, OverflowError):
        return False


def canonical_zusd_state_root_v1(state: ZUSDState) -> str:
    """Return the existing zUSD V1 root after exact-type state validation."""

    if not _state_is_valid_v1(state):
        raise TypeError("zUSD state is outside the exact canonical language")
    return cast(str, _state_root(state))


def canonical_zusd_borrow_command_root_v1(
    *,
    borrower_id: object,
    principal_e8: object,
    pre_state: object,
) -> str:
    """Hash the exact authenticated borrow projection used by this relation."""

    checked_borrower = _text(
        borrower_id,
        "borrower identifier",
        maximum_bytes=MAX_BORROWER_ID_BYTES_V1,
    )
    if type(principal_e8) is not int or not 1 <= principal_e8 <= MAX_AMOUNT_E8:
        raise TypeError("principal_e8 must be an exact positive bounded integer")
    if not _state_is_valid_v1(pre_state):
        raise TypeError("pre-state is outside the exact zUSD state language")
    body = {
        "schema": ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1,
        "action": "mint_zusd",
        "borrower_id": checked_borrower,
        "principal_e8": principal_e8,
        "pre_state_root": canonical_zusd_state_root_v1(pre_state),
    }
    return sha256(
        ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1.encode("ascii")
        + b"\x00"
        + canonical_json_bytes(body)
    ).hexdigest()


def _occurrence_root_from_values_v1(value: _OccurrenceRootInputV1) -> str:
    body = {
        "schema": ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1,
        "request_identity_root": value.request_identity.request_identity_root,
        "command_root": value.request_identity.command_root,
        "borrower_id": value.request_identity.sender_id,
        "pre_state_root": canonical_zusd_state_root_v1(value.pre_state),
        "post_state_root": canonical_zusd_state_root_v1(value.post_state),
        "principal_e8": value.principal_e8,
        "fee_e8": value.fee_e8,
        "fee_bps": value.fee_bps,
        "debt_delta_e8": value.debt_delta_e8,
    }
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zusd_authenticated_borrow_fee_occurrence", version=1)
            + canonical_json_bytes(body)
        ),
    )


def _occurrence_root_v1(value: ZUSDAuthenticatedBorrowFeeOccurrenceV1) -> str:
    return _occurrence_root_from_values_v1(
        _OccurrenceRootInputV1(
            value.request_identity,
            value.pre_state,
            value.post_state,
            value.principal_e8,
            value.fee_e8,
            value.fee_bps,
            value.debt_delta_e8,
        )
    )


__all__ = ("canonical_zusd_borrow_command_root_v1", "canonical_zusd_state_root_v1")
