"""Closed values for one authenticated positive zUSD borrowing-fee occurrence."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, NamedTuple, TypeAlias, final

from .fcis_m6_e01_request_identity import E01RequestIdentityV1
from .zusd import BPS_SCALE, MAX_AMOUNT_E8, ZUSDState

ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1: Final = "zenodex/zusd/authenticated-borrow-command/v1"
ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1: Final = (
    "zenodex/zusd/authenticated-borrow-fee-occurrence/v1"
)
MAX_BORROWER_ID_BYTES_V1: Final = 128

_OCCURRENCE_TOKEN_V1 = object()
_LOWER_HEX = frozenset("0123456789abcdef")


class ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_REQUEST_IDENTITY = "invalid_request_identity"
    WRONG_COMMAND_FAMILY = "wrong_command_family"
    INVALID_PRE_STATE = "invalid_pre_state"
    INVALID_PRINCIPAL = "invalid_principal"
    COMMAND_ROOT_MISMATCH = "command_root_mismatch"
    KERNEL_REJECTED = "kernel_rejected"
    MALFORMED_KERNEL_ACCEPT = "malformed_kernel_accept"
    ZERO_FEE = "zero_fee"
    ECONOMIC_DELTA_MISMATCH = "economic_delta_mismatch"
    CANDIDATE_MISMATCH = "candidate_mismatch"


@final
@dataclass(frozen=True, slots=True)
class ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1:
    request_identity: object
    pre_state: object
    principal_e8: object


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class ZUSDAuthenticatedBorrowFeeOccurrenceV1:
    request_identity: E01RequestIdentityV1
    pre_state: ZUSDState
    post_state: ZUSDState
    principal_e8: int
    fee_e8: int
    fee_bps: int
    debt_delta_e8: int
    occurrence_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _OCCURRENCE_TOKEN_V1:
            raise TypeError("authenticated borrow-fee occurrence requires replay")
        if type(self.request_identity) is not E01RequestIdentityV1:
            raise TypeError("request identity must be exact")
        if type(self.pre_state) is not ZUSDState or type(self.post_state) is not ZUSDState:
            raise TypeError("occurrence states must be exact")
        for name, value, minimum, maximum in (
            ("principal_e8", self.principal_e8, 1, MAX_AMOUNT_E8),
            ("fee_e8", self.fee_e8, 1, MAX_AMOUNT_E8),
            ("fee_bps", self.fee_bps, 0, BPS_SCALE),
            ("debt_delta_e8", self.debt_delta_e8, 1, MAX_AMOUNT_E8),
        ):
            if type(value) is not int or not minimum <= value <= maximum:
                raise TypeError(f"{name} is outside its exact bound")
        if (
            type(self.occurrence_root) is not str
            or len(self.occurrence_root) != 66
            or not self.occurrence_root.startswith("0x")
            or any(character not in _LOWER_HEX for character in self.occurrence_root[2:])
        ):
            raise TypeError("occurrence root must be a canonical 0x-prefixed SHA-256 digest")


@final
@dataclass(frozen=True, slots=True)
class ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    code: ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1:
            raise TypeError("borrow-fee occurrence rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("borrow-fee occurrence rejection path must be exact")


ZUSDAuthenticatedBorrowFeeOccurrenceResultV1: TypeAlias = (
    ZUSDAuthenticatedBorrowFeeOccurrenceV1 | ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1
)


class _OccurrenceConstructionV1(NamedTuple):
    request_identity: E01RequestIdentityV1
    pre_state: ZUSDState
    post_state: ZUSDState
    principal_e8: int
    fee_e8: int
    fee_bps: int
    debt_delta_e8: int
    occurrence_root: str


def _authenticated_borrow_fee_occurrence_v1(
    value: _OccurrenceConstructionV1,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceV1:
    return ZUSDAuthenticatedBorrowFeeOccurrenceV1(
        request_identity=value.request_identity,
        pre_state=value.pre_state,
        post_state=value.post_state,
        principal_e8=value.principal_e8,
        fee_e8=value.fee_e8,
        fee_bps=value.fee_bps,
        debt_delta_e8=value.debt_delta_e8,
        occurrence_root=value.occurrence_root,
        _construction_token=_OCCURRENCE_TOKEN_V1,
    )


__all__ = (
    "MAX_BORROWER_ID_BYTES_V1",
    "ZUSD_AUTHENTICATED_BORROW_COMMAND_SCHEMA_V1",
    "ZUSD_AUTHENTICATED_BORROW_FEE_OCCURRENCE_SCHEMA_V1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceResultV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceSourceV1",
    "ZUSDAuthenticatedBorrowFeeOccurrenceV1",
)
