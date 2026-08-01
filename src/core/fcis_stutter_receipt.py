"""Controlled RQAG stutter receipts for the FCIS research model.

A stutter receipt certifies one observational identity in a runtime trace. The
receipt is created only by the typed verifier below, which admits a closed set
of operation kinds, requires equality of the exact canonical roots and the
observable roots, and derives the pinned checker and verification roots.

This remains unmounted research evidence. The verifier cannot establish that a
caller truthfully labeled an external operation without an upstream operation
classifier and canonical state adapter.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import domain_sep_bytes, hex_to_bytes_fixed, sha256_hex

FCIS_RQAG_STUTTER_VERSION_V1: Final = "zenodex/fcis/rqag/stutter-receipt/v1"
MAX_STUTTER_PATH_PARTS_V1: Final = 8

_STUTTER_CONSTRUCTION_TOKEN_V1 = object()


class StutterOperationKindV1(Enum):
    SAME_COMMIT_RETRY = "same_commit_retry"
    CANONICAL_REOPEN_REENCODE = "canonical_reopen_reencode"
    SAME_EFFECT_DESTINATION_DEDUP = "same_effect_destination_dedup"
    REPEAT_PURE_VERIFICATION = "repeat_pure_verification"


class NonStutterOperationKindV1(Enum):
    NEW_COMMIT = "new_commit"
    ACK_PUBLICATION = "ack_publication"
    MIGRATION = "migration"


class StutterCheckerIdV1(Enum):
    SAME_COMMIT_RETRY = "zenodex/fcis/rqag/checker/same-commit-retry/v1"
    CANONICAL_REOPEN_REENCODE = "zenodex/fcis/rqag/checker/canonical-reopen-reencode/v1"
    SAME_EFFECT_DESTINATION_DEDUP = "zenodex/fcis/rqag/checker/same-effect-destination-dedup/v1"
    REPEAT_PURE_VERIFICATION = "zenodex/fcis/rqag/checker/repeat-pure-verification/v1"


class StutterRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_ROOT = "invalid_root"
    FORBIDDEN_OPERATION = "forbidden_operation"
    CANONICAL_STATE_CHANGED = "canonical_state_changed"
    OBSERVABLE_STATE_CHANGED = "observable_state_changed"
    CHECKER_MISMATCH = "checker_mismatch"
    INVALID_RECEIPT = "invalid_receipt"


def _u32_be_v1(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 32:
        raise ValueError("stutter frame length must fit U32")
    return value.to_bytes(4, "big")


def _frame_v1(value: bytes) -> bytes:
    return _u32_be_v1(len(value)) + value


def _require_root_v1(name: str, value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise ValueError(f"{name} must be a canonical lowercase 0x root")
    exact = value
    hex_to_bytes_fixed(exact, nbytes=32, name=name)
    return exact


def _root_bytes_v1(value: str) -> bytes:
    return cast(bytes, hex_to_bytes_fixed(value, nbytes=32, name="stutter_root"))


def _hash_fields_v1(domain: str, fields: tuple[bytes, ...]) -> str:
    payload = bytearray()
    payload.extend(_u32_be_v1(len(fields)))
    for field in fields:
        payload.extend(_frame_v1(field))
    return cast(str, sha256_hex(domain_sep_bytes(domain, version=1) + bytes(payload)))


def _checker_for_operation_v1(operation: StutterOperationKindV1) -> StutterCheckerIdV1:
    if operation is StutterOperationKindV1.SAME_COMMIT_RETRY:
        return StutterCheckerIdV1.SAME_COMMIT_RETRY
    if operation is StutterOperationKindV1.CANONICAL_REOPEN_REENCODE:
        return StutterCheckerIdV1.CANONICAL_REOPEN_REENCODE
    if operation is StutterOperationKindV1.SAME_EFFECT_DESTINATION_DEDUP:
        return StutterCheckerIdV1.SAME_EFFECT_DESTINATION_DEDUP
    if operation is StutterOperationKindV1.REPEAT_PURE_VERIFICATION:
        return StutterCheckerIdV1.REPEAT_PURE_VERIFICATION
    raise ValueError("unsupported stutter operation")


def _verification_root_v1(
    *,
    operation_id: str,
    operation_kind: StutterOperationKindV1,
    pre_canonical_root: str,
    post_canonical_root: str,
    observable_root: str,
    checker_id: StutterCheckerIdV1,
) -> str:
    return _hash_fields_v1(
        "zenodex/fcis/rqag/stutter-verification",
        (
            _root_bytes_v1(operation_id),
            operation_kind.value.encode("ascii"),
            _root_bytes_v1(pre_canonical_root),
            _root_bytes_v1(post_canonical_root),
            _root_bytes_v1(observable_root),
            checker_id.value.encode("ascii"),
        ),
    )


def _receipt_root_v1(receipt: StutterReceiptV1) -> str:
    return _hash_fields_v1(
        "zenodex/fcis/rqag/stutter-receipt",
        (
            receipt.operation_id.encode("ascii"),
            receipt.operation_kind.value.encode("ascii"),
            _root_bytes_v1(receipt.pre_canonical_root),
            _root_bytes_v1(receipt.post_canonical_root),
            _root_bytes_v1(receipt.observable_root),
            receipt.checker_id.value.encode("ascii"),
            _root_bytes_v1(receipt.verification_root),
        ),
    )


@dataclass(frozen=True, slots=True)
class StutterReceiptV1:
    """A controlled certificate for one observational identity."""

    operation_id: str
    operation_kind: StutterOperationKindV1
    pre_canonical_root: str
    post_canonical_root: str
    observable_root: str
    checker_id: StutterCheckerIdV1
    verification_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STUTTER_CONSTRUCTION_TOKEN_V1:
            raise TypeError("stutter receipts require controlled verification")
        _require_root_v1("operation_id", self.operation_id)
        if type(self.operation_kind) is not StutterOperationKindV1:
            raise TypeError("stutter operation kind must be exact")
        for name in (
            "pre_canonical_root",
            "post_canonical_root",
            "observable_root",
            "verification_root",
        ):
            _require_root_v1(name, object.__getattribute__(self, name))
        if type(self.checker_id) is not StutterCheckerIdV1:
            raise TypeError("stutter checker ID must be exact")
        expected_checker = _checker_for_operation_v1(self.operation_kind)
        if self.checker_id is not expected_checker:
            raise ValueError("stutter checker is not pinned to the operation")
        if self.pre_canonical_root != self.post_canonical_root:
            raise ValueError("stutter canonical roots differ")
        expected_verification = _verification_root_v1(
            operation_id=self.operation_id,
            operation_kind=self.operation_kind,
            pre_canonical_root=self.pre_canonical_root,
            post_canonical_root=self.post_canonical_root,
            observable_root=self.observable_root,
            checker_id=self.checker_id,
        )
        if self.verification_root != expected_verification:
            raise ValueError("stutter verification root does not match its evidence")

    @property
    def receipt_root(self) -> str:
        return _receipt_root_v1(self)


@dataclass(frozen=True, slots=True)
class StutterRejectV1:
    code: StutterRejectCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STUTTER_CONSTRUCTION_TOKEN_V1:
            raise TypeError("stutter rejections require controlled derivation")
        if type(self.code) is not StutterRejectCodeV1:
            raise TypeError("stutter rejection code must be exact")
        if type(self.path) is not tuple or len(self.path) > MAX_STUTTER_PATH_PARTS_V1:
            raise TypeError("stutter rejection path must be a bounded exact tuple")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("stutter rejection path parts must be nonempty strings")


StutterResultV1: TypeAlias = StutterReceiptV1 | StutterRejectV1


def _reject_v1(code: StutterRejectCodeV1, *path: str) -> StutterRejectV1:
    return StutterRejectV1(
        code,
        path,
        _construction_token=_STUTTER_CONSTRUCTION_TOKEN_V1,
    )


def verify_stutter_candidate_v1(
    *,
    operation_id: object,
    operation_kind: object,
    pre_canonical_root: object,
    post_canonical_root: object,
    observable_pre_root: object,
    observable_post_root: object,
) -> StutterResultV1:
    """Certify one closed RQAG operation as a stutter or return a typed reject."""

    if type(operation_kind) is NonStutterOperationKindV1:
        return _reject_v1(
            StutterRejectCodeV1.FORBIDDEN_OPERATION,
            "operation_kind",
            operation_kind.value,
        )
    if type(operation_kind) is not StutterOperationKindV1:
        return _reject_v1(StutterRejectCodeV1.WRONG_EXACT_TYPE, "operation_kind")
    try:
        checked_operation_id = _require_root_v1("operation_id", operation_id)
        checked_pre = _require_root_v1("pre_canonical_root", pre_canonical_root)
        checked_post = _require_root_v1("post_canonical_root", post_canonical_root)
        checked_observable_pre = _require_root_v1(
            "observable_pre_root",
            observable_pre_root,
        )
        checked_observable_post = _require_root_v1(
            "observable_post_root",
            observable_post_root,
        )
    except (TypeError, ValueError):
        return _reject_v1(StutterRejectCodeV1.INVALID_ROOT, "roots")
    if checked_pre != checked_post:
        return _reject_v1(StutterRejectCodeV1.CANONICAL_STATE_CHANGED, "canonical")
    if checked_observable_pre != checked_observable_post:
        return _reject_v1(StutterRejectCodeV1.OBSERVABLE_STATE_CHANGED, "observable")
    checker_id = _checker_for_operation_v1(operation_kind)
    verification_root = _verification_root_v1(
        operation_id=checked_operation_id,
        operation_kind=operation_kind,
        pre_canonical_root=checked_pre,
        post_canonical_root=checked_post,
        observable_root=checked_observable_pre,
        checker_id=checker_id,
    )
    try:
        return StutterReceiptV1(
            operation_id=checked_operation_id,
            operation_kind=operation_kind,
            pre_canonical_root=checked_pre,
            post_canonical_root=checked_post,
            observable_root=checked_observable_pre,
            checker_id=checker_id,
            verification_root=verification_root,
            _construction_token=_STUTTER_CONSTRUCTION_TOKEN_V1,
        )
    except (TypeError, ValueError):
        return _reject_v1(StutterRejectCodeV1.INVALID_RECEIPT, "receipt")


def verify_stutter_receipt_v1(receipt: object) -> StutterResultV1:
    """Revalidate a receipt before using it to remove an RQAG loop."""

    if type(receipt) is not StutterReceiptV1:
        return _reject_v1(StutterRejectCodeV1.WRONG_EXACT_TYPE, "receipt")
    try:
        receipt.__post_init__(_STUTTER_CONSTRUCTION_TOKEN_V1)
    except (TypeError, ValueError) as exc:
        code = (
            StutterRejectCodeV1.CHECKER_MISMATCH
            if "checker is not pinned" in str(exc)
            else StutterRejectCodeV1.INVALID_RECEIPT
        )
        return _reject_v1(code, "receipt")
    return receipt


__all__ = (
    "FCIS_RQAG_STUTTER_VERSION_V1",
    "NonStutterOperationKindV1",
    "StutterCheckerIdV1",
    "StutterOperationKindV1",
    "StutterRejectCodeV1",
    "StutterReceiptV1",
    "StutterRejectV1",
    "StutterResultV1",
    "verify_stutter_candidate_v1",
    "verify_stutter_receipt_v1",
)
