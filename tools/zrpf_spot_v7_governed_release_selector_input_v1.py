"""Exact authority-neutral selector and revocation records for Spot V7.

These fixed-width records carry externally governed proposals.  Parsing them
establishes canonical bytes and identity only.  It does not authenticate the
publisher or grant release, runtime, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from enum import IntEnum
from typing import Final, final

SELECTOR_INPUT_MAGIC_V1: Final = b"ZRPFSV7SELECTV1\x00"
REVOCATION_RECORD_MAGIC_V1: Final = b"ZRPFSV7REVOKEV1\x00"
WIRE_VERSION_V1: Final = 1
SELECTOR_HEADER_BYTES_V1: Final = 36
REVOCATION_HEADER_BYTES_V1: Final = 32
SELECTOR_FORMAT_FLAGS_V1: Final = 1
REVOCATION_FORMAT_FLAGS_V1: Final = 1

_SELECTOR_STRUCT_V1: Final = struct.Struct(">16sHHIIIIQQQ32s32s32s32s32s32s32s32sI")
_REVOCATION_STRUCT_V1: Final = struct.Struct(">16sHHIII32s32s32sQQII32s32s")

SELECTOR_INPUT_BYTES_V1: Final = _SELECTOR_STRUCT_V1.size
REVOCATION_RECORD_BYTES_V1: Final = _REVOCATION_STRUCT_V1.size

_SELECTOR_ID_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.selector_input.v1"
_REVOCATION_ID_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.revocation_record.v1"
ZERO_DIGEST_V1: Final = b"\x00" * 32


class SelectorOperationV1(IntEnum):
    SELECT = 1
    REVOKE = 2


class SpotV7SelectorInputRejectV1(ValueError):
    """Stable fail-closed rejection for the fixed selector wire boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@final
@dataclass(frozen=True, slots=True)
class GovernedReleaseSelectorInputV1:
    canonical_bytes: bytes
    input_id: bytes
    operation: SelectorOperationV1
    expected_database_revision: int
    evaluation_epoch: int
    target_release_revision: int
    expected_current_candidate_id: bytes | None
    expected_current_select_input_id: bytes | None
    target_candidate_id: bytes
    target_candidate_sha256: bytes
    rollback_policy_root: bytes
    revocation_registry_root: bytes
    revocation_record_id: bytes | None
    selector_nonce: bytes

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@final
@dataclass(frozen=True, slots=True)
class SpotV7RevocationRecordV1:
    canonical_bytes: bytes
    record_id: bytes
    candidate_id: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes
    effective_epoch: int
    record_revision: int
    reason_code: int
    issuer_set_root: bytes
    record_nonce: bytes

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def recompose_governed_release_selector_input_v1(
    *,
    operation: SelectorOperationV1,
    expected_database_revision: int,
    evaluation_epoch: int,
    target_release_revision: int,
    expected_current_candidate_id: bytes | None,
    expected_current_select_input_id: bytes | None,
    target_candidate_id: bytes,
    target_candidate_sha256: bytes,
    rollback_policy_root: bytes,
    revocation_registry_root: bytes,
    revocation_record_id: bytes | None,
    selector_nonce: bytes,
) -> bytes:
    """Construct the only canonical byte representation of one selector input."""

    operation = _require_operation(operation)
    expected_database_revision = _require_u64(
        expected_database_revision, "selector_expected_database_revision"
    )
    evaluation_epoch = _require_u64(evaluation_epoch, "selector_evaluation_epoch")
    target_release_revision = _require_positive_u64(
        target_release_revision, "selector_target_release_revision"
    )
    expected_candidate = _encode_optional_digest(
        expected_current_candidate_id,
        "selector_expected_current_candidate_id",
    )
    expected_input = _encode_optional_digest(
        expected_current_select_input_id,
        "selector_expected_current_select_input_id",
    )
    target_candidate_id = _require_digest(target_candidate_id, "selector_target_candidate_id")
    target_candidate_sha256 = _require_digest(
        target_candidate_sha256, "selector_target_candidate_sha256"
    )
    rollback_policy_root = _require_digest(rollback_policy_root, "selector_rollback_policy_root")
    revocation_registry_root = _require_digest(
        revocation_registry_root, "selector_revocation_registry_root"
    )
    record_id = _encode_operation_record_id(operation, revocation_record_id)
    selector_nonce = _require_digest(selector_nonce, "selector_nonce")
    return _SELECTOR_STRUCT_V1.pack(
        SELECTOR_INPUT_MAGIC_V1,
        WIRE_VERSION_V1,
        SELECTOR_HEADER_BYTES_V1,
        SELECTOR_INPUT_BYTES_V1,
        int(operation),
        SELECTOR_FORMAT_FLAGS_V1,
        0,
        expected_database_revision,
        evaluation_epoch,
        target_release_revision,
        expected_candidate,
        expected_input,
        target_candidate_id,
        target_candidate_sha256,
        rollback_policy_root,
        revocation_registry_root,
        record_id,
        selector_nonce,
        0,
    )


def parse_exact_governed_release_selector_input_v1(
    raw: bytes,
    *,
    expected_input_id: bytes,
) -> GovernedReleaseSelectorInputV1:
    """Decode exact bytes and require an independently supplied input identity."""

    if type(raw) is not bytes or len(raw) != SELECTOR_INPUT_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("selector_input_size")
    expected_input_id = _require_digest(expected_input_id, "selector_expected_input_id")
    try:
        fields = _SELECTOR_STRUCT_V1.unpack(raw)
    except struct.error as exc:
        raise SpotV7SelectorInputRejectV1("selector_input_size") from exc
    (
        magic,
        version,
        header_bytes,
        total_bytes,
        operation_raw,
        format_flags,
        reserved_u32,
        expected_database_revision,
        evaluation_epoch,
        target_release_revision,
        expected_candidate,
        expected_input,
        target_candidate_id,
        target_candidate_sha256,
        rollback_policy_root,
        revocation_registry_root,
        record_id,
        selector_nonce,
        reserved_tail_u32,
    ) = fields
    if magic != SELECTOR_INPUT_MAGIC_V1:
        raise SpotV7SelectorInputRejectV1("selector_magic")
    if version != WIRE_VERSION_V1:
        raise SpotV7SelectorInputRejectV1("selector_version")
    if header_bytes != SELECTOR_HEADER_BYTES_V1 or total_bytes != SELECTOR_INPUT_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("selector_framing")
    operation = _decode_operation(operation_raw)
    if format_flags != SELECTOR_FORMAT_FLAGS_V1:
        raise SpotV7SelectorInputRejectV1("selector_format_flags")
    if reserved_u32 != 0 or reserved_tail_u32 != 0:
        raise SpotV7SelectorInputRejectV1("selector_reserved")
    _require_positive_u64(target_release_revision, "selector_target_release_revision")
    target_candidate_id = _require_digest(target_candidate_id, "selector_target_candidate_id")
    target_candidate_sha256 = _require_digest(
        target_candidate_sha256, "selector_target_candidate_sha256"
    )
    rollback_policy_root = _require_digest(rollback_policy_root, "selector_rollback_policy_root")
    revocation_registry_root = _require_digest(
        revocation_registry_root, "selector_revocation_registry_root"
    )
    selector_nonce = _require_digest(selector_nonce, "selector_nonce")
    decoded_record_id = _decode_operation_record_id(operation, record_id)
    input_id = derive_governed_release_selector_input_id_v1(raw)
    if input_id != expected_input_id:
        raise SpotV7SelectorInputRejectV1("selector_expected_input_id")
    return GovernedReleaseSelectorInputV1(
        canonical_bytes=raw,
        input_id=input_id,
        operation=operation,
        expected_database_revision=expected_database_revision,
        evaluation_epoch=evaluation_epoch,
        target_release_revision=target_release_revision,
        expected_current_candidate_id=_decode_optional_digest(expected_candidate),
        expected_current_select_input_id=_decode_optional_digest(expected_input),
        target_candidate_id=target_candidate_id,
        target_candidate_sha256=target_candidate_sha256,
        rollback_policy_root=rollback_policy_root,
        revocation_registry_root=revocation_registry_root,
        revocation_record_id=decoded_record_id,
        selector_nonce=selector_nonce,
    )


def derive_governed_release_selector_input_id_v1(raw: bytes) -> bytes:
    if type(raw) is not bytes or len(raw) != SELECTOR_INPUT_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("selector_input_size")
    return _domain_hash(_SELECTOR_ID_DOMAIN_V1, raw)


def recompose_spot_v7_revocation_record_v1(
    *,
    candidate_id: bytes,
    revocation_policy_root: bytes,
    revocation_registry_root: bytes,
    effective_epoch: int,
    record_revision: int,
    reason_code: int,
    issuer_set_root: bytes,
    record_nonce: bytes,
) -> bytes:
    """Construct the canonical fixed-width revocation record."""

    candidate_id = _require_digest(candidate_id, "revocation_candidate_id")
    revocation_policy_root = _require_digest(revocation_policy_root, "revocation_policy_root")
    revocation_registry_root = _require_digest(revocation_registry_root, "revocation_registry_root")
    effective_epoch = _require_u64(effective_epoch, "revocation_effective_epoch")
    record_revision = _require_positive_u64(record_revision, "revocation_record_revision")
    if type(reason_code) is not int or not 0 < reason_code <= 0xFFFF_FFFF:
        raise SpotV7SelectorInputRejectV1("revocation_reason_code")
    issuer_set_root = _require_digest(issuer_set_root, "revocation_issuer_set_root")
    record_nonce = _require_digest(record_nonce, "revocation_record_nonce")
    return _REVOCATION_STRUCT_V1.pack(
        REVOCATION_RECORD_MAGIC_V1,
        WIRE_VERSION_V1,
        REVOCATION_HEADER_BYTES_V1,
        REVOCATION_RECORD_BYTES_V1,
        REVOCATION_FORMAT_FLAGS_V1,
        0,
        candidate_id,
        revocation_policy_root,
        revocation_registry_root,
        effective_epoch,
        record_revision,
        reason_code,
        0,
        issuer_set_root,
        record_nonce,
    )


def parse_exact_spot_v7_revocation_record_v1(
    raw: bytes,
    *,
    expected_record_id: bytes,
) -> SpotV7RevocationRecordV1:
    """Decode exact revocation bytes and require an independent record identity."""

    if type(raw) is not bytes or len(raw) != REVOCATION_RECORD_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("revocation_record_size")
    expected_record_id = _require_digest(expected_record_id, "revocation_expected_record_id")
    try:
        fields = _REVOCATION_STRUCT_V1.unpack(raw)
    except struct.error as exc:
        raise SpotV7SelectorInputRejectV1("revocation_record_size") from exc
    (
        magic,
        version,
        header_bytes,
        total_bytes,
        format_flags,
        reserved_u32,
        candidate_id,
        revocation_policy_root,
        revocation_registry_root,
        effective_epoch,
        record_revision,
        reason_code,
        reserved_tail_u32,
        issuer_set_root,
        record_nonce,
    ) = fields
    if magic != REVOCATION_RECORD_MAGIC_V1:
        raise SpotV7SelectorInputRejectV1("revocation_magic")
    if version != WIRE_VERSION_V1:
        raise SpotV7SelectorInputRejectV1("revocation_version")
    if header_bytes != REVOCATION_HEADER_BYTES_V1 or total_bytes != REVOCATION_RECORD_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("revocation_framing")
    if format_flags != REVOCATION_FORMAT_FLAGS_V1:
        raise SpotV7SelectorInputRejectV1("revocation_format_flags")
    if reserved_u32 != 0 or reserved_tail_u32 != 0:
        raise SpotV7SelectorInputRejectV1("revocation_reserved")
    candidate_id = _require_digest(candidate_id, "revocation_candidate_id")
    revocation_policy_root = _require_digest(revocation_policy_root, "revocation_policy_root")
    revocation_registry_root = _require_digest(revocation_registry_root, "revocation_registry_root")
    _require_positive_u64(record_revision, "revocation_record_revision")
    if reason_code == 0:
        raise SpotV7SelectorInputRejectV1("revocation_reason_code")
    issuer_set_root = _require_digest(issuer_set_root, "revocation_issuer_set_root")
    record_nonce = _require_digest(record_nonce, "revocation_record_nonce")
    record_id = derive_spot_v7_revocation_record_id_v1(raw)
    if record_id != expected_record_id:
        raise SpotV7SelectorInputRejectV1("revocation_expected_record_id")
    return SpotV7RevocationRecordV1(
        canonical_bytes=raw,
        record_id=record_id,
        candidate_id=candidate_id,
        revocation_policy_root=revocation_policy_root,
        revocation_registry_root=revocation_registry_root,
        effective_epoch=effective_epoch,
        record_revision=record_revision,
        reason_code=reason_code,
        issuer_set_root=issuer_set_root,
        record_nonce=record_nonce,
    )


def derive_spot_v7_revocation_record_id_v1(raw: bytes) -> bytes:
    if type(raw) is not bytes or len(raw) != REVOCATION_RECORD_BYTES_V1:
        raise SpotV7SelectorInputRejectV1("revocation_record_size")
    return _domain_hash(_REVOCATION_ID_DOMAIN_V1, raw)


def _require_operation(value: object) -> SelectorOperationV1:
    if type(value) is not SelectorOperationV1:
        raise SpotV7SelectorInputRejectV1("selector_operation")
    return value


def _decode_operation(value: int) -> SelectorOperationV1:
    try:
        return SelectorOperationV1(value)
    except ValueError as exc:
        raise SpotV7SelectorInputRejectV1("selector_operation") from exc


def _encode_operation_record_id(
    operation: SelectorOperationV1,
    value: bytes | None,
) -> bytes:
    if operation is SelectorOperationV1.SELECT:
        if value is not None:
            raise SpotV7SelectorInputRejectV1("selector_revocation_record_state")
        return ZERO_DIGEST_V1
    if value is None:
        raise SpotV7SelectorInputRejectV1("selector_revocation_record_state")
    return _require_digest(value, "selector_revocation_record_id")


def _decode_operation_record_id(
    operation: SelectorOperationV1,
    value: bytes,
) -> bytes | None:
    if operation is SelectorOperationV1.SELECT:
        if value != ZERO_DIGEST_V1:
            raise SpotV7SelectorInputRejectV1("selector_revocation_record_state")
        return None
    return _require_digest(value, "selector_revocation_record_id")


def _encode_optional_digest(value: bytes | None, code: str) -> bytes:
    if value is None:
        return ZERO_DIGEST_V1
    return _require_digest(value, code)


def _decode_optional_digest(value: bytes) -> bytes | None:
    return None if value == ZERO_DIGEST_V1 else _require_digest(value, "selector_digest")


def _require_digest(value: object, code: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7SelectorInputRejectV1(code)
    return value


def _require_u64(value: object, code: str) -> int:
    if type(value) is not int or not 0 <= value <= 0xFFFF_FFFF_FFFF_FFFF:
        raise SpotV7SelectorInputRejectV1(code)
    return value


def _require_positive_u64(value: object, code: str) -> int:
    value = _require_u64(value, code)
    if value == 0:
        raise SpotV7SelectorInputRejectV1(code)
    return value


def _domain_hash(domain: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big") + domain + len(payload).to_bytes(8, "big") + payload
    ).digest()
