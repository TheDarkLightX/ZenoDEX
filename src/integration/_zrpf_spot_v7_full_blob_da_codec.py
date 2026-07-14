"""Fixed bounded wire codec for the Spot V7 full-blob DA checker."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    MAX_FULL_BLOB_BYTES_V1,
    MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
)

FULL_BLOB_DA_CHECKER_REQUEST_SCHEMA_V1 = "zenodex.zrpf.full_blob_da_checker.request.v1"
FULL_BLOB_DA_CHECKER_RESPONSE_SCHEMA_V1 = "zenodex.zrpf.full_blob_da_checker.response.v1"
FULL_BLOB_DA_CHECKER_PROTOCOL_VERSION_V1 = 1

REQUEST_MAGIC_V1 = b"ZRPFFBDAREQV1!!!"
RESPONSE_MAGIC_V1 = b"ZRPFFBDARESV1!!!"
REQUEST_HEADER_BYTES_V1 = 198
RESPONSE_BODY_BYTES_V1 = 298
RESPONSE_BYTES_V1 = 330
MAX_U64 = (1 << 64) - 1
RESPONSE_COMMITMENT_DOMAIN_V1 = b"zenodex.zrpf.full_blob_da_checker.response_commitment.v1"


@dataclass(frozen=True, slots=True)
class _FullBlobDaCheckInputV1:
    policy: _GovernedSpotV7OperationalPolicyV2
    expected_certificate_epoch: int
    checked_epoch: int
    exact_certificate_bytes: bytes
    exact_blob_bytes: bytes

    def __post_init__(self) -> None:
        if (
            type(self.policy) is not _GovernedSpotV7OperationalPolicyV2
            or not self.policy._has_private_seal()
        ):
            raise TypeError("DA checker requires the exact governed Spot V7 policy")
        _require_u64(self.expected_certificate_epoch, "expected certificate epoch")
        _require_u64(self.checked_epoch, "checked epoch")
        _require_bounded_bytes(
            self.exact_certificate_bytes,
            name="exact full-blob certificate",
            maximum=MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
        )
        _require_bounded_bytes(
            self.exact_blob_bytes,
            name="exact full blob",
            maximum=MAX_FULL_BLOB_BYTES_V1,
        )


@dataclass(frozen=True, slots=True)
class _ExpectedFullBlobDaResponseV1:
    request_sha256: bytes
    application_id: bytes
    chain_or_domain_id: bytes
    expected_certificate_epoch: int
    policy_root: bytes
    exact_certificate_sha256: bytes
    exact_blob_sha256: bytes
    checked_epoch: int

    def __post_init__(self) -> None:
        for name in (
            "request_sha256",
            "application_id",
            "chain_or_domain_id",
            "policy_root",
            "exact_certificate_sha256",
            "exact_blob_sha256",
        ):
            value = getattr(self, name)
            if type(value) is not bytes or len(value) != 32:
                raise TypeError(f"expected DA response {name} must be exact 32-byte bytes")
        _require_u64(self.expected_certificate_epoch, "expected certificate epoch")
        _require_u64(self.checked_epoch, "checked epoch")


@dataclass(frozen=True, slots=True)
class _ParsedFullBlobDaResponseV1:
    certificate_root: bytes
    data_root: bytes
    retention_through_epoch: int


@dataclass(frozen=True, slots=True)
class _DecodedFullBlobDaResponseV1:
    application_id: bytes
    chain_or_domain_id: bytes
    epoch_id: int
    certificate_root: bytes
    data_root: bytes
    policy_root: bytes
    exact_blob_sha256: bytes
    exact_certificate_sha256: bytes
    checked_epoch: int
    retention_through_epoch: int
    request_sha256: bytes


def _encode_checker_request_v1(input_value: _FullBlobDaCheckInputV1) -> bytes:
    if type(input_value) is not _FullBlobDaCheckInputV1:
        raise TypeError("full-blob checker request input has the wrong type")
    material = input_value.policy._policy_for_atomic_store()
    certificate_length = len(input_value.exact_certificate_bytes)
    blob_length = len(input_value.exact_blob_bytes)
    request = b"".join(
        (
            REQUEST_MAGIC_V1,
            FULL_BLOB_DA_CHECKER_PROTOCOL_VERSION_V1.to_bytes(2, "big"),
            _prefixed_hash_bytes(material.application_id, "policy application"),
            _prefixed_hash_bytes(material.chain_or_domain_id, "policy domain"),
            _prefixed_hash_bytes(material.data_schema_id, "policy data schema"),
            _prefixed_hash_bytes(material.storage_policy_hash, "policy storage hash"),
            material.minimum_retention_epochs.to_bytes(8, "big"),
            material.minimum_remaining_epochs.to_bytes(8, "big"),
            material.maximum_blob_bytes.to_bytes(8, "big"),
            input_value.expected_certificate_epoch.to_bytes(8, "big"),
            input_value.checked_epoch.to_bytes(8, "big"),
            certificate_length.to_bytes(4, "big"),
            blob_length.to_bytes(8, "big"),
            input_value.exact_certificate_bytes,
            input_value.exact_blob_bytes,
        )
    )
    expected_length = REQUEST_HEADER_BYTES_V1 + certificate_length + blob_length
    if len(request) != expected_length:
        raise ValueError("full-blob checker request framing mismatch")
    return request


def _expected_response_v1(
    request: bytes,
    input_value: _FullBlobDaCheckInputV1,
) -> _ExpectedFullBlobDaResponseV1:
    if type(input_value) is not _FullBlobDaCheckInputV1:
        raise TypeError("full-blob checker request input has the wrong type")
    material = input_value.policy._policy_for_atomic_store()
    return _ExpectedFullBlobDaResponseV1(
        request_sha256=hashlib.sha256(request).digest(),
        application_id=_prefixed_hash_bytes(material.application_id, "policy application"),
        chain_or_domain_id=_prefixed_hash_bytes(material.chain_or_domain_id, "policy domain"),
        expected_certificate_epoch=input_value.expected_certificate_epoch,
        policy_root=_prefixed_hash_bytes(material.full_blob_policy_root, "DA policy root"),
        exact_certificate_sha256=hashlib.sha256(input_value.exact_certificate_bytes).digest(),
        exact_blob_sha256=hashlib.sha256(input_value.exact_blob_bytes).digest(),
        checked_epoch=input_value.checked_epoch,
    )


def _parse_checker_response_v1(
    raw: bytes,
    expected: _ExpectedFullBlobDaResponseV1,
) -> _ParsedFullBlobDaResponseV1:
    body = _validated_response_body(raw)
    reader = _ResponseReaderV1(body)
    _require_response_header(reader)
    fields = _read_response_fields(reader)
    _require_response_binding(fields, expected)
    if fields.certificate_root == bytes(32) or fields.data_root == bytes(32):
        raise ValueError("response contains a zero commitment")
    if fields.retention_through_epoch < fields.checked_epoch:
        raise ValueError("response retention ends before checked epoch")
    return _ParsedFullBlobDaResponseV1(
        fields.certificate_root,
        fields.data_root,
        fields.retention_through_epoch,
    )


def _validated_response_body(raw: bytes) -> bytes:
    if type(raw) is not bytes or len(raw) != RESPONSE_BYTES_V1:
        raise ValueError("response byte length mismatch")
    body = raw[:RESPONSE_BODY_BYTES_V1]
    observed = raw[RESPONSE_BODY_BYTES_V1:]
    required = hashlib.sha256(RESPONSE_COMMITMENT_DOMAIN_V1 + body).digest()
    if observed != required:
        raise ValueError("response commitment mismatch")
    return body


def _require_response_header(reader: _ResponseReaderV1) -> None:
    if reader.read(16) != RESPONSE_MAGIC_V1:
        raise ValueError("response magic mismatch")
    if reader.u16() != FULL_BLOB_DA_CHECKER_PROTOCOL_VERSION_V1:
        raise ValueError("response version mismatch")


def _read_response_fields(reader: _ResponseReaderV1) -> _DecodedFullBlobDaResponseV1:
    fields = _DecodedFullBlobDaResponseV1(
        application_id=reader.read(32),
        chain_or_domain_id=reader.read(32),
        epoch_id=reader.u64(),
        certificate_root=reader.read(32),
        data_root=reader.read(32),
        policy_root=reader.read(32),
        exact_blob_sha256=reader.read(32),
        exact_certificate_sha256=reader.read(32),
        checked_epoch=reader.u64(),
        retention_through_epoch=reader.u64(),
        request_sha256=reader.read(32),
    )
    reader.finished()
    return fields


def _require_response_binding(
    fields: _DecodedFullBlobDaResponseV1,
    expected: _ExpectedFullBlobDaResponseV1,
) -> None:
    if type(expected) is not _ExpectedFullBlobDaResponseV1:
        raise TypeError("expected response binding has wrong type")
    observed = (
        fields.application_id,
        fields.chain_or_domain_id,
        fields.epoch_id,
        fields.policy_root,
        fields.exact_certificate_sha256,
        fields.exact_blob_sha256,
        fields.checked_epoch,
        fields.request_sha256,
    )
    required = (
        expected.application_id,
        expected.chain_or_domain_id,
        expected.expected_certificate_epoch,
        expected.policy_root,
        expected.exact_certificate_sha256,
        expected.exact_blob_sha256,
        expected.checked_epoch,
        expected.request_sha256,
    )
    if observed != required:
        raise ValueError("response does not bind the exact checker request")


class _ResponseReaderV1:
    __slots__ = ("_offset", "_raw")

    def __init__(self, raw: bytes) -> None:
        self._raw = raw
        self._offset = 0

    def read(self, length: int) -> bytes:
        end = self._offset + length
        value = self._raw[self._offset : end]
        if len(value) != length:
            raise ValueError("full-blob checker response is truncated")
        self._offset = end
        return value

    def u16(self) -> int:
        return int.from_bytes(self.read(2), "big")

    def u64(self) -> int:
        return int.from_bytes(self.read(8), "big")

    def finished(self) -> None:
        if self._offset != len(self._raw):
            raise ValueError("full-blob checker response has trailing bytes")


def _prefixed_hash_bytes(value: object, name: str) -> bytes:
    if type(value) is not str or not value.startswith("0x") or len(value) != 66:
        raise ValueError(f"{name} must be exact 0x-prefixed SHA-256")
    bare = value[2:]
    if any(character not in "0123456789abcdef" for character in bare):
        raise ValueError(f"{name} must be exact 0x-prefixed SHA-256")
    parsed = bytes.fromhex(bare)
    if parsed == bytes(32):
        raise ValueError(f"{name} must be nonzero")
    return parsed


def _require_u64(value: object, name: str) -> None:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise ValueError(f"{name} must be an unsigned 64-bit integer")


def _require_bounded_bytes(value: object, *, name: str, maximum: int) -> None:
    if type(value) is not bytes or not value or len(value) > maximum:
        raise ValueError(f"{name} must be exact nonempty bytes within {maximum}")
