"""Exact authority-neutral codec for ``SpotSettlementV7VerifierOutputV1``."""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Final

SPOT_V7_VERIFIER_OUTPUT_MAGIC_V1: Final = b"ZSPTV7O1"
SPOT_V7_VERIFIER_OUTPUT_VERSION_V1: Final = 1
SPOT_V7_VERIFIER_OUTPUT_FIXED_FIELD_COUNT_V1: Final = 19
SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1: Final = (
    8 + 2 + 4 * 4 + 32 * SPOT_V7_VERIFIER_OUTPUT_FIXED_FIELD_COUNT_V1
)
SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1: Final = 65_536

SPOT_V7_JOURNAL_MAGIC_V1: Final = b"ZSPTV7J1"
SPOT_V7_JOURNAL_VERSION_V1: Final = 1
SPOT_V7_JOURNAL_FIXED_FIELD_COUNT_V1: Final = 13
SPOT_V7_JOURNAL_HEADER_BYTES_V1: Final = 8 + 2 + 4 + 4 + 2 + 2 + 4
SPOT_V7_SEMANTIC_JOURNAL_BYTES_V1: Final = 2 + 8 * 32 + 48 + 4
SPOT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1: Final = 2 + 12 * 32
SPOT_V7_MAX_PLAN_B_BYTES_V1: Final = 48 * 1_024
SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1: Final = (
    b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1"
)


class SpotV7FirecrackerProtocolRejectV1(ValueError):
    """Stable fail-closed rejection shared by payload and transport codecs."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True, init=False)
class SpotV7VerifierPayloadFrameV1:
    """Exactly decoded V7 verifier-output bytes with no execution authority."""

    raw_bytes: bytes
    journal_bytes: bytes
    plan_b_bytes: bytes
    fixed_fields: tuple[bytes, ...]
    journal_fixed_fields: tuple[bytes, ...]
    effect_binding_fixed_fields: tuple[bytes, ...]
    state_root_host_input_length: int

    def __new__(cls) -> SpotV7VerifierPayloadFrameV1:
        raise TypeError("SpotV7VerifierPayloadFrameV1 requires exact decoding")

    @property
    def payload_sha256(self) -> bytes:
        return hashlib.sha256(self.raw_bytes).digest()


@dataclass(frozen=True, slots=True)
class _JournalShapeV1:
    host_input_length: int
    semantic_length: int
    binding_length: int
    plan_length: int


@dataclass(frozen=True, slots=True)
class _DecodedV7JournalV1:
    raw_bytes: bytes
    plan_b_bytes: bytes
    fixed_fields: tuple[bytes, ...]
    effect_binding_fixed_fields: tuple[bytes, ...]
    state_root_host_input_length: int


def decode_exact_v7_verifier_payload_v1(
    raw: bytes,
) -> SpotV7VerifierPayloadFrameV1:
    """Decode exact ``SpotSettlementV7VerifierOutputV1`` canonical framing."""

    if type(raw) is not bytes or not (
        SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1 < len(raw) <= SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1
    ):
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_length")
    if raw[:8] != SPOT_V7_VERIFIER_OUTPUT_MAGIC_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_magic")
    version, total, journal_length, plan_length, host_input_length = struct.unpack_from(
        ">HIIII", raw, 8
    )
    if version != SPOT_V7_VERIFIER_OUTPUT_VERSION_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_version")
    if (
        total != len(raw)
        or journal_length != len(raw) - SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1
        or not 0 < plan_length <= SPOT_V7_MAX_PLAN_B_BYTES_V1
        or host_input_length == 0
    ):
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_framing")
    fixed = _read_nonzero_fields(
        raw,
        offset=26,
        count=SPOT_V7_VERIFIER_OUTPUT_FIXED_FIELD_COUNT_V1,
        code="v7_output_fixed_field",
    )
    journal = _decode_exact_v7_journal_v1(raw[SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1:])
    if plan_length != len(journal.plan_b_bytes) or (
        host_input_length != journal.state_root_host_input_length
    ):
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_journal_binding")
    _require_v7_output_journal_associations(fixed, journal)
    return _new_payload_frame(
        raw,
        journal,
        fixed,
        host_input_length,
    )


def _new_payload_frame(
    raw: bytes,
    journal: _DecodedV7JournalV1,
    fixed: tuple[bytes, ...],
    host_input_length: int,
) -> SpotV7VerifierPayloadFrameV1:
    value = object.__new__(SpotV7VerifierPayloadFrameV1)
    object.__setattr__(value, "raw_bytes", raw)
    object.__setattr__(value, "journal_bytes", journal.raw_bytes)
    object.__setattr__(value, "plan_b_bytes", journal.plan_b_bytes)
    object.__setattr__(value, "fixed_fields", fixed)
    object.__setattr__(value, "journal_fixed_fields", journal.fixed_fields)
    object.__setattr__(
        value,
        "effect_binding_fixed_fields",
        journal.effect_binding_fixed_fields,
    )
    object.__setattr__(value, "state_root_host_input_length", host_input_length)
    return value


def _decode_exact_v7_journal_v1(raw: bytes) -> _DecodedV7JournalV1:
    minimum = (
        SPOT_V7_JOURNAL_HEADER_BYTES_V1
        + 32 * SPOT_V7_JOURNAL_FIXED_FIELD_COUNT_V1
        + SPOT_V7_SEMANTIC_JOURNAL_BYTES_V1
        + SPOT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1
    )
    if not minimum < len(raw) <= minimum + SPOT_V7_MAX_PLAN_B_BYTES_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_journal_length")
    if raw[:8] != SPOT_V7_JOURNAL_MAGIC_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_journal_magic")
    version, total, host_length, semantic_length, binding_length, plan_length = struct.unpack_from(
        ">HIIHHI", raw, 8
    )
    if version != SPOT_V7_JOURNAL_VERSION_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_journal_version")
    shape = _JournalShapeV1(host_length, semantic_length, binding_length, plan_length)
    if not _journal_shape_is_exact(shape, total=total, actual=len(raw), minimum=minimum):
        raise SpotV7FirecrackerProtocolRejectV1("v7_journal_framing")
    return _decode_v7_journal_body(raw, shape)


def _journal_shape_is_exact(
    shape: _JournalShapeV1,
    *,
    total: int,
    actual: int,
    minimum: int,
) -> bool:
    return (
        total == actual
        and shape.host_input_length > 0
        and shape.semantic_length == SPOT_V7_SEMANTIC_JOURNAL_BYTES_V1
        and shape.binding_length == SPOT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1
        and 0 < shape.plan_length <= SPOT_V7_MAX_PLAN_B_BYTES_V1
        and minimum + shape.plan_length == actual
    )


def _decode_v7_journal_body(
    raw: bytes,
    shape: _JournalShapeV1,
) -> _DecodedV7JournalV1:
    fixed = _read_nonzero_fields(
        raw,
        offset=SPOT_V7_JOURNAL_HEADER_BYTES_V1,
        count=SPOT_V7_JOURNAL_FIXED_FIELD_COUNT_V1,
        code="v7_journal_fixed_field",
    )
    cursor = SPOT_V7_JOURNAL_HEADER_BYTES_V1 + 32 * SPOT_V7_JOURNAL_FIXED_FIELD_COUNT_V1
    semantic = raw[cursor : cursor + shape.semantic_length]
    cursor += shape.semantic_length
    binding = raw[cursor : cursor + shape.binding_length]
    cursor += shape.binding_length
    plan = raw[cursor : cursor + shape.plan_length]
    if hashlib.sha256(semantic).digest() != fixed[8]:
        raise SpotV7FirecrackerProtocolRejectV1("v7_semantic_journal_hash")
    if _binding_journal_commitment(binding) != fixed[9]:
        raise SpotV7FirecrackerProtocolRejectV1("v7_effect_binding_commitment")
    binding_fixed = _decode_effect_binding_journal_v1(binding)
    if binding_fixed[4] != fixed[10]:
        raise SpotV7FirecrackerProtocolRejectV1("v7_plan_commitment_binding")
    if hashlib.sha256(plan).digest() != fixed[11]:
        raise SpotV7FirecrackerProtocolRejectV1("v7_plan_bytes_sha256")
    return _DecodedV7JournalV1(
        raw,
        plan,
        fixed,
        binding_fixed,
        shape.host_input_length,
    )


def _decode_effect_binding_journal_v1(raw: bytes) -> tuple[bytes, ...]:
    if len(raw) != SPOT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_effect_binding_length")
    if int.from_bytes(raw[:2], "big") != 1:
        raise SpotV7FirecrackerProtocolRejectV1("v7_effect_binding_version")
    return _read_nonzero_fields(
        raw,
        offset=2,
        count=12,
        code="v7_effect_binding_field",
    )


def _require_v7_output_journal_associations(
    output: tuple[bytes, ...],
    journal: _DecodedV7JournalV1,
) -> None:
    fixed = journal.fixed_fields
    binding = journal.effect_binding_fixed_fields
    associations = (
        (output[3], hashlib.sha256(journal.raw_bytes).digest()),
        (output[4], fixed[0]),
        (output[5], fixed[1]),
        (output[6], fixed[2]),
        (output[7], fixed[3]),
        (output[8], fixed[4]),
        (output[9], fixed[5]),
        (output[10], fixed[10]),
        (output[11], fixed[11]),
        (output[12], binding[6]),
        (output[13], binding[7]),
        (output[14], fixed[12]),
        (output[18], fixed[7]),
    )
    if any(actual != expected for actual, expected in associations):
        raise SpotV7FirecrackerProtocolRejectV1("v7_output_journal_binding")


def _binding_journal_commitment(raw: bytes) -> bytes:
    domain = SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1
    return hashlib.sha256(len(domain).to_bytes(2, "big") + domain + raw).digest()


def _read_nonzero_fields(
    raw: bytes,
    *,
    offset: int,
    count: int,
    code: str,
) -> tuple[bytes, ...]:
    fields = tuple(raw[offset + index * 32 : offset + (index + 1) * 32] for index in range(count))
    if len(fields) != count or any(len(field) != 32 or not any(field) for field in fields):
        raise SpotV7FirecrackerProtocolRejectV1(code)
    return fields
