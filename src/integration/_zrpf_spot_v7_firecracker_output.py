"""Exact, authority-neutral decoding for committed Spot V7 Firecracker output.

This module mirrors the fixed outer Firecracker output protocol and the bounded
``SpotSettlementV7VerifierOutputV1`` framing.  Successful decoding establishes
byte-level consistency only.  It does not establish that Firecracker ran under
the governed jailer, that the retained receipt was the input to that run, or
that release, finality, settlement, or production policy accepted the result.
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _candidate_action_authorization_bindings_root,
    _candidate_action_ids_root,
    _candidate_authorization_grant_spends_root,
    _candidate_consumed_object_ids_root,
    _SpotV7SettlementCandidateInputV1,
    _validate_candidate,
)

SPOT_V7_COMMITTED_OUTPUT_UNBOUND_CANDIDATE_FIELDS_V1: Final = (
    "application_id",
    "chain_or_domain_id",
    "epoch_id",
    "exact_v7_receipt_bytes",
    "exact_firecracker_execution_record_bytes",
)

_REQUEST_BYTES_V1: Final = 192
_OUTPUT_BYTES_V1: Final = 16_777_216
_OUTPUT_HEADER_BYTES_V1: Final = 256
_OUTPUT_COMMIT_BYTES_V1: Final = 32
_OUTPUT_PAYLOAD_CAP_BYTES_V1: Final = 65_536
_REQUEST_MAGIC_V1: Final = b"ZRPFREQ1"
_OUTPUT_MAGIC_V1: Final = b"ZRPFOU01"
_OUTPUT_COMMIT_DOMAIN_V1: Final = b"zenodex/zrpf_firecracker_output_commit/v1\x00"
_CANDIDATE_PROFILE_CANONICAL_SHA256_V1: Final = bytes.fromhex(
    "e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e"
)
_PROTOCOL_VERSION_V1: Final = 1
_ACCEPTED_STATUS_V1: Final = 1

_V7_OUTPUT_MAGIC_V1: Final = b"ZSPTV7O1"
_V7_OUTPUT_VERSION_V1: Final = 1
_V7_OUTPUT_FIXED_FIELD_COUNT_V1: Final = 19
_V7_OUTPUT_HEADER_BYTES_V1: Final = 8 + 2 + 4 * 4 + 32 * _V7_OUTPUT_FIXED_FIELD_COUNT_V1

_V7_JOURNAL_MAGIC_V1: Final = b"ZSPTV7J1"
_V7_JOURNAL_VERSION_V1: Final = 1
_V7_JOURNAL_FIXED_FIELD_COUNT_V1: Final = 13
_V7_JOURNAL_HEADER_BYTES_V1: Final = 8 + 2 + 4 + 4 + 2 + 2 + 4
_V7_SEMANTIC_JOURNAL_BYTES_V1: Final = 2 + 8 * 32 + 48 + 4
_V7_EFFECT_BINDING_JOURNAL_BYTES_V1: Final = 2 + 12 * 32
_V7_MAX_PLAN_B_BYTES_V1: Final = 48 * 1_024
_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1: Final = (
    b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1"
)


class SpotV7CommittedOutputRejectV1(ValueError):
    """Stable fail-closed rejection for the data-only decoding boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class _DecodedCommittedSpotV7OutputV1:
    """Validated bytes and commitments from one committed output image.

    This value is data.  In particular, it is not evidence that the governed
    jailer, cgroup, network namespace, artifact set, or verifier executed.
    """

    request_sha256: bytes
    output_device_sha256: bytes
    output_payload_sha256: bytes
    output_payload_bytes: bytes
    journal_bytes: bytes
    plan_b_bytes: bytes
    fixed_fields: tuple[bytes, ...]
    journal_fixed_fields: tuple[bytes, ...]
    effect_binding_fixed_fields: tuple[bytes, ...]
    state_root_host_input_length: int


@dataclass(frozen=True, slots=True)
class _BoundCommittedSpotV7CandidateV1:
    """Exact byte-level join between one decoded output and one candidate.

    The application/domain/epoch preimages, retained receipt bytes, and jailed
    execution record are not independently present in the V7 output framing.
    Consequently this value cannot mint Firecracker or settlement authority.
    """

    decoded_output: _DecodedCommittedSpotV7OutputV1
    candidate: _SpotV7SettlementCandidateInputV1


def _decode_exact_committed_spot_v7_output_v1(
    *,
    request_bytes: bytes,
    output_device_bytes: bytes,
) -> _DecodedCommittedSpotV7OutputV1:
    """Decode one exact request-bound committed output device image."""

    request = _decode_request_v1(request_bytes)
    payload = _decode_committed_output_v1(output_device_bytes, request_bytes, request)
    (
        fixed_fields,
        journal_bytes,
        plan_b_bytes,
        journal_fixed_fields,
        effect_binding_fixed_fields,
        state_root_host_input_length,
    ) = _decode_spot_v7_payload_v1(payload)
    return _DecodedCommittedSpotV7OutputV1(
        request_sha256=hashlib.sha256(request_bytes).digest(),
        output_device_sha256=hashlib.sha256(output_device_bytes).digest(),
        output_payload_sha256=hashlib.sha256(payload).digest(),
        output_payload_bytes=payload,
        journal_bytes=journal_bytes,
        plan_b_bytes=plan_b_bytes,
        fixed_fields=fixed_fields,
        journal_fixed_fields=journal_fixed_fields,
        effect_binding_fixed_fields=effect_binding_fixed_fields,
        state_root_host_input_length=state_root_host_input_length,
    )


def _bind_decoded_spot_v7_output_to_candidate_v1(
    *,
    decoded_output: _DecodedCommittedSpotV7OutputV1,
    candidate: _SpotV7SettlementCandidateInputV1,
) -> _BoundCommittedSpotV7CandidateV1:
    """Bind all candidate fields that are explicitly committed by V7 output."""

    if type(decoded_output) is not _DecodedCommittedSpotV7OutputV1:
        raise TypeError("decoded_output must be exact _DecodedCommittedSpotV7OutputV1")
    if type(candidate) is not _SpotV7SettlementCandidateInputV1:
        raise TypeError("candidate must be exact _SpotV7SettlementCandidateInputV1")
    try:
        _validate_candidate(candidate)
    except (TypeError, ValueError) as exc:
        raise SpotV7CommittedOutputRejectV1("candidate_output_binding") from exc
    fixed = decoded_output.fixed_fields
    binding = decoded_output.effect_binding_fixed_fields
    expected = (
        (candidate.exact_firecracker_output_bytes, decoded_output.output_payload_bytes),
        (candidate.exact_v7_journal_bytes, decoded_output.journal_bytes),
        (candidate.exact_plan_b_bytes, decoded_output.plan_b_bytes),
        (_root_bytes(candidate.verified_program_id), fixed[0]),
        (_root_bytes(candidate.verified_profile_id), fixed[1]),
        (_root_bytes(candidate.verified_program_manifest_root), fixed[2]),
        (_root_bytes(candidate.source_child_claim_binding), fixed[6]),
        (_root_bytes(candidate.source_child_journal_sha256), fixed[7]),
        (_root_bytes(candidate.data_availability_certificate_root), fixed[8]),
        (_root_bytes(candidate.data_root), fixed[9]),
        (_root_bytes(candidate.settlement_effect_plan_commitment), fixed[10]),
        (hashlib.sha256(candidate.exact_plan_b_bytes).digest(), fixed[11]),
        (_root_bytes(candidate.pre_state_root), fixed[12]),
        (_root_bytes(candidate.post_state_root), fixed[13]),
        (_root_bytes(_candidate_action_ids_root(candidate)), fixed[14]),
        (
            _root_bytes(_candidate_action_authorization_bindings_root(candidate)),
            fixed[15],
        ),
        (
            _root_bytes(_candidate_authorization_grant_spends_root(candidate)),
            fixed[16],
        ),
        (_root_bytes(_candidate_consumed_object_ids_root(candidate)), fixed[17]),
        (_root_bytes(candidate.cell_transitions_root), binding[5]),
        (_root_bytes(candidate.economic_action_id), binding[8]),
    )
    if any(actual != committed for actual, committed in expected):
        raise SpotV7CommittedOutputRejectV1("candidate_output_binding")
    return _BoundCommittedSpotV7CandidateV1(decoded_output, candidate)


def _revalidate_bound_spot_v7_candidate_v1(
    value: _BoundCommittedSpotV7CandidateV1,
) -> _SpotV7SettlementCandidateInputV1:
    if type(value) is not _BoundCommittedSpotV7CandidateV1:
        raise TypeError("bound_output must be exact _BoundCommittedSpotV7CandidateV1")
    rebound = _bind_decoded_spot_v7_output_to_candidate_v1(
        decoded_output=value.decoded_output,
        candidate=value.candidate,
    )
    if rebound != value:
        raise SpotV7CommittedOutputRejectV1("candidate_output_binding")
    return value.candidate


def _decode_request_v1(raw: bytes) -> tuple[bytes, bytes, bytes]:
    _require_exact_bytes(raw, _REQUEST_BYTES_V1, "request")
    if raw[:8] != _REQUEST_MAGIC_V1:
        raise SpotV7CommittedOutputRejectV1("request_magic")
    version, header_bytes, flags = struct.unpack_from("<HHI", raw, 8)
    if version != _PROTOCOL_VERSION_V1 or header_bytes != _REQUEST_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("request_version")
    if flags != 0:
        raise SpotV7CommittedOutputRejectV1("request_flags")
    if raw[48:80] != _CANDIDATE_PROFILE_CANONICAL_SHA256_V1:
        raise SpotV7CommittedOutputRejectV1("request_profile")
    output_bytes, payload_cap = struct.unpack_from("<QI", raw, 144)
    if output_bytes != _OUTPUT_BYTES_V1 or payload_cap != _OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("request_output_bounds")
    if any(raw[188:]):
        raise SpotV7CommittedOutputRejectV1("request_reserved")
    for value in (raw[16:48], raw[80:112], raw[112:144], raw[156:188]):
        _require_nonzero_bytes32(value, "request_digest")
    return raw[16:48], raw[80:112], raw[112:144]


def _decode_committed_output_v1(
    raw: bytes,
    request_bytes: bytes,
    request: tuple[bytes, bytes, bytes],
) -> bytes:
    _require_exact_bytes(raw, _OUTPUT_BYTES_V1, "output")
    version, header_bytes, status, payload_length, reserved, output_bytes = (
        struct.unpack_from("<HHIIIQ", raw, 8)
    )
    if (
        raw[:8] != _OUTPUT_MAGIC_V1
        or version != _PROTOCOL_VERSION_V1
        or header_bytes != _OUTPUT_HEADER_BYTES_V1
        or status != _ACCEPTED_STATUS_V1
        or reserved != 0
        or output_bytes != _OUTPUT_BYTES_V1
        or any(raw[224:_OUTPUT_HEADER_BYTES_V1])
    ):
        raise SpotV7CommittedOutputRejectV1("output_header")
    nonce, runtime_manifest_sha256, input_drive_sha256 = request
    if (
        raw[32:64] != nonce
        or raw[64:96] != hashlib.sha256(request_bytes).digest()
        or raw[96:128] != input_drive_sha256
        or raw[128:160] != _CANDIDATE_PROFILE_CANONICAL_SHA256_V1
        or raw[160:192] != runtime_manifest_sha256
    ):
        raise SpotV7CommittedOutputRejectV1("output_binding")
    if not 0 < payload_length <= _OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("output_payload")
    payload_end = _OUTPUT_HEADER_BYTES_V1 + payload_length
    commit_offset = _OUTPUT_BYTES_V1 - _OUTPUT_COMMIT_BYTES_V1
    if payload_end > commit_offset:
        raise SpotV7CommittedOutputRejectV1("output_payload")
    payload = raw[_OUTPUT_HEADER_BYTES_V1:payload_end]
    if hashlib.sha256(payload).digest() != raw[192:224]:
        raise SpotV7CommittedOutputRejectV1("output_payload")
    if any(raw[payload_end:commit_offset]):
        raise SpotV7CommittedOutputRejectV1("output_trailing_bytes")
    marker = hashlib.sha256(
        _OUTPUT_COMMIT_DOMAIN_V1 + raw[:_OUTPUT_HEADER_BYTES_V1] + payload
    ).digest()
    if raw[commit_offset:] != marker:
        raise SpotV7CommittedOutputRejectV1("output_commit")
    return payload


def _decode_spot_v7_payload_v1(
    payload: bytes,
) -> tuple[
    tuple[bytes, ...],
    bytes,
    bytes,
    tuple[bytes, ...],
    tuple[bytes, ...],
    int,
]:
    if not _V7_OUTPUT_HEADER_BYTES_V1 < len(payload) <= _OUTPUT_PAYLOAD_CAP_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("v7_output_length")
    if payload[:8] != _V7_OUTPUT_MAGIC_V1:
        raise SpotV7CommittedOutputRejectV1("v7_output_magic")
    version = int.from_bytes(payload[8:10], "big")
    total = int.from_bytes(payload[10:14], "big")
    journal_length = int.from_bytes(payload[14:18], "big")
    declared_plan_length = int.from_bytes(payload[18:22], "big")
    host_input_length = int.from_bytes(payload[22:26], "big")
    if version != _V7_OUTPUT_VERSION_V1:
        raise SpotV7CommittedOutputRejectV1("v7_output_version")
    if (
        total != len(payload)
        or journal_length != len(payload) - _V7_OUTPUT_HEADER_BYTES_V1
        or not 0 < declared_plan_length <= _V7_MAX_PLAN_B_BYTES_V1
        or host_input_length == 0
    ):
        raise SpotV7CommittedOutputRejectV1("v7_output_framing")
    fixed = _read_nonzero_bytes32_fields(
        payload,
        offset=26,
        count=_V7_OUTPUT_FIXED_FIELD_COUNT_V1,
        code="v7_output_fixed_field",
    )
    journal = payload[_V7_OUTPUT_HEADER_BYTES_V1:]
    (
        plan,
        journal_fixed,
        binding_fixed,
        journal_host_input_length,
    ) = _decode_spot_v7_journal_v1(journal)
    if declared_plan_length != len(plan) or host_input_length != journal_host_input_length:
        raise SpotV7CommittedOutputRejectV1("v7_output_journal_binding")
    _require_v7_output_journal_associations(fixed, journal, journal_fixed, binding_fixed)
    return fixed, journal, plan, journal_fixed, binding_fixed, host_input_length


def _decode_spot_v7_journal_v1(
    journal: bytes,
) -> tuple[bytes, tuple[bytes, ...], tuple[bytes, ...], int]:
    minimum = (
        _V7_JOURNAL_HEADER_BYTES_V1
        + 32 * _V7_JOURNAL_FIXED_FIELD_COUNT_V1
        + _V7_SEMANTIC_JOURNAL_BYTES_V1
        + _V7_EFFECT_BINDING_JOURNAL_BYTES_V1
    )
    if not minimum < len(journal) <= minimum + _V7_MAX_PLAN_B_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("v7_journal_length")
    if journal[:8] != _V7_JOURNAL_MAGIC_V1:
        raise SpotV7CommittedOutputRejectV1("v7_journal_magic")
    version = int.from_bytes(journal[8:10], "big")
    total = int.from_bytes(journal[10:14], "big")
    host_input_length = int.from_bytes(journal[14:18], "big")
    semantic_length = int.from_bytes(journal[18:20], "big")
    binding_length = int.from_bytes(journal[20:22], "big")
    plan_length = int.from_bytes(journal[22:26], "big")
    if version != _V7_JOURNAL_VERSION_V1:
        raise SpotV7CommittedOutputRejectV1("v7_journal_version")
    if (
        total != len(journal)
        or host_input_length == 0
        or semantic_length != _V7_SEMANTIC_JOURNAL_BYTES_V1
        or binding_length != _V7_EFFECT_BINDING_JOURNAL_BYTES_V1
        or not 0 < plan_length <= _V7_MAX_PLAN_B_BYTES_V1
        or minimum + plan_length != len(journal)
    ):
        raise SpotV7CommittedOutputRejectV1("v7_journal_framing")
    fixed = _read_nonzero_bytes32_fields(
        journal,
        offset=_V7_JOURNAL_HEADER_BYTES_V1,
        count=_V7_JOURNAL_FIXED_FIELD_COUNT_V1,
        code="v7_journal_fixed_field",
    )
    cursor = _V7_JOURNAL_HEADER_BYTES_V1 + 32 * _V7_JOURNAL_FIXED_FIELD_COUNT_V1
    semantic = journal[cursor : cursor + semantic_length]
    cursor += semantic_length
    binding = journal[cursor : cursor + binding_length]
    cursor += binding_length
    plan = journal[cursor : cursor + plan_length]
    if hashlib.sha256(semantic).digest() != fixed[8]:
        raise SpotV7CommittedOutputRejectV1("v7_semantic_journal_hash")
    if _binding_journal_commitment(binding) != fixed[9]:
        raise SpotV7CommittedOutputRejectV1("v7_effect_binding_commitment")
    binding_fixed = _decode_effect_binding_journal_v1(binding)
    if binding_fixed[4] != fixed[10]:
        raise SpotV7CommittedOutputRejectV1("v7_plan_commitment_binding")
    if hashlib.sha256(plan).digest() != fixed[11]:
        raise SpotV7CommittedOutputRejectV1("v7_plan_bytes_sha256")
    return plan, fixed, binding_fixed, host_input_length


def _decode_effect_binding_journal_v1(binding: bytes) -> tuple[bytes, ...]:
    if len(binding) != _V7_EFFECT_BINDING_JOURNAL_BYTES_V1:
        raise SpotV7CommittedOutputRejectV1("v7_effect_binding_length")
    if int.from_bytes(binding[:2], "big") != 1:
        raise SpotV7CommittedOutputRejectV1("v7_effect_binding_version")
    return _read_nonzero_bytes32_fields(
        binding,
        offset=2,
        count=12,
        code="v7_effect_binding_field",
    )


def _require_v7_output_journal_associations(
    output: tuple[bytes, ...],
    journal: bytes,
    journal_fixed: tuple[bytes, ...],
    binding: tuple[bytes, ...],
) -> None:
    associations = (
        (output[3], hashlib.sha256(journal).digest()),
        (output[4], journal_fixed[0]),
        (output[5], journal_fixed[1]),
        (output[6], journal_fixed[2]),
        (output[7], journal_fixed[3]),
        (output[8], journal_fixed[4]),
        (output[9], journal_fixed[5]),
        (output[10], journal_fixed[10]),
        (output[11], journal_fixed[11]),
        (output[12], binding[6]),
        (output[13], binding[7]),
        (output[14], journal_fixed[12]),
        (output[18], journal_fixed[7]),
    )
    if any(actual != expected for actual, expected in associations):
        raise SpotV7CommittedOutputRejectV1("v7_output_journal_binding")


def _read_nonzero_bytes32_fields(
    raw: bytes,
    *,
    offset: int,
    count: int,
    code: str,
) -> tuple[bytes, ...]:
    fields = tuple(raw[offset + index * 32 : offset + (index + 1) * 32] for index in range(count))
    if len(fields) != count or any(len(field) != 32 or not any(field) for field in fields):
        raise SpotV7CommittedOutputRejectV1(code)
    return fields


def _binding_journal_commitment(binding: bytes) -> bytes:
    domain = _V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1
    return hashlib.sha256(len(domain).to_bytes(2, "big") + domain + binding).digest()


def _root_bytes(value: str) -> bytes:
    if type(value) is not str or not value.startswith("0x") or len(value) != 66:
        raise SpotV7CommittedOutputRejectV1("candidate_output_binding")
    try:
        raw = bytes.fromhex(value[2:])
    except ValueError as exc:
        raise SpotV7CommittedOutputRejectV1("candidate_output_binding") from exc
    _require_nonzero_bytes32(raw, "candidate_output_binding")
    return raw


def _require_exact_bytes(value: bytes, length: int, code: str) -> None:
    if type(value) is not bytes or len(value) != length:
        raise SpotV7CommittedOutputRejectV1(f"{code}_length")


def _require_nonzero_bytes32(value: bytes, code: str) -> None:
    if len(value) != 32 or not any(value):
        raise SpotV7CommittedOutputRejectV1(code)
