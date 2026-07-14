from __future__ import annotations

import hashlib
import inspect

import pytest

from src.integration._zrpf_spot_v7_firecracker_output import (
    SpotV7CommittedOutputRejectV1,
    _decode_spot_v7_payload_v1,
)
from tools import zrpf_spot_v7_firecracker_runtime_protocol as protocol
from tools import zrpf_spot_v7_verifier_payload_codec as payload_protocol


def test_profile_identity_is_spot_v7_specific_and_authority_false() -> None:
    retained_v3_profile = bytes.fromhex(
        "e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e"
    )

    assert protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1 != retained_v3_profile
    assert (
        hashlib.sha256(protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1).digest()
        == protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    )
    assert protocol.SPOT_V7_FIRECRACKER_RUNTIME_SETTLEMENT_AUTHORITY_V1 is False
    assert protocol.SPOT_V7_FIRECRACKER_RUNTIME_RELEASE_AUTHORITY_V1 is False
    assert protocol.SPOT_V7_FIRECRACKER_RUNTIME_PRODUCTION_READY_V1 is False

    source = inspect.getsource(protocol) + inspect.getsource(payload_protocol)
    assert "VerifiedReplayReport" not in source
    assert retained_v3_profile.hex() not in source


def test_request_vector_is_canonical_and_round_trips() -> None:
    request = _request()
    encoded = request.encode()

    assert len(encoded) == protocol.SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1
    assert protocol.decode_exact_request_v1(encoded) == request
    assert hashlib.sha256(encoded).hexdigest() == (
        "613519701cef6cde07f58ed97c10cedd60ec9a3c790efdab5824afb02ef27a36"
    )
    assert protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1.hex() == (
        "1b60e4bc78bc3ea3938f2ca72848418097208096574a1fc37e3404b841f36cd4"
    )


@pytest.mark.parametrize(
    ("offset", "value", "code"),
    [
        (0, 0, "request_magic"),
        (8, 2, "request_version"),
        (12, 1, "request_flags"),
        (48, 0, "request_profile"),
        (144, 1, "request_output_bounds"),
        (188, 1, "request_reserved"),
    ],
)
def test_request_mutations_reject_at_stable_boundaries(
    offset: int,
    value: int,
    code: str,
) -> None:
    changed = bytearray(_request().encode())
    changed[offset] = value

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as captured:
        protocol.decode_exact_request_v1(bytes(changed))

    assert captured.value.code == code


def test_request_rejects_wrong_type_width_and_zero_bindings() -> None:
    with pytest.raises(TypeError):
        protocol.SpotV7FirecrackerRequestV1()

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as zero_nonce:
        protocol.SpotV7FirecrackerRequestV1.validated(
            run_nonce_256=bytes(32),
            runtime_manifest_sha256=_digest(2),
            input_drive_sha256=_digest(3),
            settlement_intent_sha256=_digest(4),
        )
    assert zero_nonce.value.code == "request_nonce"

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as mutable:
        protocol.SpotV7FirecrackerRequestV1.validated(
            run_nonce_256=bytearray(_digest(1)),
            runtime_manifest_sha256=_digest(2),
            input_drive_sha256=_digest(3),
            settlement_intent_sha256=_digest(4),
        )
    assert mutable.value.code == "request_nonce"

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as short:
        protocol.decode_exact_request_v1(_request().encode()[:-1])
    assert short.value.code == "request_length"

    with pytest.raises(TypeError):
        protocol.StructurallyDecodedSpotV7VerifierPayloadV1()


def test_committed_output_vector_round_trips_and_binds_exact_v7_payload() -> None:
    payload = _valid_v7_payload()
    request = _request()
    output = protocol.build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=payload,
    )

    decoded = protocol.validate_exact_committed_output_v1(output, request)

    assert decoded.raw_bytes == payload
    assert decoded.plan_b_bytes == b"canonical-plan-b-v1"
    assert decoded.state_root_host_input_length == 1_024
    assert decoded.payload_sha256 == hashlib.sha256(payload).digest()
    assert hashlib.sha256(output).hexdigest() == (
        "4c6620737cc4b8f9153ccd6f014666ebed823692afffa7278f0a60bb5e7cf3f6"
    )


@pytest.mark.parametrize(
    "field",
    [
        "run_nonce_256",
        "runtime_manifest_sha256",
        "input_drive_sha256",
        "settlement_intent_sha256",
    ],
)
def test_committed_output_rejects_stale_request_binding(field: str) -> None:
    request = _request()
    output = protocol.build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=_valid_v7_payload(),
    )
    values = {
        "run_nonce_256": request.run_nonce_256,
        "runtime_manifest_sha256": request.runtime_manifest_sha256,
        "input_drive_sha256": request.input_drive_sha256,
        "settlement_intent_sha256": request.settlement_intent_sha256,
    }
    values[field] = hashlib.sha256(field.encode("ascii")).digest()
    stale = protocol.SpotV7FirecrackerRequestV1.validated(**values)

    _assert_output_reject(output, stale, "output_binding")


def test_committed_output_rejects_torn_marker_payload_and_trailing_data() -> None:
    request = _request()
    payload = _valid_v7_payload()
    output = bytearray(
        protocol.build_data_only_committed_output_v1(
            request,
            observed_input_drive_sha256=request.input_drive_sha256,
            payload=payload,
        )
    )

    output[-1] ^= 1
    _assert_output_reject(output, request, "output_commit")
    output[-1] ^= 1

    output[protocol.SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1] ^= 1
    _assert_output_reject(output, request, "output_payload")
    output[protocol.SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1] ^= 1

    trailing_offset = protocol.SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1 + len(payload) + 1
    output[trailing_offset] = 1
    _assert_output_reject(output, request, "output_trailing_bytes")


def test_committed_output_rejects_truncation_and_uncommitted_zero_image() -> None:
    request = _request()
    output = protocol.build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=_valid_v7_payload(),
    )

    _assert_output_reject(output[:-1], request, "output_length")
    _assert_output_reject(
        bytes(protocol.SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1),
        request,
        "output_header",
    )


@pytest.mark.parametrize("offset", [0, 8, 12, 20, 24])
def test_committed_output_rejects_structural_header_mutations(offset: int) -> None:
    request = _request()
    output = bytearray(_committed_output(request))
    output[offset] ^= 1

    _assert_output_reject(output, request, "output_header")


@pytest.mark.parametrize("offset", [32, 64, 96, 128, 160, 192])
def test_committed_output_rejects_direct_header_binding_mutations(offset: int) -> None:
    request = _request()
    output = bytearray(_committed_output(request))
    output[offset] ^= 1

    _assert_output_reject(output, request, "output_binding")


def test_structure_preserving_nested_mutation_reaches_v7_reject_after_outer_recommit() -> None:
    request = _request()
    output = bytearray(_committed_output(request))
    payload_length = int.from_bytes(output[16:20], "little")
    payload_start = protocol.SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1
    output[payload_start + payload_length - 1] ^= 1
    _recommit_output(output, request, payload_length)

    _assert_output_reject(output, request, "v7_plan_bytes_sha256")


def test_builder_rejects_observed_input_substitution() -> None:
    request = _request()

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as captured:
        protocol.build_data_only_committed_output_v1(
            request,
            observed_input_drive_sha256=_digest(9),
            payload=_valid_v7_payload(),
        )

    assert captured.value.code == "output_binding"


@pytest.mark.parametrize(
    ("offset", "code"),
    [
        (0, "v7_output_magic"),
        (8, "v7_output_version"),
        (10, "v7_output_framing"),
        (14, "v7_output_framing"),
    ],
)
def test_v7_payload_header_mutations_reject(offset: int, code: str) -> None:
    payload = bytearray(_valid_v7_payload())
    payload[offset] ^= 1

    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as captured:
        protocol.decode_structural_v7_verifier_payload_v1(bytes(payload))

    assert captured.value.code == code


def test_v7_payload_rejects_zero_host_length_and_zero_fixed_field() -> None:
    payload = bytearray(_valid_v7_payload())
    payload[22:26] = bytes(4)
    _assert_payload_reject(payload, "v7_output_framing")

    payload = bytearray(_valid_v7_payload())
    payload[26:58] = bytes(32)
    _assert_payload_reject(payload, "v7_output_fixed_field")


def test_v7_payload_rejects_nested_journal_and_plan_binding_mutations() -> None:
    payload = bytearray(_valid_v7_payload())
    journal_offset = payload_protocol.SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1

    payload[journal_offset] ^= 1
    _assert_payload_reject(payload, "v7_journal_magic")
    payload[journal_offset] ^= 1

    semantic_offset = journal_offset + payload_protocol.SPOT_V7_JOURNAL_HEADER_BYTES_V1 + 13 * 32
    payload[semantic_offset] ^= 1
    _assert_payload_reject(payload, "v7_semantic_journal_hash")
    payload[semantic_offset] ^= 1

    payload[-1] ^= 1
    _assert_payload_reject(payload, "v7_plan_bytes_sha256")


def test_v7_payload_rejects_outer_to_journal_association_mutation() -> None:
    payload = bytearray(_valid_v7_payload())
    journal_digest_offset = 26 + 3 * 32
    payload[journal_digest_offset] ^= 1

    _assert_payload_reject(payload, "v7_output_journal_binding")


def test_v7_payload_codec_matches_existing_candidate_decoder() -> None:
    payload = _valid_v7_payload()
    decoded = protocol.decode_structural_v7_verifier_payload_v1(payload)
    existing = _decode_spot_v7_payload_v1(payload)

    assert existing == (
        decoded.fixed_fields,
        decoded.journal_bytes,
        decoded.plan_b_bytes,
        decoded.journal_fixed_fields,
        decoded.effect_binding_fixed_fields,
        decoded.state_root_host_input_length,
    )


def test_v7_payload_negative_corpus_has_existing_decoder_reject_parity() -> None:
    mutations = (
        _mutated_payload(0),
        _mutated_payload(10),
        _mutated_payload(payload_protocol.SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1),
        _mutated_payload(-1),
    )
    for payload in mutations:
        with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as current:
            protocol.decode_structural_v7_verifier_payload_v1(payload)
        with pytest.raises(SpotV7CommittedOutputRejectV1) as existing:
            _decode_spot_v7_payload_v1(payload)
        assert current.value.code == existing.value.code


def _request() -> protocol.SpotV7FirecrackerRequestV1:
    return protocol.SpotV7FirecrackerRequestV1.validated(
        run_nonce_256=_digest(1),
        runtime_manifest_sha256=_digest(2),
        input_drive_sha256=_digest(3),
        settlement_intent_sha256=_digest(4),
    )


def _committed_output(request: protocol.SpotV7FirecrackerRequestV1) -> bytes:
    return protocol.build_data_only_committed_output_v1(
        request,
        observed_input_drive_sha256=request.input_drive_sha256,
        payload=_valid_v7_payload(),
    )


def _mutated_payload(offset: int) -> bytes:
    payload = bytearray(_valid_v7_payload())
    payload[offset] ^= 1
    return bytes(payload)


def _valid_v7_payload() -> bytes:
    plan = b"canonical-plan-b-v1"
    journal, journal_fields, binding_fields = _valid_v7_journal(plan)
    output_fields = _valid_v7_output_fields(journal, journal_fields, binding_fields)
    payload_total = payload_protocol.SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1 + len(journal)
    return b"".join(
        (
            payload_protocol.SPOT_V7_VERIFIER_OUTPUT_MAGIC_V1,
            (1).to_bytes(2, "big"),
            payload_total.to_bytes(4, "big"),
            len(journal).to_bytes(4, "big"),
            len(plan).to_bytes(4, "big"),
            (1_024).to_bytes(4, "big"),
            *output_fields,
            journal,
        )
    )


def _valid_v7_journal(
    plan: bytes,
) -> tuple[bytes, tuple[bytes, ...], tuple[bytes, ...]]:
    semantic = bytes([0x61]) * payload_protocol.SPOT_V7_SEMANTIC_JOURNAL_BYTES_V1
    binding_fields = tuple(_field(f"binding-{index}") for index in range(12))
    binding = b"\x00\x01" + b"".join(binding_fields)
    binding_commitment = hashlib.sha256(
        len(payload_protocol.SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1).to_bytes(2, "big")
        + payload_protocol.SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1
        + binding
    ).digest()
    journal_fields = (
        _field("source-program"),
        _field("source-profile"),
        _field("source-claim"),
        _field("source-journal"),
        _field("da-certificate"),
        _field("data-root"),
        _field("host-input-binding"),
        _field("host-input-sha256"),
        hashlib.sha256(semantic).digest(),
        binding_commitment,
        binding_fields[4],
        hashlib.sha256(plan).digest(),
        _field("action-ids-root"),
    )
    host_input_length = 1_024
    journal_total = (
        payload_protocol.SPOT_V7_JOURNAL_HEADER_BYTES_V1
        + len(journal_fields) * 32
        + len(semantic)
        + len(binding)
        + len(plan)
    )
    journal = b"".join(
        (
            payload_protocol.SPOT_V7_JOURNAL_MAGIC_V1,
            (1).to_bytes(2, "big"),
            journal_total.to_bytes(4, "big"),
            host_input_length.to_bytes(4, "big"),
            len(semantic).to_bytes(2, "big"),
            len(binding).to_bytes(2, "big"),
            len(plan).to_bytes(4, "big"),
            *journal_fields,
            semantic,
            binding,
            plan,
        )
    )
    return journal, journal_fields, binding_fields


def _valid_v7_output_fields(
    journal: bytes,
    journal_fields: tuple[bytes, ...],
    binding_fields: tuple[bytes, ...],
) -> tuple[bytes, ...]:
    return (
        _field("verified-program"),
        _field("verified-profile"),
        _field("program-manifest"),
        hashlib.sha256(journal).digest(),
        journal_fields[0],
        journal_fields[1],
        journal_fields[2],
        journal_fields[3],
        journal_fields[4],
        journal_fields[5],
        journal_fields[10],
        journal_fields[11],
        binding_fields[6],
        binding_fields[7],
        journal_fields[12],
        _field("authorization-bindings"),
        _field("grant-spends"),
        _field("consumed-objects"),
        journal_fields[7],
    )


def _field(label: str) -> bytes:
    return hashlib.sha256(label.encode("ascii")).digest()


def _digest(fill: int) -> bytes:
    return bytes([fill]) * 32


def _assert_output_reject(
    raw: bytes | bytearray,
    request: protocol.SpotV7FirecrackerRequestV1,
    code: str,
) -> None:
    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as captured:
        protocol.validate_exact_committed_output_v1(bytes(raw), request)
    assert captured.value.code == code


def _assert_payload_reject(raw: bytes | bytearray, code: str) -> None:
    with pytest.raises(protocol.SpotV7FirecrackerProtocolRejectV1) as captured:
        protocol.decode_structural_v7_verifier_payload_v1(bytes(raw))
    assert captured.value.code == code


def _recommit_output(
    output: bytearray,
    request: protocol.SpotV7FirecrackerRequestV1,
    payload_length: int,
) -> None:
    payload_start = protocol.SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1
    payload = bytes(output[payload_start : payload_start + payload_length])
    output[224:256] = hashlib.sha256(payload).digest()
    header = bytes(output[:payload_start])
    output[-protocol.SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1 :] = hashlib.sha256(
        protocol.SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_DOMAIN_V1
        + protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        + request.sha256
        + header
        + payload
    ).digest()
