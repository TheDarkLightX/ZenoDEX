"""One-provider response authentication for sampled retrievability V1."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from src.integration.zeno_ledger_signature import (
    validate_bls_signed_artifact_envelope_v0,
)

from .codec import (
    SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
    decode_exact_response_document_v1,
    response_payload_hash_v1,
)
from .errors import reject
from .hashing import (
    chunk_hash_vector_sha256_v1,
    chunk_leaf_hash_v1,
    derive_challenge_indices_v1,
    expected_chunk_length_v1,
)
from .model import (
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    SampledRetrievabilityPolicyV1,
    require_token,
    require_u64,
)
from .validation import checked_add, exact_equal, require_list


@dataclass(frozen=True, slots=True)
class _ResponseVerificationContextV1:
    policy: SampledRetrievabilityPolicyV1
    target: FullBlobRetrievabilityTargetV1
    beacon: BeaconCommitmentV1
    checked_epoch: int
    ordered_chunk_hashes: tuple[str, ...]


def verify_provider_responses_v1(
    records: list[object],
    *,
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
    ordered_chunk_hashes: tuple[str, ...],
) -> tuple[str, ...]:
    context = _ResponseVerificationContextV1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=checked_epoch,
        ordered_chunk_hashes=ordered_chunk_hashes,
    )
    if len(records) > len(policy.providers):
        reject("PROVIDER_RESPONSE_LIMIT", "provider response count exceeds policy records")
    seen_provider_ids: set[str] = set()
    seen_public_keys: set[str] = set()
    accepted: list[str] = []
    previous_identity: tuple[str, str] | None = None
    for index, raw_record in enumerate(records):
        record = _require_exact_record(raw_record, index)
        response_bytes = _decode_response_hex(record, index)
        response = _decode_response(response_bytes)
        provider_id = _response_token(response, "provider_id")
        key_id = _response_token(response, "key_id")
        identity = (provider_id, key_id)
        if provider_id in seen_provider_ids:
            reject("DUPLICATE_PROVIDER", "provider identity appears more than once")
        if previous_identity is not None and identity <= previous_identity:
            reject("RESPONSE_ORDER_MISMATCH", "provider responses are not canonically ordered")
        previous_identity = identity
        provider = policy.find_provider(provider_id, key_id)
        if provider is None:
            reject("PROVIDER_NOT_ACTIVE", "provider key is absent from policy")
        response_epoch = _response_u64(response, "response_epoch")
        if not policy.is_active_at(response_epoch):
            reject("POLICY_NOT_ACTIVE", "retrievability policy is inactive at response epoch")
        if not provider.is_active_at(checked_epoch) or not provider.is_active_at(response_epoch):
            reject("PROVIDER_NOT_ACTIVE", "provider key is inactive for the sampled response")
        if provider.public_key in seen_public_keys:
            reject("DUPLICATE_PROVIDER", "provider public key appears more than once")
        _require_response_bindings(response, context, provider_id, key_id)
        _verify_response_signature(
            record,
            response_bytes,
            provider_id,
            key_id,
            provider.public_key,
        )
        seen_provider_ids.add(provider_id)
        seen_public_keys.add(provider.public_key)
        accepted.append(provider_id)
    return tuple(accepted)


def _decode_response(response_bytes: bytes) -> dict[str, object]:
    try:
        return decode_exact_response_document_v1(response_bytes)
    except (TypeError, ValueError):
        reject("NONCANONICAL_RESPONSE", "provider response bytes are not exact V1 JSON")


def _require_response_bindings(
    response: dict[str, object],
    context: _ResponseVerificationContextV1,
    provider_id: str,
    key_id: str,
) -> None:
    policy = context.policy
    target = context.target
    checked_epoch = context.checked_epoch
    deadline = checked_add(checked_epoch, policy.response_window_epochs, "response deadline")
    response_epoch = _response_u64(response, "response_epoch")
    fixed = {
        "application_id": target.application_id,
        "beacon": context.beacon.to_document(),
        "certificate_root": target.certificate_root,
        "chain_or_domain_id": target.chain_or_domain_id,
        "checked_epoch": checked_epoch,
        "chunk_hash_vector_sha256": chunk_hash_vector_sha256_v1(
            context.ordered_chunk_hashes
        ),
        "chunk_root": target.chunk_root,
        "data_root": target.data_root,
        "epoch_id": target.epoch_id,
        "key_id": key_id,
        "policy_root": policy.policy_root,
        "provider_id": provider_id,
        "response_deadline_epoch": deadline,
        "retention_through_epoch": target.retention_through_epoch,
        "storage_policy_hash": target.storage_policy_hash,
    }
    if any(not exact_equal(response.get(field), value) for field, value in fixed.items()):
        reject("RESPONSE_BINDING_MISMATCH", "provider response scope binding mismatch")
    if response_epoch < checked_epoch or response_epoch > deadline:
        reject("RESPONSE_DEADLINE_EXCEEDED", "provider response is outside the response window")
    expected_indices = derive_challenge_indices_v1(
        policy,
        target,
        context.beacon,
        provider_id,
    )
    assigned = _require_index_list(
        response.get("assigned_chunk_indices"),
        expected_count=policy.challenge_count,
    )
    if assigned != expected_indices:
        reject("CHALLENGE_INDICES_MISMATCH", "provider challenge indices are not deterministic")
    _require_openings(
        response.get("openings"),
        expected_indices,
        target,
        context.ordered_chunk_hashes,
    )


def _require_openings(
    raw: object,
    expected_indices: tuple[int, ...],
    target: FullBlobRetrievabilityTargetV1,
    ordered_chunk_hashes: tuple[str, ...],
) -> None:
    openings = require_list(raw, name="response openings")
    if len(openings) != len(expected_indices):
        reject("CHUNK_OPENING_MISMATCH", "opening count differs from challenge count")
    for offset, expected_index in enumerate(expected_indices):
        opening = openings[offset]
        if type(opening) is not dict or set(opening) != {"chunk_bytes_hex", "chunk_index"}:
            reject("CHUNK_OPENING_MISMATCH", "chunk opening fields mismatch")
        observed_index = opening.get("chunk_index")
        if type(observed_index) is not int or observed_index != expected_index:
            reject("CHUNK_OPENING_MISMATCH", "chunk opening index mismatch")
        chunk = _decode_chunk_bytes(opening.get("chunk_bytes_hex"))
        if len(chunk) != expected_chunk_length_v1(target, expected_index):
            reject("CHUNK_OPENING_MISMATCH", "chunk opening length mismatch")
        if chunk_leaf_hash_v1(expected_index, chunk) != ordered_chunk_hashes[expected_index]:
            reject("CHUNK_OPENING_MISMATCH", "chunk opening does not match committed leaf")


def _decode_chunk_bytes(value: object) -> bytes:
    if type(value) is not str or len(value) % 2 != 0:
        reject("CHUNK_OPENING_MISMATCH", "chunk opening bytes are not canonical hex")
    try:
        chunk = bytes.fromhex(value)
    except ValueError:
        reject("CHUNK_OPENING_MISMATCH", "chunk opening bytes are invalid hex")
    if chunk.hex() != value:
        reject("CHUNK_OPENING_MISMATCH", "chunk opening hex is noncanonical")
    return chunk


def _verify_response_signature(
    record: dict[str, object],
    response_bytes: bytes,
    expected_provider_id: str,
    expected_key_id: str,
    expected_public_key: str,
) -> None:
    envelope = record.get("signature_envelope")
    if type(envelope) is not dict:
        reject("SIGNATURE_INVALID", "signature envelope must be an exact object")
    if envelope.get("signer_id") != expected_provider_id or (
        envelope.get("key_id") != expected_key_id
    ):
        reject("SIGNATURE_INVALID", "signature envelope provider binding mismatch")
    try:
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind=SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
            expected_payload_hash=response_payload_hash_v1(response_bytes),
            expected_public_key=expected_public_key,
        )
    except (TypeError, ValueError, RuntimeError):
        reject("SIGNATURE_INVALID", "provider BLS signature verification failed")


def _require_exact_record(value: object, index: int) -> dict[str, object]:
    if type(value) is not dict or set(value) != {
        "response_bytes_hex",
        "signature_envelope",
    }:
        reject("RESPONSE_RECORD_INVALID", f"responses[{index}] fields mismatch")
    return value


def _decode_response_hex(record: Mapping[str, object], index: int) -> bytes:
    value = record.get("response_bytes_hex")
    if type(value) is not str or len(value) % 2 != 0:
        reject("NONCANONICAL_RESPONSE", f"responses[{index}] bytes are not canonical hex")
    try:
        result = bytes.fromhex(value)
    except ValueError:
        reject("NONCANONICAL_RESPONSE", f"responses[{index}] bytes are invalid hex")
    if result.hex() != value:
        reject("NONCANONICAL_RESPONSE", f"responses[{index}] hex is noncanonical")
    return result


def _response_token(response: Mapping[str, object], field: str) -> str:
    try:
        return require_token(response.get(field), name=f"response {field}")
    except (TypeError, ValueError):
        reject("RESPONSE_BINDING_MISMATCH", f"response {field} is invalid")


def _response_u64(response: Mapping[str, object], field: str) -> int:
    try:
        return require_u64(response.get(field), name=f"response {field}")
    except (TypeError, ValueError):
        reject("RESPONSE_BINDING_MISMATCH", f"response {field} is invalid")


def _require_index_list(value: object, *, expected_count: int) -> tuple[int, ...]:
    values = require_list(value, name="assigned_chunk_indices")
    if len(values) != expected_count:
        reject("CHALLENGE_INDICES_MISMATCH", "challenge index count differs from policy")
    result: list[int] = []
    for index, raw in enumerate(values):
        if type(raw) is not int or raw < 0:
            reject("CHALLENGE_INDICES_MISMATCH", f"challenge index {index} is invalid")
        result.append(raw)
    return tuple(result)
