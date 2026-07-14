"""Canonical response and evidence codecs for sampled retrievability V1."""

from __future__ import annotations

import hashlib
import json
from typing import Final, Mapping, NoReturn

from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0

from .hashing import (
    chunk_bytes_at_v1,
    chunk_hash_vector_sha256_v1,
    derive_challenge_indices_v1,
    verify_exact_blob_matches_target_v1,
)
from .model import (
    MAX_EXACT_EVIDENCE_BYTES_V1,
    MAX_EXACT_RESPONSE_BYTES_V1,
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    SampledRetrievabilityPolicyV1,
    SignedProviderResponseV1,
    require_token,
    require_u64,
)

SAMPLED_RETRIEVABILITY_RESPONSE_SCHEMA_V1: Final = (
    "zenodex.zrpf.sampled_retrievability_response.v1"
)
SAMPLED_RETRIEVABILITY_EVIDENCE_SCHEMA_V1: Final = (
    "zenodex.zrpf.sampled_retrievability_evidence.v1"
)
SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1: Final = (
    "zrpf_sampled_retrievability_response"
)

AUTHORITY_CLAIMS_V1: Final = {
    "authenticated_sampled_response_scoped_to_checked_epoch": True,
    "governed_policy_provenance_verified": False,
    "governed_beacon_provenance_verified": False,
    "beacon_unpredictability_verified": False,
    "response_timing_provenance_verified": False,
    "provider_independence_verified": False,
    "continuous_availability_verified": False,
    "public_future_availability_verified": False,
    "release_authority": False,
    "settlement_authority": False,
    "production_authority": False,
}

_RESPONSE_FIELDS_V1: Final = frozenset(
    {
        "application_id",
        "assigned_chunk_indices",
        "beacon",
        "certificate_root",
        "chain_or_domain_id",
        "checked_epoch",
        "chunk_hash_vector_sha256",
        "chunk_root",
        "data_root",
        "epoch_id",
        "key_id",
        "openings",
        "policy_root",
        "provider_id",
        "response_deadline_epoch",
        "response_epoch",
        "retention_through_epoch",
        "schema",
        "storage_policy_hash",
    }
)
_EVIDENCE_FIELDS_V1: Final = frozenset(
    {
        "authority",
        "beacon",
        "checked_epoch",
        "full_blob_target",
        "ordered_chunk_hashes",
        "policy_root",
        "responses",
        "schema",
    }
)


def build_provider_response_bytes_v1(
    *,
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
    response_epoch: int,
    provider_id: str,
    key_id: str,
    exact_blob_bytes: bytes,
) -> bytes:
    """Build one provider proposal; lifecycle and signature checks occur later."""

    _require_exact_inputs(policy, target, beacon)
    checked = require_u64(checked_epoch, name="checked_epoch")
    responded = require_u64(response_epoch, name="response_epoch")
    provider = require_token(provider_id, name="provider_id")
    key = require_token(key_id, name="key_id")
    if policy.find_provider(provider, key) is None:
        raise ValueError("provider response identity is absent from the policy")
    _require_scope_binding(policy, target, beacon)
    chunk_hashes = verify_exact_blob_matches_target_v1(target, exact_blob_bytes)
    indices = derive_challenge_indices_v1(policy, target, beacon, provider)
    deadline = checked + policy.response_window_epochs
    if deadline > (1 << 64) - 1:
        raise ValueError("response deadline overflows u64")
    body = {
        "application_id": target.application_id,
        "assigned_chunk_indices": list(indices),
        "beacon": beacon.to_document(),
        "certificate_root": target.certificate_root,
        "chain_or_domain_id": target.chain_or_domain_id,
        "checked_epoch": checked,
        "chunk_hash_vector_sha256": chunk_hash_vector_sha256_v1(chunk_hashes),
        "chunk_root": target.chunk_root,
        "data_root": target.data_root,
        "epoch_id": target.epoch_id,
        "key_id": key,
        "openings": [
            {
                "chunk_bytes_hex": chunk_bytes_at_v1(exact_blob_bytes, index).hex(),
                "chunk_index": index,
            }
            for index in indices
        ],
        "policy_root": policy.policy_root,
        "provider_id": provider,
        "response_deadline_epoch": deadline,
        "response_epoch": responded,
        "retention_through_epoch": target.retention_through_epoch,
        "schema": SAMPLED_RETRIEVABILITY_RESPONSE_SCHEMA_V1,
        "storage_policy_hash": target.storage_policy_hash,
    }
    raw = canonical_json_bytes_v0(body)
    if len(raw) > MAX_EXACT_RESPONSE_BYTES_V1:
        raise ValueError("provider response exceeds the V1 byte bound")
    return raw


def response_payload_hash_v1(exact_response_bytes: bytes) -> str:
    """Hash exact canonical response bytes for the existing BLS envelope."""

    decode_exact_response_document_v1(exact_response_bytes)
    return hash_v0(
        "zrpf_sampled_retrievability_response_payload_v1",
        exact_response_bytes,
    )


def build_exact_evidence_bytes_v1(
    *,
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
    exact_blob_bytes: bytes,
    signed_responses: tuple[SignedProviderResponseV1, ...],
) -> bytes:
    """Build canonical evidence bytes without making an authority decision."""

    _require_exact_inputs(policy, target, beacon)
    checked = require_u64(checked_epoch, name="checked_epoch")
    _require_scope_binding(policy, target, beacon)
    chunk_hashes = verify_exact_blob_matches_target_v1(target, exact_blob_bytes)
    if type(signed_responses) is not tuple or not signed_responses:
        raise TypeError("signed_responses must be a nonempty tuple")
    records: list[tuple[tuple[str, str], dict[str, object]]] = []
    for index, response in enumerate(signed_responses):
        if type(response) is not SignedProviderResponseV1:
            raise TypeError("signed_responses must contain exact response proposals")
        document = decode_exact_response_document_v1(response.response_bytes)
        identity = (
            _require_response_token(document, "provider_id"),
            _require_response_token(document, "key_id"),
        )
        records.append(
            (
                identity,
                {
                    "response_bytes_hex": response.response_bytes.hex(),
                    "signature_envelope": _plain_mapping_copy(
                        response.signature_envelope,
                        name=f"signed_responses[{index}].signature_envelope",
                    ),
                },
            )
        )
    records.sort(key=lambda item: item[0])
    body = {
        "authority": dict(AUTHORITY_CLAIMS_V1),
        "beacon": beacon.to_document(),
        "checked_epoch": checked,
        "full_blob_target": target.to_document(),
        "ordered_chunk_hashes": list(chunk_hashes),
        "policy_root": policy.policy_root,
        "responses": [record for _, record in records],
        "schema": SAMPLED_RETRIEVABILITY_EVIDENCE_SCHEMA_V1,
    }
    raw = canonical_json_bytes_v0(body)
    if len(raw) > MAX_EXACT_EVIDENCE_BYTES_V1:
        raise ValueError("sampled retrievability evidence exceeds the V1 byte bound")
    return raw


def decode_exact_evidence_document_v1(raw: bytes) -> dict[str, object]:
    document = _decode_exact_json_object(
        raw,
        maximum=MAX_EXACT_EVIDENCE_BYTES_V1,
        name="sampled retrievability evidence",
    )
    _require_exact_fields(document, _EVIDENCE_FIELDS_V1, "evidence")
    return document


def decode_exact_response_document_v1(raw: bytes) -> dict[str, object]:
    document = _decode_exact_json_object(
        raw,
        maximum=MAX_EXACT_RESPONSE_BYTES_V1,
        name="sampled retrievability response",
    )
    _require_exact_fields(document, _RESPONSE_FIELDS_V1, "response")
    if document.get("schema") != SAMPLED_RETRIEVABILITY_RESPONSE_SCHEMA_V1:
        raise ValueError("sampled retrievability response schema mismatch")
    return document


def exact_evidence_sha256_v1(raw: bytes) -> str:
    decode_exact_evidence_document_v1(raw)
    return hashlib.sha256(raw).hexdigest()


def _decode_exact_json_object(raw: bytes, *, maximum: int, name: str) -> dict[str, object]:
    if type(raw) is not bytes or not 1 <= len(raw) <= maximum:
        raise ValueError(f"{name} bytes are empty or oversized")
    try:
        decoded = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ValueError(f"{name} is not exact bounded JSON") from exc
    if type(decoded) is not dict:
        raise ValueError(f"{name} must be a JSON object")
    if canonical_json_bytes_v0(decoded) != raw:
        raise ValueError(f"{name} is not canonical JSON")
    return decoded


def _require_exact_fields(
    value: Mapping[str, object],
    expected: frozenset[str],
    name: str,
) -> None:
    if set(value) != expected:
        raise ValueError(f"{name} fields mismatch")


def _require_exact_inputs(
    policy: object,
    target: object,
    beacon: object,
) -> None:
    if type(policy) is not SampledRetrievabilityPolicyV1:
        raise TypeError("sampled retrievability policy has the wrong type")
    if type(target) is not FullBlobRetrievabilityTargetV1:
        raise TypeError("full-blob target has the wrong type")
    if type(beacon) is not BeaconCommitmentV1:
        raise TypeError("beacon commitment has the wrong type")


def _require_scope_binding(
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
) -> None:
    if policy.application_id != target.application_id:
        raise ValueError("policy/full-blob application mismatch")
    if policy.chain_or_domain_id != target.chain_or_domain_id:
        raise ValueError("policy/full-blob domain mismatch")
    if policy.storage_policy_hash != target.storage_policy_hash:
        raise ValueError("policy/full-blob storage policy mismatch")
    if policy.beacon_source_id != beacon.source_id:
        raise ValueError("policy/beacon source mismatch")
    if policy.beacon_policy_hash != beacon.policy_hash:
        raise ValueError("policy/beacon policy mismatch")


def _require_response_token(document: Mapping[str, object], field: str) -> str:
    return require_token(document.get(field), name=f"response {field}")


def _plain_mapping_copy(value: Mapping[str, object], *, name: str) -> dict[str, object]:
    try:
        raw = canonical_json_bytes_v0(dict(value))
        decoded = json.loads(raw)
    except (TypeError, ValueError, RecursionError) as exc:
        raise ValueError(f"{name} is not canonical plain JSON") from exc
    if type(decoded) is not dict:
        raise ValueError(f"{name} must be an object")
    return decoded


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_float(value: str) -> NoReturn:
    raise ValueError(f"JSON floats are forbidden: {value}")


def _reject_nonfinite(value: str) -> NoReturn:
    raise ValueError(f"JSON constants are forbidden: {value}")
