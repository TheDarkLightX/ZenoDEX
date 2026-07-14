"""Exact full-blob and deterministic challenge hashing for retrievability V1."""

from __future__ import annotations

import hashlib
from typing import Final

from src.integration.zeno_ledger_v0 import hash_v0

from .model import (
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    SampledRetrievabilityPolicyV1,
    require_root,
    require_token,
    require_u64,
)

FULL_BLOB_CHUNK_BYTES_V1: Final = 65_536
MAX_FULL_BLOB_BYTES_V1: Final = 8 * 1_024 * 1_024
MAX_FULL_BLOB_CHUNKS_V1: Final = 128

_DATA_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.full_blob_da.data_root.v1"
_CHUNK_HASH_DOMAIN_V1: Final = b"zenodex.zrpf.full_blob_da.chunk.v1"
_CHUNK_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.full_blob_da.chunk_root.v1"
_CERTIFICATE_ROOT_DOMAIN_V1: Final = b"zenodex.zrpf.full_blob_da.certificate_root.v1"
_CHALLENGE_DOMAIN_V1: Final = b"zenodex.zrpf.sampled_retrievability.challenge.v1"


def derive_exact_full_blob_target_v1(
    *,
    application_id: str,
    chain_or_domain_id: str,
    epoch_id: int,
    data_schema_id: str,
    exact_blob_bytes: bytes,
    retention_through_epoch: int,
    storage_policy_hash: str,
) -> FullBlobRetrievabilityTargetV1:
    """Independently derive the existing full-blob V1 commitment ABI."""

    application = require_root(application_id, name="full-blob application_id")
    domain = require_root(chain_or_domain_id, name="full-blob chain_or_domain_id")
    schema = require_root(data_schema_id, name="full-blob data_schema_id")
    storage = require_root(storage_policy_hash, name="full-blob storage_policy_hash")
    epoch = require_u64(epoch_id, name="full-blob epoch_id")
    retention = require_u64(
        retention_through_epoch,
        name="full-blob retention_through_epoch",
    )
    if retention < epoch:
        raise ValueError("full-blob retention ends before its epoch")
    blob = _require_exact_blob(exact_blob_bytes)
    data_root = _derive_data_root(blob)
    chunk_hashes = derive_chunk_hashes_v1(blob)
    chunk_root = derive_chunk_root_v1(chunk_hashes)
    target_without_root = FullBlobRetrievabilityTargetV1(
        certificate_version=1,
        application_id=application,
        chain_or_domain_id=domain,
        epoch_id=epoch,
        data_schema_id=schema,
        data_root=data_root,
        blob_length=len(blob),
        chunk_size=FULL_BLOB_CHUNK_BYTES_V1,
        chunk_count=len(chunk_hashes),
        chunk_root=chunk_root,
        retention_through_epoch=retention,
        storage_policy_hash=storage,
        certificate_root=data_root,
    )
    return FullBlobRetrievabilityTargetV1(
        certificate_version=target_without_root.certificate_version,
        application_id=target_without_root.application_id,
        chain_or_domain_id=target_without_root.chain_or_domain_id,
        epoch_id=target_without_root.epoch_id,
        data_schema_id=target_without_root.data_schema_id,
        data_root=target_without_root.data_root,
        blob_length=target_without_root.blob_length,
        chunk_size=target_without_root.chunk_size,
        chunk_count=target_without_root.chunk_count,
        chunk_root=target_without_root.chunk_root,
        retention_through_epoch=target_without_root.retention_through_epoch,
        storage_policy_hash=target_without_root.storage_policy_hash,
        certificate_root=derive_certificate_root_v1(target_without_root),
    )


def derive_chunk_hashes_v1(exact_blob_bytes: bytes) -> tuple[str, ...]:
    blob = _require_exact_blob(exact_blob_bytes)
    result: list[str] = []
    for index, chunk in enumerate(_chunks(blob)):
        hasher = _domain_hasher(_CHUNK_HASH_DOMAIN_V1)
        hasher.update(index.to_bytes(4, "big"))
        hasher.update(len(chunk).to_bytes(4, "big"))
        hasher.update(chunk)
        result.append("0x" + hasher.hexdigest())
    if len(result) > MAX_FULL_BLOB_CHUNKS_V1:
        raise ValueError("full-blob chunk count exceeds the V1 bound")
    return tuple(result)


def derive_chunk_root_v1(ordered_chunk_hashes: tuple[str, ...]) -> str:
    if type(ordered_chunk_hashes) is not tuple or not (
        1 <= len(ordered_chunk_hashes) <= MAX_FULL_BLOB_CHUNKS_V1
    ):
        raise ValueError("ordered chunk-hash vector is outside the V1 bound")
    hasher = _domain_hasher(_CHUNK_ROOT_DOMAIN_V1)
    hasher.update(len(ordered_chunk_hashes).to_bytes(4, "big"))
    for index, chunk_hash in enumerate(ordered_chunk_hashes):
        root = require_root(chunk_hash, name=f"ordered_chunk_hashes[{index}]")
        hasher.update(bytes.fromhex(root[2:]))
    return "0x" + hasher.hexdigest()


def derive_certificate_root_v1(target: FullBlobRetrievabilityTargetV1) -> str:
    if type(target) is not FullBlobRetrievabilityTargetV1:
        raise TypeError("certificate-root derivation requires an exact full-blob target")
    hasher = _domain_hasher(_CERTIFICATE_ROOT_DOMAIN_V1)
    hasher.update(target.certificate_version.to_bytes(2, "big"))
    hasher.update(bytes.fromhex(target.application_id[2:]))
    hasher.update(bytes.fromhex(target.chain_or_domain_id[2:]))
    hasher.update(target.epoch_id.to_bytes(8, "big"))
    hasher.update(bytes.fromhex(target.data_schema_id[2:]))
    hasher.update(bytes.fromhex(target.data_root[2:]))
    hasher.update(target.blob_length.to_bytes(8, "big"))
    hasher.update(target.chunk_size.to_bytes(4, "big"))
    hasher.update(target.chunk_count.to_bytes(4, "big"))
    hasher.update(bytes.fromhex(target.chunk_root[2:]))
    hasher.update(target.retention_through_epoch.to_bytes(8, "big"))
    hasher.update(bytes.fromhex(target.storage_policy_hash[2:]))
    return "0x" + hasher.hexdigest()


def derive_challenge_indices_v1(
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    provider_id: str,
) -> tuple[int, ...]:
    """Derive unique unbiased indices from the exact beacon and scope roots."""

    if type(policy) is not SampledRetrievabilityPolicyV1:
        raise TypeError("challenge derivation requires an exact policy")
    if type(target) is not FullBlobRetrievabilityTargetV1:
        raise TypeError("challenge derivation requires an exact full-blob target")
    if type(beacon) is not BeaconCommitmentV1:
        raise TypeError("challenge derivation requires an exact beacon")
    provider = require_token(provider_id, name="challenge provider_id")
    if policy.challenge_count > target.chunk_count:
        raise ValueError("challenge_count exceeds the full-blob chunk count")
    provider_bytes = provider.encode("ascii")
    modulus = target.chunk_count
    selected: list[int] = []
    for slot in range(policy.challenge_count):
        accepted = False
        for attempt in range(4_096):
            hasher = _domain_hasher(_CHALLENGE_DOMAIN_V1)
            hasher.update(bytes.fromhex(beacon.commitment[2:]))
            hasher.update(bytes.fromhex(beacon.source_id[2:]))
            hasher.update(bytes.fromhex(beacon.policy_hash[2:]))
            hasher.update(beacon.beacon_epoch.to_bytes(8, "big"))
            hasher.update(bytes.fromhex(policy.policy_root[2:]))
            hasher.update(bytes.fromhex(target.certificate_root[2:]))
            hasher.update(len(provider_bytes).to_bytes(2, "big"))
            hasher.update(provider_bytes)
            hasher.update(slot.to_bytes(2, "big"))
            hasher.update(attempt.to_bytes(2, "big"))
            index = map_digest_to_unbiased_chunk_index_v1(hasher.digest(), modulus)
            if index is None:
                continue
            if index in selected:
                continue
            selected.append(index)
            accepted = True
            break
        if not accepted:
            raise ValueError("challenge derivation exhausted its bounded retry budget")
    return tuple(selected)


def map_digest_to_unbiased_chunk_index_v1(
    digest: bytes,
    chunk_count: int,
) -> int | None:
    """Map a 256-bit digest uniformly or reject its high biased tail."""

    if type(digest) is not bytes or len(digest) != 32:
        raise ValueError("challenge digest must be exactly 32 bytes")
    if type(chunk_count) is not int or not 1 <= chunk_count <= MAX_FULL_BLOB_CHUNKS_V1:
        raise ValueError("challenge chunk_count is outside the V1 bound")
    universe_size = 1 << 256
    acceptance_limit = universe_size - (universe_size % chunk_count)
    candidate = int.from_bytes(digest, "big")
    if candidate >= acceptance_limit:
        return None
    return candidate % chunk_count


def chunk_hash_vector_sha256_v1(ordered_chunk_hashes: tuple[str, ...]) -> str:
    for index, value in enumerate(ordered_chunk_hashes):
        require_root(value, name=f"ordered_chunk_hashes[{index}]")
    return hash_v0(
        "zrpf_sampled_retrievability_chunk_hash_vector_v1",
        list(ordered_chunk_hashes),
    )


def verify_exact_blob_matches_target_v1(
    target: FullBlobRetrievabilityTargetV1,
    exact_blob_bytes: bytes,
) -> tuple[str, ...]:
    derived = derive_exact_full_blob_target_v1(
        application_id=target.application_id,
        chain_or_domain_id=target.chain_or_domain_id,
        epoch_id=target.epoch_id,
        data_schema_id=target.data_schema_id,
        exact_blob_bytes=exact_blob_bytes,
        retention_through_epoch=target.retention_through_epoch,
        storage_policy_hash=target.storage_policy_hash,
    )
    if derived != target:
        raise ValueError("exact blob does not match the full-blob target")
    return derive_chunk_hashes_v1(exact_blob_bytes)


def chunk_bytes_at_v1(exact_blob_bytes: bytes, index: int) -> bytes:
    blob = _require_exact_blob(exact_blob_bytes)
    if type(index) is not int or not 0 <= index < MAX_FULL_BLOB_CHUNKS_V1:
        raise ValueError("chunk index is not a bounded integer")
    chunks = _chunks(blob)
    if index >= len(chunks):
        raise ValueError("chunk index is outside the blob")
    return chunks[index]


def expected_chunk_length_v1(target: FullBlobRetrievabilityTargetV1, index: int) -> int:
    if type(index) is not int or not 0 <= index < target.chunk_count:
        raise ValueError("chunk index is outside the target")
    if index + 1 < target.chunk_count:
        return target.chunk_size
    remainder = target.blob_length % target.chunk_size
    return remainder if remainder != 0 else target.chunk_size


def chunk_leaf_hash_v1(index: int, chunk: bytes) -> str:
    if type(index) is not int or not 0 <= index < MAX_FULL_BLOB_CHUNKS_V1:
        raise ValueError("chunk index is outside the V1 bound")
    if type(chunk) is not bytes or not 1 <= len(chunk) <= FULL_BLOB_CHUNK_BYTES_V1:
        raise ValueError("chunk bytes are empty or oversized")
    hasher = _domain_hasher(_CHUNK_HASH_DOMAIN_V1)
    hasher.update(index.to_bytes(4, "big"))
    hasher.update(len(chunk).to_bytes(4, "big"))
    hasher.update(chunk)
    return "0x" + hasher.hexdigest()


def _derive_data_root(blob: bytes) -> str:
    hasher = _domain_hasher(_DATA_ROOT_DOMAIN_V1)
    hasher.update(len(blob).to_bytes(8, "big"))
    hasher.update(blob)
    return "0x" + hasher.hexdigest()


def _domain_hasher(domain: bytes) -> hashlib._Hash:
    if len(domain) > 65_535:
        raise ValueError("hash domain exceeds u16")
    hasher = hashlib.sha256()
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)
    return hasher


def _require_exact_blob(value: object) -> bytes:
    if type(value) is not bytes or not 1 <= len(value) <= MAX_FULL_BLOB_BYTES_V1:
        raise ValueError("exact full blob is empty or exceeds the V1 bound")
    return value


def _chunks(blob: bytes) -> tuple[bytes, ...]:
    return tuple(
        blob[offset : offset + FULL_BLOB_CHUNK_BYTES_V1]
        for offset in range(0, len(blob), FULL_BLOB_CHUNK_BYTES_V1)
    )
