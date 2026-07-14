"""Private authenticated-result projection for sampled retrievability V1."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from .model import (
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    SampledRetrievabilityPolicyV1,
)


@dataclass(frozen=True, slots=True)
class _VerifiedProjectionV1:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    data_schema_id: str
    data_root: str
    blob_length: int
    chunk_size: int
    chunk_count: int
    chunk_root: str
    retention_through_epoch: int
    storage_policy_hash: str
    checked_epoch: int
    accepted_provider_ids: tuple[str, ...]
    policy_root: str
    certificate_root: str
    policy_revision: int
    policy_activation_epoch: int
    policy_revocation_epoch: int | None
    minimum_retention_epochs: int
    minimum_remaining_epochs: int
    response_window_epochs: int
    minimum_provider_responses: int
    beacon_source_id: str
    beacon_policy_hash: str
    beacon_epoch: int
    beacon_commitment: str
    evidence_sha256: str


def _build_verified_projection_v1(
    *,
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
    accepted_provider_ids: tuple[str, ...],
    exact_evidence_bytes: bytes,
) -> _VerifiedProjectionV1:
    return _VerifiedProjectionV1(
        application_id=target.application_id,
        chain_or_domain_id=target.chain_or_domain_id,
        epoch_id=target.epoch_id,
        data_schema_id=target.data_schema_id,
        data_root=target.data_root,
        blob_length=target.blob_length,
        chunk_size=target.chunk_size,
        chunk_count=target.chunk_count,
        chunk_root=target.chunk_root,
        retention_through_epoch=target.retention_through_epoch,
        storage_policy_hash=target.storage_policy_hash,
        checked_epoch=checked_epoch,
        accepted_provider_ids=accepted_provider_ids,
        policy_root=policy.policy_root,
        certificate_root=target.certificate_root,
        policy_revision=policy.policy_revision,
        policy_activation_epoch=policy.activation_epoch,
        policy_revocation_epoch=policy.revocation_epoch,
        minimum_retention_epochs=policy.minimum_retention_epochs,
        minimum_remaining_epochs=policy.minimum_remaining_epochs,
        response_window_epochs=policy.response_window_epochs,
        minimum_provider_responses=policy.minimum_provider_responses,
        beacon_source_id=beacon.source_id,
        beacon_policy_hash=beacon.policy_hash,
        beacon_epoch=beacon.beacon_epoch,
        beacon_commitment=beacon.commitment,
        evidence_sha256=hashlib.sha256(exact_evidence_bytes).hexdigest(),
    )


def _require_authenticated_provider_ids(
    value: object,
    policy: SampledRetrievabilityPolicyV1,
    checked_epoch: int,
) -> tuple[str, ...]:
    if type(value) is not tuple or not value:
        raise TypeError("authenticated provider IDs must be a nonempty tuple")
    if any(type(provider_id) is not str for provider_id in value):
        raise TypeError("authenticated provider IDs must contain exact strings")
    if tuple(sorted(set(value))) != value:
        raise ValueError("authenticated provider IDs are not canonical and distinct")
    active = set(policy.active_provider_ids_at(checked_epoch))
    if any(provider_id not in active for provider_id in value):
        raise ValueError("authenticated provider ID is inactive at the checked epoch")
    if len(value) < policy.minimum_provider_responses:
        raise ValueError("authenticated provider IDs do not satisfy policy quorum")
    return value
