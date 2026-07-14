"""Private bounded projection for the Spot V7 combined DA prerequisite."""

from __future__ import annotations

from dataclasses import dataclass

from src.integration.zrpf_sampled_retrievability_v1.model import (
    require_root,
    require_token,
    require_u64,
)


@dataclass(frozen=True, slots=True)
class _SpotV7GovernedDaPrerequisiteProjectionV1:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    checked_epoch: int
    certificate_root: str
    data_root: str
    chunk_root: str
    retention_through_epoch: int
    full_blob_policy_root: str
    sampled_policy_root: str
    exact_blob_sha256: str
    accepted_provider_ids: tuple[str, ...]
    accepted_provider_set_root: str
    sampled_evidence_sha256: str
    operational_policy_provenance_root: str
    operational_policy_manifest_sha256: str
    operational_policy_signer_registry_hash: str
    operational_policy_signature_quorum_report_hash: str
    operational_policy_revision: int
    operational_policy_evaluation_epoch: int
    beacon_source_id: str
    beacon_policy_hash: str
    beacon_epoch: int
    beacon_commitment: str

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "certificate_root",
            "data_root",
            "chunk_root",
            "full_blob_policy_root",
            "sampled_policy_root",
            "exact_blob_sha256",
            "accepted_provider_set_root",
            "operational_policy_provenance_root",
            "operational_policy_signer_registry_hash",
            "operational_policy_signature_quorum_report_hash",
            "beacon_source_id",
            "beacon_policy_hash",
            "beacon_commitment",
        ):
            require_root(getattr(self, name), name=f"combined DA {name}")
        for name in (
            "epoch_id",
            "checked_epoch",
            "retention_through_epoch",
            "operational_policy_revision",
            "operational_policy_evaluation_epoch",
            "beacon_epoch",
        ):
            require_u64(getattr(self, name), name=f"combined DA {name}")
        if self.checked_epoch < self.epoch_id:
            raise ValueError("combined DA checked epoch precedes data epoch")
        if self.retention_through_epoch < self.checked_epoch:
            raise ValueError("combined DA retention ends before the checked epoch")
        if self.beacon_epoch != self.checked_epoch:
            raise ValueError("combined DA beacon epoch differs from checked epoch")
        if type(self.accepted_provider_ids) is not tuple or not self.accepted_provider_ids:
            raise TypeError("combined DA provider IDs must be a nonempty tuple")
        for provider_id in self.accepted_provider_ids:
            require_token(provider_id, name="combined DA provider_id")
        if tuple(sorted(set(self.accepted_provider_ids))) != self.accepted_provider_ids:
            raise ValueError("combined DA provider IDs are not canonical and distinct")
        _require_bare_sha256(
            self.sampled_evidence_sha256,
            name="combined DA sampled evidence SHA-256",
        )
        _require_bare_sha256(
            self.operational_policy_manifest_sha256,
            name="combined DA operational policy manifest SHA-256",
        )


def _require_bare_sha256(value: object, *, name: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{name} must be canonical lowercase hex")
