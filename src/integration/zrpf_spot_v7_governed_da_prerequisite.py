"""Private Spot V7 join of governed full-blob and authenticated sample evidence.

This module consumes two independently sealed prerequisite values. It binds one
governed exact full-blob result to one BLS-authenticated sampled response at the
same application, domain, epoch, data commitment, checked epoch, and retention
scope. The existing operational-policy release provenance is retained exactly.

The sampled provider policy and beacon do not yet have governed provenance in
the Spot V7 operational manifest. The resulting capability therefore remains a
private prerequisite with no release, settlement, production, continuous-
availability, or future-public-availability authority.
"""

from __future__ import annotations

import hashlib
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_governed_da_projection import (
    _SpotV7GovernedDaPrerequisiteProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
    _GovernedOperationalPolicyProvenanceV1,
    _GovernedSpotV7OperationalPolicyV2,
    _require_exact_full_blob_satisfaction_v2,
    _require_operational_policy_v2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zrpf_sampled_retrievability_v1.hashing import (
    derive_exact_full_blob_target_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.projection import (
    _VerifiedProjectionV1,
)
from src.integration.zrpf_sampled_retrievability_v1.verifier import (
    _AuthenticatedSampledRetrievabilityEvidenceV1,
)

__all__ = ()


class SpotV7GovernedDaPrerequisiteBindingErrorV1(ValueError):
    """Stable cross-binding rejection before any downstream gate is opened."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_GOVERNED_DA_PREREQUISITE_REJECTED: {code}")


class _GovernedSpotV7DataAvailabilityPrerequisiteSealV1:
    __slots__ = ()


_GOVERNED_SPOT_V7_DA_PREREQUISITE_SEAL_V1 = (
    _GovernedSpotV7DataAvailabilityPrerequisiteSealV1()
)


@final
class _GovernedSpotV7DataAvailabilityPrerequisiteV1:
    """Non-transferable scoped DA prerequisite; no application authority."""

    __slots__ = (
        "_exact_full_blob",
        "_operational_policy",
        "_projection",
        "_sampled_response",
        "_seal",
    )

    _exact_full_blob: _GovernedExactFullBlobPolicySatisfactionV2
    _operational_policy: _GovernedSpotV7OperationalPolicyV2
    _projection: _SpotV7GovernedDaPrerequisiteProjectionV1
    _sampled_response: _AuthenticatedSampledRetrievabilityEvidenceV1
    _seal: _GovernedSpotV7DataAvailabilityPrerequisiteSealV1

    def __init__(
        self,
        projection: _SpotV7GovernedDaPrerequisiteProjectionV1,
        *,
        operational_policy: _GovernedSpotV7OperationalPolicyV2,
        exact_full_blob: _GovernedExactFullBlobPolicySatisfactionV2,
        sampled_response: _AuthenticatedSampledRetrievabilityEvidenceV1,
        seal: _GovernedSpotV7DataAvailabilityPrerequisiteSealV1,
    ) -> None:
        if type(projection) is not _SpotV7GovernedDaPrerequisiteProjectionV1:
            raise TypeError("combined DA projection has the wrong type")
        if seal is not _GOVERNED_SPOT_V7_DA_PREREQUISITE_SEAL_V1:
            raise TypeError("combined DA prerequisite requires the module-private seal")
        expected = _derive_projection_v1(
            operational_policy=operational_policy,
            exact_full_blob=exact_full_blob,
            sampled_response=sampled_response,
        )
        if projection != expected:
            raise ValueError("combined DA prerequisite projection drift")
        object.__setattr__(self, "_operational_policy", operational_policy)
        object.__setattr__(self, "_exact_full_blob", exact_full_blob)
        object.__setattr__(self, "_sampled_response", sampled_response)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("combined DA prerequisite cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("combined DA prerequisite cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("combined DA prerequisite cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("combined DA prerequisite cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("combined DA prerequisite cannot be serialized")

    def _has_private_seal(self) -> bool:
        return (
            getattr(self, "_seal", None)
            is _GOVERNED_SPOT_V7_DA_PREREQUISITE_SEAL_V1
        )

    def _projection_for_downstream_binding_v1(
        self,
    ) -> _SpotV7GovernedDaPrerequisiteProjectionV1:
        if not self._has_private_seal():
            raise TypeError("combined DA prerequisite lacks its private seal")
        expected = _derive_projection_v1(
            operational_policy=self._operational_policy,
            exact_full_blob=self._exact_full_blob,
            sampled_response=self._sampled_response,
        )
        if expected != self._projection:
            raise ValueError("combined DA prerequisite projection drift")
        return self._projection

    @property
    def governed_exact_full_blob_policy_satisfied(self) -> bool:
        self._projection_for_downstream_binding_v1()
        return True

    @property
    def authenticated_sampled_response_scoped_to_checked_epoch(self) -> bool:
        self._projection_for_downstream_binding_v1()
        return True

    @property
    def operational_policy_release_provenance_bound(self) -> bool:
        self._projection_for_downstream_binding_v1()
        return True

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        return False

    @property
    def current_operational_policy_release_head_verified(self) -> bool:
        return False

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        return False

    @property
    def beacon_unpredictability_verified(self) -> bool:
        return False

    @property
    def response_timing_provenance_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _bind_governed_spot_v7_da_prerequisite_v1(
    *,
    operational_policy: object,
    exact_full_blob: object,
    sampled_response: object,
) -> _GovernedSpotV7DataAvailabilityPrerequisiteV1:
    """Join only exact private prerequisite values after deterministic binding."""

    policy = _require_operational_policy_v2(operational_policy)
    full_blob = _require_exact_full_blob_satisfaction_v2(exact_full_blob)
    sampled = _require_authenticated_sampled_response_v1(sampled_response)
    projection = _derive_projection_v1(
        operational_policy=policy,
        exact_full_blob=full_blob,
        sampled_response=sampled,
    )
    return _GovernedSpotV7DataAvailabilityPrerequisiteV1(
        projection,
        operational_policy=policy,
        exact_full_blob=full_blob,
        sampled_response=sampled,
        seal=_GOVERNED_SPOT_V7_DA_PREREQUISITE_SEAL_V1,
    )


def _require_authenticated_sampled_response_v1(
    value: object,
) -> _AuthenticatedSampledRetrievabilityEvidenceV1:
    if type(value) is not _AuthenticatedSampledRetrievabilityEvidenceV1:
        raise TypeError("combined DA prerequisite requires an authenticated sampled response")
    if not value._has_private_seal():
        raise TypeError("combined DA prerequisite requires an authenticated sampled response")
    value._projection_for_spot_v7_da_prerequisite_v1()
    return value


def _derive_projection_v1(
    *,
    operational_policy: _GovernedSpotV7OperationalPolicyV2,
    exact_full_blob: _GovernedExactFullBlobPolicySatisfactionV2,
    sampled_response: _AuthenticatedSampledRetrievabilityEvidenceV1,
) -> _SpotV7GovernedDaPrerequisiteProjectionV1:
    policy = _require_operational_policy_v2(operational_policy)
    full_blob = _require_exact_full_blob_satisfaction_v2(exact_full_blob)
    sampled = _require_authenticated_sampled_response_v1(sampled_response)
    if full_blob._governed_policy is not policy:
        _mismatch("POLICY_CAPABILITY_MISMATCH")

    full = full_blob._projection
    sampled_projection = sampled._projection_for_spot_v7_da_prerequisite_v1()
    store_policy = policy._policy_for_atomic_store()
    provenance = policy._policy_provenance_for_atomic_store()
    try:
        policy._require_active_at_epoch_for_operational_use(
            sampled_projection.checked_epoch
        )
    except ValueError:
        _mismatch("POLICY_PROVENANCE_INACTIVE")
    _require_identity_and_scope_v1(store_policy, full, sampled_projection)
    _require_policy_binding_v1(store_policy, full, sampled_projection)
    _require_exact_full_blob_binding_v1(
        store_policy,
        full_blob,
        full,
        sampled_projection,
    )
    _require_same(
        sampled_projection.beacon_epoch,
        sampled_projection.checked_epoch,
        "BEACON_EPOCH_MISMATCH",
    )
    provider_set_root = hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        list(sampled_projection.accepted_provider_ids),
    )
    return _projection_from_bound_values(
        full=full,
        sampled=sampled_projection,
        provenance=provenance,
        provider_set_root=provider_set_root,
    )


def _require_identity_and_scope_v1(
    policy: _TestOnlySpotV7OperationalPolicyV1,
    full: _GovernedFullBlobPolicyProjectionV1,
    sampled: _VerifiedProjectionV1,
) -> None:
    _require_same(sampled.application_id, full.application_id, "APPLICATION_MISMATCH")
    _require_same(full.application_id, policy.application_id, "APPLICATION_MISMATCH")
    _require_same(sampled.chain_or_domain_id, full.chain_or_domain_id, "DOMAIN_MISMATCH")
    _require_same(full.chain_or_domain_id, policy.chain_or_domain_id, "DOMAIN_MISMATCH")
    _require_same(sampled.epoch_id, full.epoch_id, "EPOCH_MISMATCH")
    _require_same(sampled.checked_epoch, full.checked_epoch, "CHECKED_EPOCH_MISMATCH")
    _require_same(
        sampled.retention_through_epoch,
        full.retention_through_epoch,
        "RETENTION_MISMATCH",
    )


def _require_policy_binding_v1(
    policy: _TestOnlySpotV7OperationalPolicyV1,
    full: _GovernedFullBlobPolicyProjectionV1,
    sampled: _VerifiedProjectionV1,
) -> None:
    _require_same(
        sampled.storage_policy_hash,
        policy.storage_policy_hash,
        "STORAGE_POLICY_MISMATCH",
    )
    _require_same(
        full.policy_root,
        policy.full_blob_policy_root,
        "FULL_BLOB_POLICY_ROOT_MISMATCH",
    )
    if (
        sampled.minimum_retention_epochs < policy.minimum_retention_epochs
        or sampled.minimum_remaining_epochs < policy.minimum_remaining_epochs
    ):
        _mismatch("SAMPLED_RETENTION_POLICY_WEAKER")


def _require_exact_full_blob_binding_v1(
    policy: _TestOnlySpotV7OperationalPolicyV1,
    capability: _GovernedExactFullBlobPolicySatisfactionV2,
    full: _GovernedFullBlobPolicyProjectionV1,
    sampled: _VerifiedProjectionV1,
) -> None:
    expected_blob_sha256 = "0x" + hashlib.sha256(capability._exact_blob_bytes).hexdigest()
    _require_same(full.exact_blob_sha256, expected_blob_sha256, "EXACT_BLOB_DIGEST_MISMATCH")
    derived = derive_exact_full_blob_target_v1(
        application_id=policy.application_id,
        chain_or_domain_id=policy.chain_or_domain_id,
        epoch_id=full.epoch_id,
        data_schema_id=policy.data_schema_id,
        exact_blob_bytes=capability._exact_blob_bytes,
        retention_through_epoch=full.retention_through_epoch,
        storage_policy_hash=policy.storage_policy_hash,
    )
    _require_same(sampled.data_root, full.data_root, "DATA_ROOT_MISMATCH")
    _require_same(full.data_root, derived.data_root, "DATA_ROOT_MISMATCH")
    _require_same(sampled.data_root, derived.data_root, "DATA_ROOT_MISMATCH")
    _require_same(sampled.chunk_root, derived.chunk_root, "CHUNK_ROOT_MISMATCH")
    _require_same(
        sampled.certificate_root,
        full.certificate_root,
        "CERTIFICATE_ROOT_MISMATCH",
    )
    _require_same(
        full.certificate_root,
        derived.certificate_root,
        "CERTIFICATE_ROOT_MISMATCH",
    )
    _require_same(
        sampled.certificate_root,
        derived.certificate_root,
        "CERTIFICATE_ROOT_MISMATCH",
    )
    _require_same(
        sampled.data_schema_id,
        derived.data_schema_id,
        "CERTIFICATE_ROOT_MISMATCH",
    )
    _require_same(sampled.blob_length, derived.blob_length, "DATA_ROOT_MISMATCH")
    _require_same(sampled.chunk_size, derived.chunk_size, "CHUNK_ROOT_MISMATCH")
    _require_same(sampled.chunk_count, derived.chunk_count, "CHUNK_ROOT_MISMATCH")


def _projection_from_bound_values(
    *,
    full: _GovernedFullBlobPolicyProjectionV1,
    sampled: _VerifiedProjectionV1,
    provenance: _GovernedOperationalPolicyProvenanceV1,
    provider_set_root: str,
) -> _SpotV7GovernedDaPrerequisiteProjectionV1:
    return _SpotV7GovernedDaPrerequisiteProjectionV1(
        application_id=sampled.application_id,
        chain_or_domain_id=sampled.chain_or_domain_id,
        epoch_id=sampled.epoch_id,
        checked_epoch=sampled.checked_epoch,
        certificate_root=sampled.certificate_root,
        data_root=sampled.data_root,
        chunk_root=sampled.chunk_root,
        retention_through_epoch=sampled.retention_through_epoch,
        full_blob_policy_root=full.policy_root,
        sampled_policy_root=sampled.policy_root,
        exact_blob_sha256=full.exact_blob_sha256,
        accepted_provider_ids=sampled.accepted_provider_ids,
        accepted_provider_set_root=provider_set_root,
        sampled_evidence_sha256=sampled.evidence_sha256,
        operational_policy_provenance_root=provenance.evidence_root,
        operational_policy_manifest_sha256=provenance.manifest_sha256,
        operational_policy_signer_registry_hash=provenance.signer_registry_hash,
        operational_policy_signature_quorum_report_hash=(
            provenance.signature_quorum_report_hash
        ),
        operational_policy_revision=provenance.policy_revision,
        operational_policy_evaluation_epoch=provenance.evaluation_epoch,
        beacon_source_id=sampled.beacon_source_id,
        beacon_policy_hash=sampled.beacon_policy_hash,
        beacon_epoch=sampled.beacon_epoch,
        beacon_commitment=sampled.beacon_commitment,
    )


def _require_same(left: object, right: object, code: str) -> None:
    if type(left) is not type(right) or left != right:
        _mismatch(code)


def _mismatch(code: str) -> NoReturn:
    raise SpotV7GovernedDaPrerequisiteBindingErrorV1(code)
