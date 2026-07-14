"""Governed Spot V7 sampled-policy and checkpoint-beacon DA prerequisite V2.

This module first wraps an authenticated sampled response with the exact signed
V3 sampled policy and the exact governed lagged-checkpoint beacon.  It then
joins that wrapper with the existing exact full-blob capability.  The resulting
private V2 prerequisite advances only two scoped provenance claims: sampled
policy governance and governed beacon provenance.  Every stronger availability
or application-authority claim remains false.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_governed_da_projection import (
    _SpotV7GovernedDaPrerequisiteProjectionV1,
)
from src.integration._zrpf_spot_v7_governed_da_projection_v2 import (
    _SpotV7GovernedDaPrerequisiteProjectionV2,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
    _require_exact_full_blob_satisfaction_v2,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
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
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    _GovernedSpotV7LaggedCheckpointBeaconV1,
    _require_governed_lagged_checkpoint_beacon_v1,
)

__all__ = ()


class SpotV7GovernedDaPrerequisiteBindingErrorV2(ValueError):
    """Stable V2 cross-binding rejection before any downstream gate opens."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_GOVERNED_DA_PREREQUISITE_V2_REJECTED: {code}")


def _mismatch(code: str) -> NoReturn:
    raise SpotV7GovernedDaPrerequisiteBindingErrorV2(code)


@dataclass(frozen=True, slots=True)
class _GovernedSampledResponseProjectionV1:
    sampled: _VerifiedProjectionV1
    operational_policy_provenance_root: str
    source_checkpoint_sequence: int
    source_checkpoint_hash: str
    source_finality_policy_root: str
    source_finality_certificate_root: str
    source_finality_evidence_root: str

    def __post_init__(self) -> None:
        if type(self.sampled) is not _VerifiedProjectionV1:
            raise TypeError("governed sampled projection has the wrong sampled type")


class _GovernedSampledResponseSealV1:
    __slots__ = ()


_GOVERNED_SAMPLED_RESPONSE_SEAL_V1 = _GovernedSampledResponseSealV1()


@final
class _GovernedSpotV7SampledResponseV1:
    """Private authenticated sample under signed policy and governed beacon."""

    __slots__ = ("_beacon", "_policy", "_projection", "_sampled", "_seal")

    _beacon: _GovernedSpotV7LaggedCheckpointBeaconV1
    _policy: _GovernedSpotV7OperationalPolicyV3
    _projection: _GovernedSampledResponseProjectionV1
    _sampled: _AuthenticatedSampledRetrievabilityEvidenceV1
    _seal: _GovernedSampledResponseSealV1

    def __init__(
        self,
        projection: _GovernedSampledResponseProjectionV1,
        *,
        operational_policy: _GovernedSpotV7OperationalPolicyV3,
        governed_beacon: _GovernedSpotV7LaggedCheckpointBeaconV1,
        sampled_response: _AuthenticatedSampledRetrievabilityEvidenceV1,
        seal: _GovernedSampledResponseSealV1,
    ) -> None:
        if type(projection) is not _GovernedSampledResponseProjectionV1:
            raise TypeError("governed sampled-response projection has the wrong type")
        if seal is not _GOVERNED_SAMPLED_RESPONSE_SEAL_V1:
            raise TypeError("governed sampled response requires the module-private seal")
        expected = _derive_governed_sample_projection_v1(
            operational_policy=operational_policy,
            governed_beacon=governed_beacon,
            sampled_response=sampled_response,
        )
        if projection != expected:
            raise ValueError("governed sampled-response projection drift")
        object.__setattr__(self, "_policy", operational_policy)
        object.__setattr__(self, "_beacon", governed_beacon)
        object.__setattr__(self, "_sampled", sampled_response)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("governed sampled response cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("governed sampled response cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("governed sampled response cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("governed sampled response cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("governed sampled response cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_SAMPLED_RESPONSE_SEAL_V1

    def _projection_for_combined_da_v2(self) -> _GovernedSampledResponseProjectionV1:
        if not self._has_private_seal():
            raise TypeError("governed sampled response lacks its private seal")
        expected = _derive_governed_sample_projection_v1(
            operational_policy=self._policy,
            governed_beacon=self._beacon,
            sampled_response=self._sampled,
        )
        if expected != self._projection:
            raise ValueError("governed sampled-response projection drift")
        return self._projection

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        self._projection_for_combined_da_v2()
        return True

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        self._projection_for_combined_da_v2()
        return True

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


def _bind_governed_spot_v7_sampled_response_v1(
    *,
    operational_policy: object,
    governed_beacon: object,
    sampled_response: object,
) -> _GovernedSpotV7SampledResponseV1:
    """Bind exact authenticated sample bytes to signed policy and beacon facts."""

    policy = _require_governed_operational_policy_v3(operational_policy)
    beacon = _require_governed_lagged_checkpoint_beacon_v1(governed_beacon)
    sampled = _require_authenticated_sampled_response(sampled_response)
    projection = _derive_governed_sample_projection_v1(
        operational_policy=policy,
        governed_beacon=beacon,
        sampled_response=sampled,
    )
    return _GovernedSpotV7SampledResponseV1(
        projection,
        operational_policy=policy,
        governed_beacon=beacon,
        sampled_response=sampled,
        seal=_GOVERNED_SAMPLED_RESPONSE_SEAL_V1,
    )


def _derive_governed_sample_projection_v1(
    *,
    operational_policy: _GovernedSpotV7OperationalPolicyV3,
    governed_beacon: _GovernedSpotV7LaggedCheckpointBeaconV1,
    sampled_response: _AuthenticatedSampledRetrievabilityEvidenceV1,
) -> _GovernedSampledResponseProjectionV1:
    policy = _require_governed_operational_policy_v3(operational_policy)
    beacon = _require_governed_lagged_checkpoint_beacon_v1(governed_beacon)
    sampled = _require_authenticated_sampled_response(sampled_response)
    if beacon._policy is not policy:
        _mismatch("POLICY_CAPABILITY_MISMATCH")
    beacon_projection = beacon._projection_for_governed_da_v2()
    sampled_projection = sampled._projection_for_spot_v7_da_prerequisite_v1()
    expected_policy = policy._sampled_policy_for_governed_da_v2()
    expected_beacon = beacon._beacon_for_sampled_retrievability_v1()
    if sampled._expected_policy != expected_policy:
        _mismatch("SAMPLED_POLICY_MISMATCH")
    if sampled._expected_beacon != expected_beacon:
        _mismatch("GOVERNED_BEACON_MISMATCH")
    if sampled_projection.checked_epoch != beacon_projection.checked_epoch:
        _mismatch("CHECKED_EPOCH_MISMATCH")
    policy._require_active_at_epoch_for_governed_da_v2(sampled_projection.checked_epoch)
    return _GovernedSampledResponseProjectionV1(
        sampled=sampled_projection,
        operational_policy_provenance_root=(
            policy._projection_for_governed_da_v2().policy_provenance_root
        ),
        source_checkpoint_sequence=beacon_projection.source_checkpoint_sequence,
        source_checkpoint_hash=beacon_projection.source_checkpoint_hash,
        source_finality_policy_root=beacon_projection.source_finality_policy_root,
        source_finality_certificate_root=(
            beacon_projection.source_finality_certificate_root
        ),
        source_finality_evidence_root=beacon_projection.source_finality_evidence_root,
    )


def _require_authenticated_sampled_response(
    value: object,
) -> _AuthenticatedSampledRetrievabilityEvidenceV1:
    if (
        not isinstance(value, _AuthenticatedSampledRetrievabilityEvidenceV1)
        or type(value) is not _AuthenticatedSampledRetrievabilityEvidenceV1
    ):
        raise TypeError("governed sample requires exact authenticated sampled response")
    authenticated = value
    if not authenticated._has_private_seal():
        raise TypeError("governed sample requires sealed authenticated sampled response")
    authenticated._projection_for_spot_v7_da_prerequisite_v1()
    return authenticated


def _require_governed_sampled_response(
    value: object,
) -> _GovernedSpotV7SampledResponseV1:
    if type(value) is not _GovernedSpotV7SampledResponseV1:
        raise TypeError("combined DA V2 requires exact governed sampled response")
    if not value._has_private_seal():
        raise TypeError("combined DA V2 requires sealed governed sampled response")
    value._projection_for_combined_da_v2()
    return value


class _GovernedDaPrerequisiteSealV2:
    __slots__ = ()


_GOVERNED_DA_PREREQUISITE_SEAL_V2 = _GovernedDaPrerequisiteSealV2()


@final
class _GovernedSpotV7DataAvailabilityPrerequisiteV2:
    """Private exact-content and governed sampled-policy DA prerequisite V2."""

    __slots__ = ("_full_blob", "_policy", "_projection", "_sampled", "_seal")

    _full_blob: _GovernedExactFullBlobPolicySatisfactionV2
    _policy: _GovernedSpotV7OperationalPolicyV3
    _projection: _SpotV7GovernedDaPrerequisiteProjectionV2
    _sampled: _GovernedSpotV7SampledResponseV1
    _seal: _GovernedDaPrerequisiteSealV2

    def __init__(
        self,
        projection: _SpotV7GovernedDaPrerequisiteProjectionV2,
        *,
        operational_policy: _GovernedSpotV7OperationalPolicyV3,
        exact_full_blob: _GovernedExactFullBlobPolicySatisfactionV2,
        governed_sampled_response: _GovernedSpotV7SampledResponseV1,
        seal: _GovernedDaPrerequisiteSealV2,
    ) -> None:
        if type(projection) is not _SpotV7GovernedDaPrerequisiteProjectionV2:
            raise TypeError("combined DA V2 projection has the wrong type")
        if seal is not _GOVERNED_DA_PREREQUISITE_SEAL_V2:
            raise TypeError("combined DA V2 requires the module-private seal")
        expected = _derive_combined_da_projection_v2(
            operational_policy=operational_policy,
            exact_full_blob=exact_full_blob,
            governed_sampled_response=governed_sampled_response,
        )
        if projection != expected:
            raise ValueError("combined DA V2 projection drift")
        object.__setattr__(self, "_policy", operational_policy)
        object.__setattr__(self, "_full_blob", exact_full_blob)
        object.__setattr__(self, "_sampled", governed_sampled_response)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("combined DA V2 prerequisite cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("combined DA V2 prerequisite cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("combined DA V2 prerequisite cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("combined DA V2 prerequisite cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("combined DA V2 prerequisite cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_DA_PREREQUISITE_SEAL_V2

    def _projection_for_downstream_binding_v2(
        self,
    ) -> _SpotV7GovernedDaPrerequisiteProjectionV2:
        if not self._has_private_seal():
            raise TypeError("combined DA V2 prerequisite lacks its private seal")
        expected = _derive_combined_da_projection_v2(
            operational_policy=self._policy,
            exact_full_blob=self._full_blob,
            governed_sampled_response=self._sampled,
        )
        if expected != self._projection:
            raise ValueError("combined DA V2 projection drift")
        return self._projection

    def _source_finality_artifacts_for_operational_store_v4(
        self,
    ) -> tuple[bytes, bytes]:
        projection = self._projection_for_downstream_binding_v2()
        source = self._sampled._beacon._source_finality
        if not source._has_private_seal():
            raise TypeError("governed DA V2 source finality lacks its private seal")
        if source._projection.certificate_root != (
            projection.source_finality_certificate_root
        ):
            raise ValueError("governed DA V2 source finality certificate drift")
        if source._projection.finality_evidence_root != (
            projection.source_finality_evidence_root
        ):
            raise ValueError("governed DA V2 source finality evidence drift")
        return (
            source._exact_certificate_bytes,
            source._exact_finality_evidence_bytes,
        )

    @property
    def governed_exact_full_blob_policy_satisfied(self) -> bool:
        self._projection_for_downstream_binding_v2()
        return True

    @property
    def authenticated_sampled_response_scoped_to_checked_epoch(self) -> bool:
        self._projection_for_downstream_binding_v2()
        return True

    @property
    def operational_policy_release_provenance_bound(self) -> bool:
        self._projection_for_downstream_binding_v2()
        return True

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        self._projection_for_downstream_binding_v2()
        return True

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        self._projection_for_downstream_binding_v2()
        return True

    @property
    def current_operational_policy_release_head_verified(self) -> bool:
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


def _bind_governed_spot_v7_da_prerequisite_v2(
    *,
    operational_policy: object,
    exact_full_blob: object,
    governed_sampled_response: object,
) -> _GovernedSpotV7DataAvailabilityPrerequisiteV2:
    """Join only exact sealed V3 policy, full blob, and governed sample values."""

    policy = _require_governed_operational_policy_v3(operational_policy)
    full_blob = _require_exact_full_blob_satisfaction_v2(exact_full_blob)
    sampled = _require_governed_sampled_response(governed_sampled_response)
    projection = _derive_combined_da_projection_v2(
        operational_policy=policy,
        exact_full_blob=full_blob,
        governed_sampled_response=sampled,
    )
    return _GovernedSpotV7DataAvailabilityPrerequisiteV2(
        projection,
        operational_policy=policy,
        exact_full_blob=full_blob,
        governed_sampled_response=sampled,
        seal=_GOVERNED_DA_PREREQUISITE_SEAL_V2,
    )


def _derive_combined_da_projection_v2(
    *,
    operational_policy: _GovernedSpotV7OperationalPolicyV3,
    exact_full_blob: _GovernedExactFullBlobPolicySatisfactionV2,
    governed_sampled_response: _GovernedSpotV7SampledResponseV1,
) -> _SpotV7GovernedDaPrerequisiteProjectionV2:
    policy = _require_governed_operational_policy_v3(operational_policy)
    full_blob = _require_exact_full_blob_satisfaction_v2(exact_full_blob)
    governed_sample = _require_governed_sampled_response(governed_sampled_response)
    if governed_sample._policy is not policy:
        _mismatch("POLICY_CAPABILITY_MISMATCH")
    base_policy = policy._base_store_policy_for_full_blob_v2()
    if full_blob._governed_policy._policy_for_atomic_store() != base_policy:
        _mismatch("FULL_BLOB_POLICY_MATERIAL_MISMATCH")
    full = full_blob._projection
    governed_projection = governed_sample._projection_for_combined_da_v2()
    sampled = governed_projection.sampled
    policy_projection = policy._projection_for_governed_da_v2()
    policy._require_active_at_epoch_for_governed_da_v2(sampled.checked_epoch)
    expected_blob_sha = "0x" + hashlib.sha256(full_blob._exact_blob_bytes).hexdigest()
    derived = derive_exact_full_blob_target_v1(
        application_id=base_policy.application_id,
        chain_or_domain_id=base_policy.chain_or_domain_id,
        epoch_id=full.epoch_id,
        data_schema_id=base_policy.data_schema_id,
        exact_blob_bytes=full_blob._exact_blob_bytes,
        retention_through_epoch=full.retention_through_epoch,
        storage_policy_hash=base_policy.storage_policy_hash,
    )
    checks = (
        (sampled.application_id == full.application_id, "APPLICATION_MISMATCH"),
        (full.application_id == base_policy.application_id, "APPLICATION_MISMATCH"),
        (sampled.chain_or_domain_id == full.chain_or_domain_id, "DOMAIN_MISMATCH"),
        (full.chain_or_domain_id == base_policy.chain_or_domain_id, "DOMAIN_MISMATCH"),
        (sampled.epoch_id == full.epoch_id, "EPOCH_MISMATCH"),
        (sampled.checked_epoch == full.checked_epoch, "CHECKED_EPOCH_MISMATCH"),
        (
            sampled.retention_through_epoch == full.retention_through_epoch,
            "RETENTION_MISMATCH",
        ),
        (full.policy_root == policy_projection.full_blob_da_policy_root, "FULL_BLOB_POLICY_ROOT_MISMATCH"),
        (sampled.policy_root == policy_projection.sampled_policy_root, "SAMPLED_POLICY_ROOT_MISMATCH"),
        (full.exact_blob_sha256 == expected_blob_sha, "EXACT_BLOB_DIGEST_MISMATCH"),
        (sampled.data_root == full.data_root == derived.data_root, "DATA_ROOT_MISMATCH"),
        (sampled.chunk_root == derived.chunk_root, "CHUNK_ROOT_MISMATCH"),
        (
            sampled.certificate_root == full.certificate_root == derived.certificate_root,
            "CERTIFICATE_ROOT_MISMATCH",
        ),
        (sampled.data_schema_id == derived.data_schema_id, "DATA_SCHEMA_MISMATCH"),
        (sampled.blob_length == derived.blob_length, "BLOB_LENGTH_MISMATCH"),
        (sampled.chunk_size == derived.chunk_size, "CHUNK_SIZE_MISMATCH"),
        (sampled.chunk_count == derived.chunk_count, "CHUNK_COUNT_MISMATCH"),
    )
    for accepted, code in checks:
        if not accepted:
            _mismatch(code)
    provenance = policy._provenance_for_governed_da_v2()
    provider_set_root = hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        list(sampled.accepted_provider_ids),
    )
    base_projection = _SpotV7GovernedDaPrerequisiteProjectionV1(
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
    beacon_projection = governed_sample._beacon._projection_for_governed_da_v2()
    return _SpotV7GovernedDaPrerequisiteProjectionV2(
        base=base_projection,
        zeno_ledger_chain_id=policy_projection.zeno_ledger_chain_id,
        source_network_id=beacon_projection.source_network_id,
        source_protocol_id=beacon_projection.source_protocol_id,
        source_epoch_lag=beacon_projection.source_epoch_lag,
        source_checkpoint_sequence=governed_projection.source_checkpoint_sequence,
        source_checkpoint_hash=governed_projection.source_checkpoint_hash,
        source_finality_policy_root=governed_projection.source_finality_policy_root,
        source_finality_certificate_root=(
            governed_projection.source_finality_certificate_root
        ),
        source_finality_evidence_root=governed_projection.source_finality_evidence_root,
    )
