"""Authority-false Spot V7 V2 operational packet and exact store projection.

This module joins four already-sealed prerequisite values. It retains the exact
blob, DA certificate, finality certificate, and external-finality evidence,
then deterministically rederives the schema-V2 persistence packet. No function
here authenticates raw caller data or promotes settlement or production
authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _AuthenticatedCheckpointFinalityProjectionV2,
    _GovernedFullBlobPolicyProjectionV1,
    _GovernedOperationalPolicyProjectionV1,
    _require_finality_binding,
    _require_full_blob_binding,
    _require_policy_binding,
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    MAX_FINALITY_CERTIFICATE_BYTES_V2,
    MAX_FINALITY_EVIDENCE_BYTES_V2,
    MAX_FULL_BLOB_BYTES_V1,
    MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
    _derive_test_only_checkpoint_finality_artifacts_v2,
    _derive_test_only_full_blob_artifacts_v1,
    _seal_test_only_spot_v7_operational_commit_v1,
    _TestOnlyCheckpointFinalityArtifactsV2,
    _TestOnlyFullBlobArtifactsV1,
    _TestOnlySpotV7OperationalCommitInputV1,
    _TestOnlySpotV7OperationalCommitV1,
    _TestOnlySpotV7OperationalPolicyV1,
)


@dataclass(frozen=True, slots=True)
class _GovernedOperationalPolicyMaterialV2:
    """Complete immutable policy material behind the governed V2 policy seal."""

    application_id: str
    chain_or_domain_id: str
    data_schema_id: str
    storage_policy_hash: str
    minimum_retention_epochs: int
    minimum_remaining_epochs: int
    maximum_blob_bytes: int
    finality_network_id: str
    finality_protocol_id: str
    external_finality_policy_hash: str
    finality_verifier_set_root: str
    genesis_application_checkpoint_sequence: int
    genesis_application_checkpoint_hash: str

    def __post_init__(self) -> None:
        self._to_authority_false_store_policy()

    def _to_authority_false_store_policy(self) -> _TestOnlySpotV7OperationalPolicyV1:
        return _TestOnlySpotV7OperationalPolicyV1(
            application_id=self.application_id,
            chain_or_domain_id=self.chain_or_domain_id,
            data_schema_id=self.data_schema_id,
            storage_policy_hash=self.storage_policy_hash,
            minimum_retention_epochs=self.minimum_retention_epochs,
            minimum_remaining_epochs=self.minimum_remaining_epochs,
            maximum_blob_bytes=self.maximum_blob_bytes,
            finality_network_id=self.finality_network_id,
            finality_protocol_id=self.finality_protocol_id,
            external_finality_policy_hash=self.external_finality_policy_hash,
            finality_verifier_set_root=self.finality_verifier_set_root,
            genesis_application_checkpoint_sequence=(self.genesis_application_checkpoint_sequence),
            genesis_application_checkpoint_hash=(self.genesis_application_checkpoint_hash),
        )


class _GovernedOperationalPolicySealV2:
    __slots__ = ()


class _GovernedExactFullBlobPolicySealV2:
    __slots__ = ()


class _AuthenticatedExactCheckpointFinalitySealV2:
    __slots__ = ()


class _AtomicEconomicCommitSealV2:
    __slots__ = ()


_GOVERNED_OPERATIONAL_POLICY_SEAL_V2 = _GovernedOperationalPolicySealV2()
_GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2 = _GovernedExactFullBlobPolicySealV2()
_AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2 = _AuthenticatedExactCheckpointFinalitySealV2()
_ATOMIC_ECONOMIC_COMMIT_SEAL_V2 = _AtomicEconomicCommitSealV2()


class _NonTransferableOperationalCapabilityV2:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 V2 operational capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 V2 operational capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 V2 operational capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 V2 operational capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 V2 operational capability cannot be serialized")


@final
class _GovernedSpotV7OperationalPolicyV2(_NonTransferableOperationalCapabilityV2):
    """Release-adapter-owned complete policy material for the V2 store sink."""

    __slots__ = ("_material", "_projection", "_seal")

    _material: _GovernedOperationalPolicyMaterialV2
    _projection: _GovernedOperationalPolicyProjectionV1
    _seal: _GovernedOperationalPolicySealV2

    def __init__(
        self,
        material: _GovernedOperationalPolicyMaterialV2,
        *,
        seal: _GovernedOperationalPolicySealV2,
    ) -> None:
        if type(material) is not _GovernedOperationalPolicyMaterialV2:
            raise TypeError("governed operational policy material has the wrong type")
        if seal is not _GOVERNED_OPERATIONAL_POLICY_SEAL_V2:
            raise TypeError("V2 operational policy requires the module-private governed seal")
        store_policy = material._to_authority_false_store_policy()
        projection = _GovernedOperationalPolicyProjectionV1(
            application_id=material.application_id,
            chain_or_domain_id=material.chain_or_domain_id,
            full_blob_da_policy_root=store_policy.full_blob_policy_root,
            checkpoint_finality_policy_root=(store_policy.checkpoint_finality_policy_root),
        )
        object.__setattr__(self, "_material", material)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_OPERATIONAL_POLICY_SEAL_V2

    def _policy_for_atomic_store(self) -> _TestOnlySpotV7OperationalPolicyV1:
        if not self._has_private_seal():
            raise TypeError("V2 operational policy lacks its private governed seal")
        policy = self._material._to_authority_false_store_policy()
        expected = _GovernedOperationalPolicyProjectionV1(
            application_id=policy.application_id,
            chain_or_domain_id=policy.chain_or_domain_id,
            full_blob_da_policy_root=policy.full_blob_policy_root,
            checkpoint_finality_policy_root=policy.checkpoint_finality_policy_root,
        )
        if expected != self._projection:
            raise ValueError("V2 operational policy projection drift")
        return policy

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@final
class _GovernedExactFullBlobPolicySatisfactionV2(_NonTransferableOperationalCapabilityV2):
    """Exact blob and canonical certificate retained by a governed DA adapter."""

    __slots__ = (
        "_projection",
        "_exact_blob_bytes",
        "_exact_certificate_bytes",
        "_seal",
    )

    _projection: _GovernedFullBlobPolicyProjectionV1
    _exact_blob_bytes: bytes
    _exact_certificate_bytes: bytes
    _seal: _GovernedExactFullBlobPolicySealV2

    def __init__(
        self,
        projection: _GovernedFullBlobPolicyProjectionV1,
        *,
        exact_blob_bytes: bytes,
        exact_certificate_bytes: bytes,
        seal: _GovernedExactFullBlobPolicySealV2,
    ) -> None:
        if type(projection) is not _GovernedFullBlobPolicyProjectionV1:
            raise TypeError("exact full-blob projection has the wrong type")
        if seal is not _GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2:
            raise TypeError("exact full-blob result requires the module-private governed seal")
        _require_exact_artifact_bytes(
            exact_blob_bytes,
            name="exact full blob",
            maximum=MAX_FULL_BLOB_BYTES_V1,
        )
        _require_exact_artifact_bytes(
            exact_certificate_bytes,
            name="exact full-blob certificate",
            maximum=MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
        )
        if _sha256(exact_blob_bytes) != projection.exact_blob_sha256:
            raise ValueError("exact full-blob SHA-256 disagrees with its sealed projection")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_blob_bytes", exact_blob_bytes)
        object.__setattr__(self, "_exact_certificate_bytes", exact_certificate_bytes)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2


@final
class _AuthenticatedExactCheckpointFinalityTransitionV2(_NonTransferableOperationalCapabilityV2):
    """Exact certificate and authenticated external-finality evidence packet."""

    __slots__ = (
        "_projection",
        "_exact_certificate_bytes",
        "_exact_finality_evidence_bytes",
        "_seal",
    )

    _projection: _AuthenticatedCheckpointFinalityProjectionV2
    _exact_certificate_bytes: bytes
    _exact_finality_evidence_bytes: bytes
    _seal: _AuthenticatedExactCheckpointFinalitySealV2

    def __init__(
        self,
        projection: _AuthenticatedCheckpointFinalityProjectionV2,
        *,
        exact_certificate_bytes: bytes,
        exact_finality_evidence_bytes: bytes,
        seal: _AuthenticatedExactCheckpointFinalitySealV2,
    ) -> None:
        if type(projection) is not _AuthenticatedCheckpointFinalityProjectionV2:
            raise TypeError("exact checkpoint-finality projection has the wrong type")
        if seal is not _AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2:
            raise TypeError(
                "exact checkpoint finality requires the module-private authenticated seal"
            )
        _require_exact_artifact_bytes(
            exact_certificate_bytes,
            name="exact checkpoint-finality certificate",
            maximum=MAX_FINALITY_CERTIFICATE_BYTES_V2,
        )
        _require_exact_artifact_bytes(
            exact_finality_evidence_bytes,
            name="exact external-finality evidence",
            maximum=MAX_FINALITY_EVIDENCE_BYTES_V2,
        )
        if _sha256(exact_finality_evidence_bytes) != projection.finality_evidence_root:
            raise ValueError("exact finality evidence root disagrees with its sealed projection")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_certificate_bytes", exact_certificate_bytes)
        object.__setattr__(
            self,
            "_exact_finality_evidence_bytes",
            exact_finality_evidence_bytes,
        )
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2


@final
class _SpotV7AtomicEconomicCommitCapabilityV2(_NonTransferableOperationalCapabilityV2):
    """Authority-false exact packet for the completed atomic V2 store sink."""

    __slots__ = (
        "_settlement",
        "_policy",
        "_data_availability",
        "_finality",
        "_seal",
    )

    _settlement: _GovernedFirecrackerSpotV7SettlementV1
    _policy: _GovernedSpotV7OperationalPolicyV2
    _data_availability: _GovernedExactFullBlobPolicySatisfactionV2
    _finality: _AuthenticatedExactCheckpointFinalityTransitionV2
    _seal: _AtomicEconomicCommitSealV2

    def __init__(
        self,
        *,
        settlement: _GovernedFirecrackerSpotV7SettlementV1,
        policy: _GovernedSpotV7OperationalPolicyV2,
        data_availability: _GovernedExactFullBlobPolicySatisfactionV2,
        finality: _AuthenticatedExactCheckpointFinalityTransitionV2,
        seal: _AtomicEconomicCommitSealV2,
    ) -> None:
        if seal is not _ATOMIC_ECONOMIC_COMMIT_SEAL_V2:
            raise TypeError("V2 atomic economic commit requires the module-private seal")
        _build_authority_false_store_packet_v2(
            settlement=settlement,
            policy=policy,
            data_availability=data_availability,
            finality=finality,
        )
        object.__setattr__(self, "_settlement", settlement)
        object.__setattr__(self, "_policy", policy)
        object.__setattr__(self, "_data_availability", data_availability)
        object.__setattr__(self, "_finality", finality)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _ATOMIC_ECONOMIC_COMMIT_SEAL_V2

    def _packet_for_atomic_store(self) -> _TestOnlySpotV7OperationalCommitV1:
        if not self._has_private_seal():
            raise TypeError("V2 atomic economic commit lacks its module-private seal")
        return _build_authority_false_store_packet_v2(
            settlement=self._settlement,
            policy=self._policy,
            data_availability=self._data_availability,
            finality=self._finality,
        )

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _bind_spot_v7_operational_commit_capability_v2(
    *,
    settlement: object,
    policy: object,
    data_availability: object,
    finality: object,
) -> _SpotV7AtomicEconomicCommitCapabilityV2:
    """Join four pre-sealed prerequisites into an authority-false V2 packet."""

    return _SpotV7AtomicEconomicCommitCapabilityV2(
        settlement=_require_settlement_capability(settlement),
        policy=_require_operational_policy_v2(policy),
        data_availability=_require_exact_full_blob_satisfaction_v2(data_availability),
        finality=_require_exact_authenticated_finality_v2(finality),
        seal=_ATOMIC_ECONOMIC_COMMIT_SEAL_V2,
    )


def _require_operational_policy_v2(
    value: object,
) -> _GovernedSpotV7OperationalPolicyV2:
    if type(value) is not _GovernedSpotV7OperationalPolicyV2:
        raise TypeError("V2 operational gate requires the exact governed policy")
    if not value._has_private_seal():
        raise TypeError("V2 operational gate requires the exact governed policy")
    value._policy_for_atomic_store()
    return value


def _require_exact_full_blob_satisfaction_v2(
    value: object,
) -> _GovernedExactFullBlobPolicySatisfactionV2:
    if type(value) is not _GovernedExactFullBlobPolicySatisfactionV2:
        raise TypeError("V2 operational gate requires exact sealed full-blob artifacts")
    if not value._has_private_seal():
        raise TypeError("V2 operational gate requires exact sealed full-blob artifacts")
    return value


def _require_exact_authenticated_finality_v2(
    value: object,
) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    if type(value) is not _AuthenticatedExactCheckpointFinalityTransitionV2:
        raise TypeError("V2 operational gate requires exact authenticated finality artifacts")
    if not value._has_private_seal():
        raise TypeError("V2 operational gate requires exact authenticated finality artifacts")
    return value


def _build_authority_false_store_packet_v2(
    *,
    settlement: object,
    policy: object,
    data_availability: object,
    finality: object,
) -> _TestOnlySpotV7OperationalCommitV1:
    settlement_value = _require_settlement_capability(settlement)
    policy_value = _require_operational_policy_v2(policy)
    da_value = _require_exact_full_blob_satisfaction_v2(data_availability)
    finality_value = _require_exact_authenticated_finality_v2(finality)
    candidate = settlement_value._candidate_for_atomic_store()
    policy_projection = policy_value._projection
    _require_policy_binding(candidate, policy_projection)
    _require_full_blob_binding(candidate, policy_projection, da_value._projection)
    _require_finality_binding(candidate, policy_projection, finality_value._projection)

    store_policy = policy_value._policy_for_atomic_store()
    store_settlement = _seal_test_only_spot_v7_settlement_v1(candidate)
    store_da = _derive_test_only_full_blob_artifacts_v1(
        policy=store_policy,
        epoch_id=da_value._projection.epoch_id,
        checked_epoch=da_value._projection.checked_epoch,
        retention_through_epoch=da_value._projection.retention_through_epoch,
        exact_blob_bytes=da_value._exact_blob_bytes,
        exact_certificate_bytes=da_value._exact_certificate_bytes,
    )
    _require_exact_da_projection(store_da, da_value._projection)
    store_finality = _derive_test_only_checkpoint_finality_artifacts_v2(
        policy=store_policy,
        settlement=store_settlement,
        prior_application_checkpoint_sequence=(
            finality_value._projection.prior_application_checkpoint_sequence
        ),
        prior_application_checkpoint_hash=(
            finality_value._projection.prior_application_checkpoint_hash
        ),
        next_application_checkpoint_hash=(
            finality_value._projection.next_application_checkpoint_hash
        ),
        exact_certificate_bytes=finality_value._exact_certificate_bytes,
        exact_finality_evidence_bytes=(finality_value._exact_finality_evidence_bytes),
    )
    _require_exact_finality_projection(store_finality, finality_value._projection)
    return _seal_test_only_spot_v7_operational_commit_v1(
        _TestOnlySpotV7OperationalCommitInputV1(
            settlement=store_settlement,
            policy=store_policy,
            data_availability=store_da,
            finality=store_finality,
        )
    )


def _require_exact_da_projection(
    observed: _TestOnlyFullBlobArtifactsV1,
    expected: _GovernedFullBlobPolicyProjectionV1,
) -> None:
    checks = (
        observed.epoch_id == expected.epoch_id,
        observed.certificate_root == expected.certificate_root,
        observed.data_root == expected.data_root,
        observed.policy_root == expected.policy_root,
        observed.blob_sha256 == expected.exact_blob_sha256,
        observed.checked_epoch == expected.checked_epoch,
        observed.retention_through_epoch == expected.retention_through_epoch,
    )
    if not all(checks):
        raise ValueError("exact V2 DA projection differs from recomposed artifacts")


def _require_exact_finality_projection(
    observed: _TestOnlyCheckpointFinalityArtifactsV2,
    expected: _AuthenticatedCheckpointFinalityProjectionV2,
) -> None:
    checks = (
        observed.epoch_id == expected.epoch_id,
        observed.proof_journal_hash == expected.proof_journal_hash,
        observed.post_state_root == expected.post_state_root,
        observed.policy_root == expected.policy_root,
        observed.certificate_root == expected.certificate_root,
        observed.finality_evidence_root == expected.finality_evidence_root,
        observed.prior_application_checkpoint_sequence
        == expected.prior_application_checkpoint_sequence,
        observed.prior_application_checkpoint_hash == expected.prior_application_checkpoint_hash,
        observed.next_application_checkpoint_sequence
        == expected.next_application_checkpoint_sequence,
        observed.next_application_checkpoint_hash == expected.next_application_checkpoint_hash,
    )
    if not all(checks):
        raise ValueError("exact V2 finality projection differs from recomposed artifacts")


def _sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_exact_artifact_bytes(value: bytes, *, name: str, maximum: int) -> None:
    if type(value) is not bytes or not value or len(value) > maximum:
        raise ValueError(f"{name} must be exact nonempty bytes within {maximum}")


__all__: list[str] = []
