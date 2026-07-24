from __future__ import annotations

import copy
import hashlib
import pickle
from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest

import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
import src.integration.zrpf_sampled_retrievability_v1.verifier as sampled_verifier
import src.integration.zrpf_spot_v7_governed_da_prerequisite as governed_da
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
    _GovernedOperationalPolicyMaterialV2,
    _GovernedOperationalPolicyProvenanceV1,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_full_blob_artifacts_v1,
    _TestOnlyFullBlobArtifactsV1,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zrpf_sampled_retrievability_v1 import (
    SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
    BeaconCommitmentV1,
    ProviderKeyLifecycleV1,
    SampledRetrievabilityPolicyV1,
    SignedProviderResponseV1,
    build_exact_evidence_bytes_v1,
    build_provider_response_bytes_v1,
    derive_exact_full_blob_target_v1,
    response_payload_hash_v1,
    verify_exact_evidence_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.verifier import (
    _AuthenticatedSampledRetrievabilityEvidenceV1,
)

EPOCH_ID = 40
CHECKED_EPOCH = 52
RETENTION_THROUGH_EPOCH = 65
EXACT_BLOB = b"exact governed full-blob DA bytes\x00\xff"
PRIVATE_KEYS = tuple("0x" + value.to_bytes(32, "big").hex() for value in (1, 2))


def _root(seed: int) -> str:
    return "0x" + (bytes([seed]) * 32).hex()


def _test_policy() -> _TestOnlySpotV7OperationalPolicyV1:
    return _TestOnlySpotV7OperationalPolicyV1(
        application_id=_root(1),
        chain_or_domain_id=_root(2),
        data_schema_id=_root(3),
        storage_policy_hash=_root(4),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_024 * 1_024,
        finality_network_id=_root(5),
        finality_protocol_id=_root(6),
        external_finality_policy_hash=_root(7),
        finality_verifier_set_root=_root(8),
        genesis_application_checkpoint_sequence=0,
        genesis_application_checkpoint_hash=_root(9),
    )


def _governed_policy(
    policy: _TestOnlySpotV7OperationalPolicyV1 | None = None,
    *,
    policy_revocation_epoch: int | None = None,
) -> _GovernedSpotV7OperationalPolicyV2:
    material = policy or _test_policy()
    provenance_bytes = b'{"schema":"test-only-operational-policy-provenance-v1"}'
    return _GovernedSpotV7OperationalPolicyV2(
        _GovernedOperationalPolicyMaterialV2(
            application_id=material.application_id,
            chain_or_domain_id=material.chain_or_domain_id,
            data_schema_id=material.data_schema_id,
            storage_policy_hash=material.storage_policy_hash,
            minimum_retention_epochs=material.minimum_retention_epochs,
            minimum_remaining_epochs=material.minimum_remaining_epochs,
            maximum_blob_bytes=material.maximum_blob_bytes,
            finality_network_id=material.finality_network_id,
            finality_protocol_id=material.finality_protocol_id,
            external_finality_policy_hash=material.external_finality_policy_hash,
            finality_verifier_set_root=material.finality_verifier_set_root,
            genesis_application_checkpoint_sequence=(
                material.genesis_application_checkpoint_sequence
            ),
            genesis_application_checkpoint_hash=(
                material.genesis_application_checkpoint_hash
            ),
        ),
        provenance=_GovernedOperationalPolicyProvenanceV1(
            evidence_root="0x" + hashlib.sha256(provenance_bytes).hexdigest(),
            exact_evidence_bytes=provenance_bytes,
            manifest_sha256=hashlib.sha256(b"test-only-manifest").hexdigest(),
            signer_registry_hash=_root(10),
            signature_quorum_report_hash=_root(11),
            policy_revision=3,
            policy_activation_epoch=0,
            policy_revocation_epoch=policy_revocation_epoch,
            signer_registry_revision=2,
            signer_registry_activation_epoch=0,
            signer_registry_revocation_epoch=None,
            evaluation_epoch=1,
        ),
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _full_blob_artifacts(
    policy: _TestOnlySpotV7OperationalPolicyV1 | None = None,
) -> _TestOnlyFullBlobArtifactsV1:
    return _build_test_only_full_blob_artifacts_v1(
        policy=policy or _test_policy(),
        epoch_id=EPOCH_ID,
        checked_epoch=CHECKED_EPOCH,
        retention_through_epoch=RETENTION_THROUGH_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
    )


def _full_blob_capability(
    policy: _GovernedSpotV7OperationalPolicyV2,
) -> _GovernedExactFullBlobPolicySatisfactionV2:
    artifacts = _full_blob_artifacts(policy._policy_for_atomic_store())
    projection = _GovernedFullBlobPolicyProjectionV1(
        application_id=policy._material.application_id,
        chain_or_domain_id=policy._material.chain_or_domain_id,
        epoch_id=artifacts.epoch_id,
        certificate_root=artifacts.certificate_root,
        data_root=artifacts.data_root,
        policy_root=artifacts.policy_root,
        exact_blob_sha256=artifacts.blob_sha256,
        checked_epoch=artifacts.checked_epoch,
        retention_through_epoch=artifacts.retention_through_epoch,
    )
    return _GovernedExactFullBlobPolicySatisfactionV2(
        projection,
        governed_policy=policy,
        exact_blob_bytes=artifacts.exact_blob_bytes,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
    )


def _provider(index: int) -> ProviderKeyLifecycleV1:
    return ProviderKeyLifecycleV1(
        provider_id=f"provider-{index}",
        key_id=f"provider-key-{index}",
        public_key=bls_public_key_hex_from_private_key_v0(PRIVATE_KEYS[index]),
        activation_epoch=0,
        revocation_epoch=None,
    )


def _sampled_result(
    *,
    application_id: str | None = None,
    chain_or_domain_id: str | None = None,
    epoch_id: int = EPOCH_ID,
    checked_epoch: int = CHECKED_EPOCH,
    data_schema_id: str | None = None,
    exact_blob_bytes: bytes = EXACT_BLOB,
    retention_through_epoch: int = RETENTION_THROUGH_EPOCH,
    storage_policy_hash: str | None = None,
    minimum_retention_epochs: int | None = None,
    minimum_remaining_epochs: int | None = None,
) -> _AuthenticatedSampledRetrievabilityEvidenceV1:
    operational = _test_policy()
    application = application_id or operational.application_id
    domain = chain_or_domain_id or operational.chain_or_domain_id
    storage = storage_policy_hash or operational.storage_policy_hash
    policy = SampledRetrievabilityPolicyV1.validated(
        application_id=application,
        chain_or_domain_id=domain,
        policy_revision=7,
        activation_epoch=0,
        revocation_epoch=None,
        storage_policy_hash=storage,
        beacon_source_id=_root(12),
        beacon_policy_hash=_root(13),
        minimum_retention_epochs=(
            operational.minimum_retention_epochs
            if minimum_retention_epochs is None
            else minimum_retention_epochs
        ),
        minimum_remaining_epochs=(
            operational.minimum_remaining_epochs
            if minimum_remaining_epochs is None
            else minimum_remaining_epochs
        ),
        challenge_count=1,
        response_window_epochs=2,
        minimum_provider_responses=2,
        providers=(_provider(0), _provider(1)),
    )
    target = derive_exact_full_blob_target_v1(
        application_id=application,
        chain_or_domain_id=domain,
        epoch_id=epoch_id,
        data_schema_id=data_schema_id or operational.data_schema_id,
        exact_blob_bytes=exact_blob_bytes,
        retention_through_epoch=retention_through_epoch,
        storage_policy_hash=storage,
    )
    beacon = BeaconCommitmentV1.validated(
        source_id=policy.beacon_source_id,
        policy_hash=policy.beacon_policy_hash,
        beacon_epoch=checked_epoch,
        commitment=_root(14),
    )
    responses: list[SignedProviderResponseV1] = []
    for index, provider in enumerate(policy.providers):
        response_bytes = build_provider_response_bytes_v1(
            policy=policy,
            target=target,
            beacon=beacon,
            checked_epoch=checked_epoch,
            response_epoch=checked_epoch + 1,
            provider_id=provider.provider_id,
            key_id=provider.key_id,
            exact_blob_bytes=exact_blob_bytes,
        )
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind=SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
            payload_hash=response_payload_hash_v1(response_bytes),
            signer_id=provider.provider_id,
            key_id=provider.key_id,
            private_key_hex=PRIVATE_KEYS[index],
        )
        responses.append(SignedProviderResponseV1(response_bytes, envelope))
    evidence = build_exact_evidence_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=checked_epoch,
        exact_blob_bytes=exact_blob_bytes,
        signed_responses=tuple(responses),
    )
    return verify_exact_evidence_v1(
        evidence,
        expected_policy=policy,
        expected_target=target,
        expected_beacon=beacon,
        checked_epoch=checked_epoch,
    )


def _valid_prerequisites() -> tuple[
    _GovernedSpotV7OperationalPolicyV2,
    _GovernedExactFullBlobPolicySatisfactionV2,
    _AuthenticatedSampledRetrievabilityEvidenceV1,
]:
    policy = _governed_policy()
    return policy, _full_blob_capability(policy), _sampled_result()


def test_private_combined_da_prerequisite_binds_exact_scoped_evidence() -> None:
    policy, full_blob, sampled = _valid_prerequisites()

    result = governed_da._bind_governed_spot_v7_da_prerequisite_v1(
        operational_policy=policy,
        exact_full_blob=full_blob,
        sampled_response=sampled,
    )
    projection = result._projection_for_downstream_binding_v1()

    assert projection.application_id == _test_policy().application_id
    assert projection.chain_or_domain_id == _test_policy().chain_or_domain_id
    assert projection.epoch_id == EPOCH_ID
    assert projection.checked_epoch == CHECKED_EPOCH
    assert projection.certificate_root == full_blob._projection.certificate_root
    assert projection.data_root == full_blob._projection.data_root
    assert projection.retention_through_epoch == RETENTION_THROUGH_EPOCH
    assert projection.full_blob_policy_root == full_blob._projection.policy_root
    assert projection.sampled_policy_root == sampled.policy_root
    assert projection.exact_blob_sha256 == full_blob._projection.exact_blob_sha256
    assert projection.accepted_provider_ids == ("provider-0", "provider-1")
    assert projection.accepted_provider_set_root == hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        ["provider-0", "provider-1"],
    )
    assert projection.sampled_evidence_sha256 == sampled.evidence_sha256
    assert (
        projection.operational_policy_provenance_root
        == policy._provenance.evidence_root
    )
    assert (
        projection.operational_policy_manifest_sha256
        == policy._provenance.manifest_sha256
    )
    assert projection.beacon_source_id == _root(12)
    assert projection.beacon_policy_hash == _root(13)
    assert projection.beacon_epoch == CHECKED_EPOCH
    assert projection.beacon_commitment == _root(14)
    assert result.governed_exact_full_blob_policy_satisfied is True
    assert result.authenticated_sampled_response_scoped_to_checked_epoch is True
    assert result.operational_policy_release_provenance_bound is True
    assert result.sampled_policy_governance_provenance_verified is False
    assert result.current_operational_policy_release_head_verified is False
    assert result.governed_beacon_provenance_verified is False
    assert result.beacon_unpredictability_verified is False
    assert result.response_timing_provenance_verified is False
    assert result.provider_independence_verified is False
    assert result.continuous_availability_verified is False
    assert result.public_future_availability_verified is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


@pytest.mark.parametrize(
    ("parameter", "replacement", "message"),
    (
        ("operational_policy", {"verified": True}, "exact governed policy"),
        ("operational_policy", True, "exact governed policy"),
        ("operational_policy", b'{"verified":true}', "exact governed policy"),
        ("exact_full_blob", {"verified": True}, "exact sealed full-blob"),
        ("exact_full_blob", True, "exact sealed full-blob"),
        ("exact_full_blob", b'{"verified":true}', "exact sealed full-blob"),
        ("sampled_response", {"verified": True}, "authenticated sampled response"),
        ("sampled_response", True, "authenticated sampled response"),
        (
            "sampled_response",
            b'{"verified":true}',
            "authenticated sampled response",
        ),
    ),
)
def test_raw_mapping_or_boolean_cannot_mint_combined_da_capability(
    parameter: str,
    replacement: object,
    message: str,
) -> None:
    policy, full_blob, sampled = _valid_prerequisites()
    inputs: dict[str, object] = {
        "operational_policy": policy,
        "exact_full_blob": full_blob,
        "sampled_response": sampled,
    }
    inputs[parameter] = replacement

    with pytest.raises(TypeError, match=message):
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(**inputs)


@pytest.mark.parametrize(
    ("sampled_changes", "code"),
    (
        ({"application_id": _root(20)}, "APPLICATION_MISMATCH"),
        ({"chain_or_domain_id": _root(21)}, "DOMAIN_MISMATCH"),
        ({"epoch_id": EPOCH_ID + 1}, "EPOCH_MISMATCH"),
        ({"checked_epoch": CHECKED_EPOCH + 1}, "CHECKED_EPOCH_MISMATCH"),
        (
            {"retention_through_epoch": RETENTION_THROUGH_EPOCH + 1},
            "RETENTION_MISMATCH",
        ),
        ({"storage_policy_hash": _root(22)}, "STORAGE_POLICY_MISMATCH"),
        ({"exact_blob_bytes": b"different exact blob"}, "DATA_ROOT_MISMATCH"),
        ({"data_schema_id": _root(23)}, "CERTIFICATE_ROOT_MISMATCH"),
    ),
)
def test_every_cross_scope_mismatch_rejects_with_stable_code(
    sampled_changes: dict[str, object],
    code: str,
) -> None:
    policy = _governed_policy()
    full_blob = _full_blob_capability(policy)
    sampled = _sampled_result(**sampled_changes)  # type: ignore[arg-type]

    with pytest.raises(
        governed_da.SpotV7GovernedDaPrerequisiteBindingErrorV1
    ) as rejected:
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(
            operational_policy=policy,
            exact_full_blob=full_blob,
            sampled_response=sampled,
        )

    assert rejected.value.code == code


def test_full_blob_must_retain_the_exact_governed_policy_capability() -> None:
    retained_policy = _governed_policy()
    full_blob = _full_blob_capability(retained_policy)
    substituted_policy = _governed_policy()

    with pytest.raises(
        governed_da.SpotV7GovernedDaPrerequisiteBindingErrorV1
    ) as rejected:
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(
            operational_policy=substituted_policy,
            exact_full_blob=full_blob,
            sampled_response=_sampled_result(),
        )

    assert rejected.value.code == "POLICY_CAPABILITY_MISMATCH"


def test_governed_policy_provenance_must_remain_active_at_checked_epoch() -> None:
    policy = _governed_policy(policy_revocation_epoch=CHECKED_EPOCH)

    with pytest.raises(
        governed_da.SpotV7GovernedDaPrerequisiteBindingErrorV1
    ) as rejected:
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(
            operational_policy=policy,
            exact_full_blob=_full_blob_capability(policy),
            sampled_response=_sampled_result(),
        )

    assert rejected.value.code == "POLICY_PROVENANCE_INACTIVE"


def test_sampled_retention_policy_cannot_be_weaker_than_governed_policy() -> None:
    policy = _governed_policy()
    sampled = _sampled_result(minimum_remaining_epochs=4)

    with pytest.raises(
        governed_da.SpotV7GovernedDaPrerequisiteBindingErrorV1
    ) as rejected:
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(
            operational_policy=policy,
            exact_full_blob=_full_blob_capability(policy),
            sampled_response=sampled,
        )

    assert rejected.value.code == "SAMPLED_RETENTION_POLICY_WEAKER"


def test_exact_full_blob_digest_drift_rejects_before_combined_capability() -> None:
    policy, full_blob, sampled = _valid_prerequisites()
    object.__setattr__(
        full_blob,
        "_projection",
        replace(full_blob._projection, exact_blob_sha256=_root(24)),
    )

    with pytest.raises(
        governed_da.SpotV7GovernedDaPrerequisiteBindingErrorV1
    ) as rejected:
        governed_da._bind_governed_spot_v7_da_prerequisite_v1(
            operational_policy=policy,
            exact_full_blob=full_blob,
            sampled_response=sampled,
        )

    assert rejected.value.code == "EXACT_BLOB_DIGEST_MISMATCH"


def test_combined_capability_cannot_be_mutated_copied_serialized_or_forged() -> None:
    policy, full_blob, sampled = _valid_prerequisites()
    result = governed_da._bind_governed_spot_v7_da_prerequisite_v1(
        operational_policy=policy,
        exact_full_blob=full_blob,
        sampled_response=sampled,
    )

    with pytest.raises(TypeError, match="cannot be mutated"):
        result._projection = replace(result._projection, epoch_id=EPOCH_ID + 1)
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(result)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(result)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(result)
    unchecked_constructor = cast(
        Callable[..., object],
        governed_da._GovernedSpotV7DataAvailabilityPrerequisiteV1,
    )
    with pytest.raises(TypeError, match="module-private seal"):
        unchecked_constructor(
            result._projection,
            operational_policy=policy,
            exact_full_blob=full_blob,
            sampled_response=sampled,
            seal=object(),
        )


def test_sampled_result_private_projection_detects_evidence_digest_drift() -> None:
    result = _sampled_result()
    object.__setattr__(result, "_exact_evidence_bytes", result.exact_evidence_bytes + b"\n")

    with pytest.raises(ValueError, match="evidence digest drift"):
        result._projection_for_spot_v7_da_prerequisite_v1()


def test_combined_da_module_exports_no_public_authority_api() -> None:
    assert governed_da.__all__ == ()
    assert sampled_verifier._AuthenticatedSampledRetrievabilityEvidenceV1.__module__.endswith(
        ".verifier"
    )
