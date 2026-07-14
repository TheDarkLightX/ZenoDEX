"""CBC tests for the versioned governed Spot V7 DA prerequisite V2."""

from __future__ import annotations

import copy
import hashlib
import pickle
from dataclasses import replace

import pytest

import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
    _GovernedOperationalPolicyProvenanceV1,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_full_blob_artifacts_v1,
)
from src.integration.zeno_ledger_signature import (
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zrpf_sampled_retrievability_v1 import (
    SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
    SignedProviderResponseV1,
    build_exact_evidence_bytes_v1,
    build_provider_response_bytes_v1,
    derive_exact_full_blob_target_v1,
    response_payload_hash_v1,
    verify_exact_evidence_v1,
)
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    SpotV7GovernedDaPrerequisiteBindingErrorV2,
    _bind_governed_spot_v7_da_prerequisite_v2,
    _bind_governed_spot_v7_sampled_response_v1,
    _GovernedSpotV7DataAvailabilityPrerequisiteV2,
    _GovernedSpotV7SampledResponseV1,
)
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    bind_governed_spot_v7_lagged_checkpoint_beacon_v1,
)
from tests.integration.test_zrpf_spot_v7_lagged_checkpoint_beacon import _finality
from tests.integration.test_zrpf_spot_v7_operational_policy_v3 import (
    POLICY_ACTIVATION_EPOCH,
    _load,
    _manifest,
    _registry,
)

EPOCH_ID = 10
CHECKED_EPOCH = POLICY_ACTIVATION_EPOCH
RETENTION_THROUGH_EPOCH = 25
EXACT_BLOB = b"a" * 65_536 + b"b" * 65_536 + b"tail"
PROVIDER_PRIVATE_KEYS = (
    "0x" + (21).to_bytes(32, "big").hex(),
    "0x" + (22).to_bytes(32, "big").hex(),
)


def _policy_v3():
    registry = _registry()
    return _load(_manifest(registry), registry)


def _legacy_policy(
    policy_v3,
    *,
    base_override=None,
) -> _GovernedSpotV7OperationalPolicyV2:
    base = base_override or policy_v3._material.base_material
    evidence = b'{"schema":"test-only-operational-policy-provenance-v1"}'
    return _GovernedSpotV7OperationalPolicyV2(
        base,
        provenance=_GovernedOperationalPolicyProvenanceV1(
            evidence_root="0x" + hashlib.sha256(evidence).hexdigest(),
            exact_evidence_bytes=evidence,
            manifest_sha256=hashlib.sha256(b"test-only-v1-manifest").hexdigest(),
            signer_registry_hash="0x" + hashlib.sha256(b"registry-v1").hexdigest(),
            signature_quorum_report_hash=(
                "0x" + hashlib.sha256(b"quorum-v1").hexdigest()
            ),
            policy_revision=1,
            policy_activation_epoch=0,
            policy_revocation_epoch=None,
            signer_registry_revision=1,
            signer_registry_activation_epoch=0,
            signer_registry_revocation_epoch=None,
            evaluation_epoch=1,
        ),
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _full_blob(policy_v3) -> _GovernedExactFullBlobPolicySatisfactionV2:
    legacy = _legacy_policy(policy_v3)
    base = legacy._policy_for_atomic_store()
    artifacts = _build_test_only_full_blob_artifacts_v1(
        policy=base,
        epoch_id=EPOCH_ID,
        checked_epoch=CHECKED_EPOCH,
        retention_through_epoch=RETENTION_THROUGH_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
    )
    projection = _GovernedFullBlobPolicyProjectionV1(
        application_id=base.application_id,
        chain_or_domain_id=base.chain_or_domain_id,
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
        governed_policy=legacy,
        exact_blob_bytes=artifacts.exact_blob_bytes,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        seal=operational_v2._GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
    )


def _beacon(policy_v3, *, checkpoint_hash: str | None = None):
    policy_root = (
        policy_v3._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    )
    return bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=policy_v3,
        source_finality=_finality(policy_root, checkpoint_hash=checkpoint_hash),
        checked_epoch=CHECKED_EPOCH,
    )


def _sampled(policy_v3, governed_beacon):
    policy = policy_v3._sampled_policy_for_governed_da_v2()
    base = policy_v3._material.base_material
    beacon = governed_beacon._beacon_for_sampled_retrievability_v1()
    target = derive_exact_full_blob_target_v1(
        application_id=base.application_id,
        chain_or_domain_id=base.chain_or_domain_id,
        epoch_id=EPOCH_ID,
        data_schema_id=base.data_schema_id,
        exact_blob_bytes=EXACT_BLOB,
        retention_through_epoch=RETENTION_THROUGH_EPOCH,
        storage_policy_hash=base.storage_policy_hash,
    )
    responses: list[SignedProviderResponseV1] = []
    for index, provider in enumerate(policy.providers):
        response_bytes = build_provider_response_bytes_v1(
            policy=policy,
            target=target,
            beacon=beacon,
            checked_epoch=CHECKED_EPOCH,
            response_epoch=CHECKED_EPOCH + 1,
            provider_id=provider.provider_id,
            key_id=provider.key_id,
            exact_blob_bytes=EXACT_BLOB,
        )
        envelope = build_bls_signed_artifact_envelope_v0(
            payload_kind=SAMPLED_RETRIEVABILITY_RESPONSE_PAYLOAD_KIND_V1,
            payload_hash=response_payload_hash_v1(response_bytes),
            signer_id=provider.provider_id,
            key_id=provider.key_id,
            private_key_hex=PROVIDER_PRIVATE_KEYS[index],
        )
        responses.append(SignedProviderResponseV1(response_bytes, envelope))
    evidence = build_exact_evidence_bytes_v1(
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
        exact_blob_bytes=EXACT_BLOB,
        signed_responses=tuple(responses),
    )
    return verify_exact_evidence_v1(
        evidence,
        expected_policy=policy,
        expected_target=target,
        expected_beacon=beacon,
        checked_epoch=CHECKED_EPOCH,
    )


def _valid():
    policy = _policy_v3()
    beacon = _beacon(policy)
    sampled = _sampled(policy, beacon)
    governed_sample = _bind_governed_spot_v7_sampled_response_v1(
        operational_policy=policy,
        governed_beacon=beacon,
        sampled_response=sampled,
    )
    return policy, beacon, sampled, governed_sample, _full_blob(policy)


def test_governed_sample_wrapper_binds_signed_policy_and_checkpoint_beacon() -> None:
    policy, beacon, sampled, governed_sample, _ = _valid()

    assert type(governed_sample) is _GovernedSpotV7SampledResponseV1
    projection = governed_sample._projection_for_combined_da_v2()
    assert projection.sampled == sampled._projection
    assert projection.operational_policy_provenance_root == (
        policy._projection.policy_provenance_root
    )
    assert projection.source_checkpoint_sequence == CHECKED_EPOCH - 1
    assert projection.source_checkpoint_hash == beacon._projection.source_checkpoint_hash
    assert governed_sample.sampled_policy_governance_provenance_verified is True
    assert governed_sample.governed_beacon_provenance_verified is True
    assert governed_sample.beacon_unpredictability_verified is False
    assert governed_sample.response_timing_provenance_verified is False
    assert governed_sample.provider_independence_verified is False
    assert governed_sample.continuous_availability_verified is False
    assert governed_sample.public_future_availability_verified is False
    assert governed_sample.release_authority is False
    assert governed_sample.settlement_authority is False
    assert governed_sample.production_authority is False


def test_combined_da_v2_advances_only_two_governance_provenance_claims() -> None:
    policy, _, _, governed_sample, full_blob = _valid()

    combined = _bind_governed_spot_v7_da_prerequisite_v2(
        operational_policy=policy,
        exact_full_blob=full_blob,
        governed_sampled_response=governed_sample,
    )

    assert type(combined) is _GovernedSpotV7DataAvailabilityPrerequisiteV2
    projection = combined._projection_for_downstream_binding_v2()
    assert projection.base.application_id == policy._projection.application_id
    assert projection.base.epoch_id == EPOCH_ID
    assert projection.base.checked_epoch == CHECKED_EPOCH
    assert projection.base.sampled_policy_root == policy._projection.sampled_policy_root
    assert projection.zeno_ledger_chain_id == policy._projection.zeno_ledger_chain_id
    assert projection.source_checkpoint_sequence == CHECKED_EPOCH - 1
    assert combined.governed_exact_full_blob_policy_satisfied is True
    assert combined.authenticated_sampled_response_scoped_to_checked_epoch is True
    assert combined.operational_policy_release_provenance_bound is True
    assert combined.sampled_policy_governance_provenance_verified is True
    assert combined.governed_beacon_provenance_verified is True
    assert combined.current_operational_policy_release_head_verified is False
    assert combined.beacon_unpredictability_verified is False
    assert combined.response_timing_provenance_verified is False
    assert combined.provider_independence_verified is False
    assert combined.continuous_availability_verified is False
    assert combined.public_future_availability_verified is False
    assert combined.release_authority is False
    assert combined.settlement_authority is False
    assert combined.production_authority is False


def test_governed_sample_rejects_different_governed_beacon() -> None:
    policy = _policy_v3()
    first_beacon = _beacon(policy)
    sampled = _sampled(policy, first_beacon)
    second_beacon = _beacon(policy, checkpoint_hash="0x" + hashlib.sha256(b"other").hexdigest())

    with pytest.raises(SpotV7GovernedDaPrerequisiteBindingErrorV2) as captured:
        _bind_governed_spot_v7_sampled_response_v1(
            operational_policy=policy,
            governed_beacon=second_beacon,
            sampled_response=sampled,
        )
    assert captured.value.code == "GOVERNED_BEACON_MISMATCH"


def test_combined_da_v2_rejects_full_blob_policy_substitution() -> None:
    policy, _, _, governed_sample, full_blob = _valid()
    other_base = replace(
        policy._material.base_material,
        storage_policy_hash="0x" + hashlib.sha256(b"other-storage").hexdigest(),
    )
    other_legacy = _legacy_policy(policy, base_override=other_base)
    object.__setattr__(full_blob, "_governed_policy", other_legacy)

    with pytest.raises(SpotV7GovernedDaPrerequisiteBindingErrorV2) as captured:
        _bind_governed_spot_v7_da_prerequisite_v2(
            operational_policy=policy,
            exact_full_blob=full_blob,
            governed_sampled_response=governed_sample,
        )
    assert captured.value.code == "FULL_BLOB_POLICY_MATERIAL_MISMATCH"


@pytest.mark.parametrize(
    ("field", "replacement", "message"),
    (
        ("operational_policy", True, "exact Spot V7 operational policy V3"),
        ("governed_beacon", {"verified": True}, "exact lagged checkpoint beacon"),
        ("sampled_response", b'{"verified":true}', "authenticated sampled response"),
    ),
)
def test_raw_values_cannot_mint_governed_sample(
    field: str,
    replacement: object,
    message: str,
) -> None:
    policy, beacon, sampled, _, _ = _valid()
    inputs: dict[str, object] = {
        "operational_policy": policy,
        "governed_beacon": beacon,
        "sampled_response": sampled,
    }
    inputs[field] = replacement
    with pytest.raises(TypeError, match=message):
        _bind_governed_spot_v7_sampled_response_v1(**inputs)


def test_v2_capabilities_are_nontransferable_and_recheck_evidence() -> None:
    policy, _, sampled, governed_sample, full_blob = _valid()
    combined = _bind_governed_spot_v7_da_prerequisite_v2(
        operational_policy=policy,
        exact_full_blob=full_blob,
        governed_sampled_response=governed_sample,
    )

    for capability in (governed_sample, combined):
        with pytest.raises(TypeError):
            copy.copy(capability)
        with pytest.raises(TypeError):
            copy.deepcopy(capability)
        with pytest.raises(TypeError):
            pickle.dumps(capability)

    object.__setattr__(sampled, "_exact_evidence_bytes", b"forged")
    with pytest.raises(ValueError, match="evidence digest drift"):
        combined._projection_for_downstream_binding_v2()
