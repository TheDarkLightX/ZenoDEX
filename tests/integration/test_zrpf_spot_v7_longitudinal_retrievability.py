"""CBC tests for bounded finite-window Spot V7 retrievability evidence."""

from __future__ import annotations

import copy
import hashlib
import pickle
from functools import lru_cache
from typing import Any, cast

import pytest

import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_full_blob_artifacts_v1,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
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
    _bind_governed_spot_v7_da_prerequisite_v2,
    _bind_governed_spot_v7_sampled_response_v1,
)
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    bind_governed_spot_v7_lagged_checkpoint_beacon_v1,
)
from src.integration.zrpf_spot_v7_longitudinal_retrievability import (
    MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1,
    SpotV7LongitudinalRetrievabilityBindingErrorV1,
    _bind_bounded_spot_v7_longitudinal_retrievability_v1,
    _GovernedSpotV7LongitudinalRetrievabilityV1,
)
from tests.integration.test_zrpf_spot_v7_governed_da_prerequisite_v2 import (
    EPOCH_ID,
    EXACT_BLOB,
    PROVIDER_PRIVATE_KEYS,
    RETENTION_THROUGH_EPOCH,
    _legacy_policy,
    _policy_v3,
)
from tests.integration.test_zrpf_spot_v7_lagged_checkpoint_beacon import (
    _finality,
)

FIRST_CHECKED_EPOCH = 20
_DEFAULT_POLICY = _policy_v3()


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _full_blob(
    policy: _GovernedSpotV7OperationalPolicyV3,
    checked_epoch: int,
    exact_blob: bytes = EXACT_BLOB,
) -> _GovernedExactFullBlobPolicySatisfactionV2:
    legacy = _legacy_policy(policy)
    base = legacy._policy_for_atomic_store()
    artifacts = _build_test_only_full_blob_artifacts_v1(
        policy=base,
        epoch_id=EPOCH_ID,
        checked_epoch=checked_epoch,
        retention_through_epoch=RETENTION_THROUGH_EPOCH,
        exact_blob_bytes=exact_blob,
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


def _combined(
    checked_epoch: int,
    *,
    policy: _GovernedSpotV7OperationalPolicyV3 | None = None,
    exact_blob: bytes = EXACT_BLOB,
    checkpoint_hash: str | None = None,
):
    governed_policy = policy or _DEFAULT_POLICY
    source_policy_root = (
        governed_policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    )
    source = _finality(
        source_policy_root,
        sequence=checked_epoch - 1,
        checkpoint_hash=(checkpoint_hash or _root(f"checkpoint-{checked_epoch - 1}")),
        evidence=f"finality-evidence-{checked_epoch}".encode("ascii"),
    )
    beacon = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=governed_policy,
        source_finality=source,
        checked_epoch=checked_epoch,
    )
    sampled_policy = governed_policy._sampled_policy_for_governed_da_v2()
    base = governed_policy._material.base_material
    target = derive_exact_full_blob_target_v1(
        application_id=base.application_id,
        chain_or_domain_id=base.chain_or_domain_id,
        epoch_id=EPOCH_ID,
        data_schema_id=base.data_schema_id,
        exact_blob_bytes=exact_blob,
        retention_through_epoch=RETENTION_THROUGH_EPOCH,
        storage_policy_hash=base.storage_policy_hash,
    )
    beacon_value = beacon._beacon_for_sampled_retrievability_v1()
    responses: list[SignedProviderResponseV1] = []
    for index, provider in enumerate(sampled_policy.providers):
        response_bytes = build_provider_response_bytes_v1(
            policy=sampled_policy,
            target=target,
            beacon=beacon_value,
            checked_epoch=checked_epoch,
            response_epoch=checked_epoch + 1,
            provider_id=provider.provider_id,
            key_id=provider.key_id,
            exact_blob_bytes=exact_blob,
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
        policy=sampled_policy,
        target=target,
        beacon=beacon_value,
        checked_epoch=checked_epoch,
        exact_blob_bytes=exact_blob,
        signed_responses=tuple(responses),
    )
    sampled = verify_exact_evidence_v1(
        evidence,
        expected_policy=sampled_policy,
        expected_target=target,
        expected_beacon=beacon_value,
        checked_epoch=checked_epoch,
    )
    governed_sample = _bind_governed_spot_v7_sampled_response_v1(
        operational_policy=governed_policy,
        governed_beacon=beacon,
        sampled_response=sampled,
    )
    return _bind_governed_spot_v7_da_prerequisite_v2(
        operational_policy=governed_policy,
        exact_full_blob=_full_blob(governed_policy, checked_epoch, exact_blob),
        governed_sampled_response=governed_sample,
    )


@lru_cache(maxsize=MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1 + 2)
def _cached_combined(checked_epoch: int):
    return _combined(checked_epoch, policy=_DEFAULT_POLICY)


def _window(
    *epochs: int,
    policy: _GovernedSpotV7OperationalPolicyV3 | None = None,
):
    governed_policy = policy or _DEFAULT_POLICY
    samples = (
        tuple(_cached_combined(epoch) for epoch in epochs)
        if governed_policy is _DEFAULT_POLICY
        else tuple(_combined(epoch, policy=governed_policy) for epoch in epochs)
    )
    return _bind_bounded_spot_v7_longitudinal_retrievability_v1(
        samples
    )


def test_consecutive_governed_samples_mint_only_bounded_finite_window_claim() -> None:
    result = _window(20, 21, 22)

    assert type(result) is _GovernedSpotV7LongitudinalRetrievabilityV1
    projection = result._projection_for_longitudinal_downstream_binding_v1()
    assert projection.start_checked_epoch == 20
    assert projection.end_checked_epoch == 22
    assert projection.sample_count == 3
    assert tuple(item.checked_epoch for item in projection.observations) == (20, 21, 22)
    assert tuple(item.source_checkpoint_sequence for item in projection.observations) == (
        19,
        20,
        21,
    )
    assert len(set(item.source_checkpoint_hash for item in projection.observations)) == 3
    assert len(set(item.beacon_commitment for item in projection.observations)) == 3
    repeated = _bind_bounded_spot_v7_longitudinal_retrievability_v1(result._samples)
    assert repeated._projection.window_root == projection.window_root
    assert _window(20, 21)._projection.window_root != projection.window_root
    assert result.bounded_finite_window_retrievability_verified is True
    assert result.sampled_policy_governance_provenance_verified is True
    assert result.governed_beacon_provenance_verified is True
    assert result.current_operational_policy_release_head_verified is False
    assert result.beacon_unpredictability_verified is False
    assert result.response_timing_provenance_verified is False
    assert result.provider_independence_verified is False
    assert result.continuous_availability_verified is False
    assert result.public_future_availability_verified is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


@pytest.mark.parametrize(
    ("epochs", "code"),
    (
        ((20,), "SAMPLE_COUNT_OUT_OF_BOUNDS"),
        ((20, 20), "CHECKED_EPOCH_NOT_CONSECUTIVE"),
        ((21, 20), "CHECKED_EPOCH_NOT_CONSECUTIVE"),
        ((20, 22), "CHECKED_EPOCH_NOT_CONSECUTIVE"),
    ),
)
def test_non_window_epoch_sequences_reject(epochs: tuple[int, ...], code: str) -> None:
    with pytest.raises(SpotV7LongitudinalRetrievabilityBindingErrorV1) as captured:
        _window(*epochs)
    assert captured.value.code == code


def test_window_over_sample_limit_rejects_before_derivation() -> None:
    sample = _combined(FIRST_CHECKED_EPOCH)
    values = tuple(sample for _ in range(MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1 + 1))

    with pytest.raises(SpotV7LongitudinalRetrievabilityBindingErrorV1) as captured:
        _bind_bounded_spot_v7_longitudinal_retrievability_v1(values)
    assert captured.value.code == "SAMPLE_COUNT_OUT_OF_BOUNDS"


def test_changed_content_rejects() -> None:
    policy = _DEFAULT_POLICY
    samples = (
        _cached_combined(20),
        _combined(21, policy=policy, exact_blob=EXACT_BLOB[:-1] + b"x"),
    )

    with pytest.raises(SpotV7LongitudinalRetrievabilityBindingErrorV1) as captured:
        _bind_bounded_spot_v7_longitudinal_retrievability_v1(samples)
    assert captured.value.code == "CONTENT_IDENTITY_MISMATCH"


def test_distinct_policy_capabilities_reject_even_when_material_matches() -> None:
    other_policy = _policy_v3()
    samples = (_cached_combined(20), _combined(21, policy=other_policy))

    with pytest.raises(SpotV7LongitudinalRetrievabilityBindingErrorV1) as captured:
        _bind_bounded_spot_v7_longitudinal_retrievability_v1(samples)
    assert captured.value.code == "POLICY_CAPABILITY_MISMATCH"


def test_reused_source_checkpoint_hash_rejects() -> None:
    first = _cached_combined(20)
    reused_hash = first._projection.source_checkpoint_hash
    second = _combined(
        21,
        policy=_DEFAULT_POLICY,
        checkpoint_hash=reused_hash,
    )

    with pytest.raises(SpotV7LongitudinalRetrievabilityBindingErrorV1) as captured:
        _bind_bounded_spot_v7_longitudinal_retrievability_v1((first, second))
    assert captured.value.code == "SOURCE_CHECKPOINT_REUSED"


@pytest.mark.parametrize(
    "raw",
    ([], [True, True], (True, True), {"verified": True}, b"verified"),
)
def test_raw_or_forged_values_cannot_mint_window(raw: object) -> None:
    with pytest.raises(TypeError):
        _bind_bounded_spot_v7_longitudinal_retrievability_v1(raw)


def test_window_is_nontransferable_and_rechecks_exact_samples() -> None:
    result = _window(20, 21)

    with pytest.raises(TypeError):
        copy.copy(result)
    with pytest.raises(TypeError):
        copy.deepcopy(result)
    with pytest.raises(TypeError):
        pickle.dumps(result)
    with pytest.raises(TypeError):
        result._seal = cast(Any, object())

    object.__setattr__(result._projection, "data_root", _root("forged-data"))
    with pytest.raises(ValueError, match="projection drift"):
        result._projection_for_longitudinal_downstream_binding_v1()
