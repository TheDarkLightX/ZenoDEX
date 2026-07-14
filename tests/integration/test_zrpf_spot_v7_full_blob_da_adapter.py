"""Integration tests for the pinned Spot V7 full-blob DA adapter."""

from __future__ import annotations

import hashlib
import os
import pickle
from pathlib import Path

import pytest

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedExactFullBlobPolicySatisfactionV2,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _build_test_only_full_blob_artifacts_v1,
)
from src.integration.zrpf_spot_v7_full_blob_da_adapter import (
    FullBlobDaAdapterError,
    PinnedFullBlobDaPolicyVerifierV1,
    TrustedFullBlobDaPolicySatisfactionV1,
    _parse_success_response_v1,
)
from src.integration.zrpf_spot_v7_operational_policy_adapter import (
    SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1,
    load_spot_v7_operational_policy_v1,
    spot_v7_operational_policy_manifest_digest_v1,
)
from src.state.canonical import canonical_json_bytes


def _root(seed: int) -> str:
    return f"0x{seed:064x}"


def _authority_manifest() -> str:
    return f"{91:064x}"


def _manifest() -> dict[str, object]:
    return {
        "schema": SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1,
        "application_id": _root(1),
        "chain_or_domain_id": _root(2),
        "data_schema_id": _root(3),
        "storage_policy_hash": _root(4),
        "minimum_retention_epochs": 100,
        "minimum_remaining_epochs": 25,
        "maximum_blob_bytes": 8 * 1024 * 1024,
        "finality_network_id": _root(5),
        "finality_protocol_id": _root(6),
        "external_finality_policy_hash": _root(7),
        "finality_verifier_set_root": _root(8),
        "genesis_application_checkpoint_sequence": 40,
        "genesis_application_checkpoint_hash": _root(9),
        "valid_from_epoch": 41,
        "valid_through_epoch": 400,
        "authority_manifest_sha256": _authority_manifest(),
        "release_binding_config_digest": _root(11),
    }


def _policy():
    manifest = _manifest()
    raw = canonical_json_bytes(manifest)
    return load_spot_v7_operational_policy_v1(
        raw,
        expected_manifest_digest=spot_v7_operational_policy_manifest_digest_v1(raw),
        expected_application_id=str(manifest["application_id"]),
        expected_chain_or_domain_id=str(manifest["chain_or_domain_id"]),
        expected_authority_manifest_sha256=str(manifest["authority_manifest_sha256"]),
        expected_release_binding_config_digest=str(
            manifest["release_binding_config_digest"]
        ),
        current_epoch=50,
    )


def _verifier_path() -> Path:
    raw = os.environ.get("ZRPF_FULL_BLOB_DA_VERIFIER")
    if raw is None:
        pytest.skip("ZRPF_FULL_BLOB_DA_VERIFIER is not configured")
    path = Path(raw)
    if not path.is_absolute() or not path.is_file():
        raise AssertionError("configured DA verifier path is not an absolute file")
    return path


def _verifier(*, expected_sha256: str | None = None, authority: str | None = None):
    path = _verifier_path()
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return PinnedFullBlobDaPolicyVerifierV1(
        executable=path,
        expected_sha256=digest if expected_sha256 is None else expected_sha256,
        expected_authority_manifest_sha256=(
            _authority_manifest() if authority is None else authority
        ),
        timeout_seconds=15,
        max_address_space_bytes=1024 * 1024 * 1024,
        max_stack_bytes=16 * 1024 * 1024,
    )


def _artifacts():
    policy = _policy()
    store_policy = policy._capability_for_operational_gate()._policy_for_atomic_store()
    blob = b"exact source-opened Spot V7 replay bytes"
    artifacts = _build_test_only_full_blob_artifacts_v1(
        policy=store_policy,
        epoch_id=50,
        checked_epoch=75,
        retention_through_epoch=200,
        exact_blob_bytes=blob,
    )
    return policy, artifacts


def test_actual_static_rust_verifier_mints_exact_sealed_capability() -> None:
    policy, artifacts = _artifacts()
    result = _verifier().verify_and_seal(
        policy=policy,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_blob_bytes=artifacts.exact_blob_bytes,
        expected_certificate_epoch=artifacts.epoch_id,
        checked_epoch=artifacts.checked_epoch,
    )

    assert result.policy_manifest_digest == policy.manifest_digest
    assert result.policy_root == artifacts.policy_root
    assert result.certificate_root == artifacts.certificate_root
    assert result.data_root == artifacts.data_root
    assert result.exact_blob_sha256 == artifacts.blob_sha256
    assert result.epoch_id == artifacts.epoch_id
    assert result.checked_epoch == artifacts.checked_epoch
    assert result.retention_through_epoch == artifacts.retention_through_epoch
    assert result.retrievability_verified is False
    assert result.settlement_authority is False
    assert result.production_authority is False

    capability = result._capability_for_operational_gate()
    assert type(capability) is _GovernedExactFullBlobPolicySatisfactionV2
    assert capability._has_private_seal() is True


def test_result_is_nonconstructible_nonmutable_and_nonserializable() -> None:
    with pytest.raises(TypeError):
        TrustedFullBlobDaPolicySatisfactionV1()
    policy, artifacts = _artifacts()
    result = _verifier().verify_and_seal(
        policy=policy,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_blob_bytes=artifacts.exact_blob_bytes,
        expected_certificate_epoch=50,
        checked_epoch=75,
    )
    with pytest.raises(TypeError):
        pickle.dumps(result)
    with pytest.raises((AttributeError, TypeError)):
        result.checked_epoch = 76  # type: ignore[misc]


@pytest.mark.parametrize("target", ["blob", "certificate"])
def test_exact_artifact_mutation_rejects(target: str) -> None:
    policy, artifacts = _artifacts()
    blob = bytearray(artifacts.exact_blob_bytes)
    certificate = bytearray(artifacts.exact_certificate_bytes)
    if target == "blob":
        blob[0] ^= 1
    else:
        certificate[-1] ^= 1
    with pytest.raises(FullBlobDaAdapterError) as captured:
        _verifier().verify_and_seal(
            policy=policy,
            exact_certificate_bytes=bytes(certificate),
            exact_blob_bytes=bytes(blob),
            expected_certificate_epoch=50,
            checked_epoch=75,
        )
    assert captured.value.code == "PINNED_VERIFIER_REJECTED"


def test_wrong_verifier_or_authority_identity_rejects() -> None:
    policy, artifacts = _artifacts()
    with pytest.raises(FullBlobDaAdapterError) as captured:
        _verifier(expected_sha256=f"{99:064x}").verify_and_seal(
            policy=policy,
            exact_certificate_bytes=artifacts.exact_certificate_bytes,
            exact_blob_bytes=artifacts.exact_blob_bytes,
            expected_certificate_epoch=50,
            checked_epoch=75,
        )
    assert captured.value.code == "PINNED_VERIFIER_REJECTED"

    with pytest.raises(FullBlobDaAdapterError) as captured:
        _verifier(authority=f"{100:064x}").verify_and_seal(
            policy=policy,
            exact_certificate_bytes=artifacts.exact_certificate_bytes,
            exact_blob_bytes=artifacts.exact_blob_bytes,
            expected_certificate_epoch=50,
            checked_epoch=75,
        )
    assert captured.value.code == "AUTHORITY_MANIFEST_MISMATCH"


def test_epoch_and_retention_policy_rejections_remain_fail_closed() -> None:
    policy, artifacts = _artifacts()
    for expected_epoch, checked_epoch in ((49, 75), (50, 49), (50, 176)):
        with pytest.raises(FullBlobDaAdapterError) as captured:
            _verifier().verify_and_seal(
                policy=policy,
                exact_certificate_bytes=artifacts.exact_certificate_bytes,
                exact_blob_bytes=artifacts.exact_blob_bytes,
                expected_certificate_epoch=expected_epoch,
                checked_epoch=checked_epoch,
            )
        assert captured.value.code == "PINNED_VERIFIER_REJECTED"


def test_success_parser_rejects_malformed_or_zero_bound_outputs() -> None:
    with pytest.raises(FullBlobDaAdapterError) as captured:
        _parse_success_response_v1(b"")
    assert captured.value.code == "VERIFIER_RESPONSE_LENGTH"

    malformed = bytearray(160)
    malformed[:8] = b"ZDAOK1\x00\x00"
    with pytest.raises(FullBlobDaAdapterError) as captured:
        _parse_success_response_v1(bytes(malformed))
    assert captured.value.code == "VERIFIER_RESPONSE_HASH"


def test_production_source_has_one_pinned_execution_call_site() -> None:
    source = (
        Path(__file__).parents[2]
        / "src/integration/zrpf_spot_v7_full_blob_da_adapter.py"
    ).read_text(encoding="utf-8")
    assert source.count("execute_pinned_verifier_once(") == 1
    assert "verified=True" not in source
    assert '"verified"' not in source
