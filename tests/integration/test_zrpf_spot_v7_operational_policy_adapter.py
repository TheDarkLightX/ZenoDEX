"""Tests for the release-bound Spot V7 operational-policy loader."""

from __future__ import annotations

import copy
import json
import pickle

import pytest

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration.zrpf_spot_v7_operational_policy_adapter import (
    SPOT_V7_OPERATIONAL_POLICY_MANIFEST_SCHEMA_V1,
    SpotV7OperationalPolicyBindingError,
    TrustedSpotV7OperationalPolicyBindingV1,
    load_spot_v7_operational_policy_v1,
    spot_v7_operational_policy_manifest_digest_v1,
)
from src.state.canonical import canonical_json_bytes


def _root(seed: int) -> str:
    return f"0x{seed:064x}"


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
        "authority_manifest_sha256": f"{10:064x}",
        "release_binding_config_digest": _root(11),
    }


def _load(
    manifest: dict[str, object] | None = None,
    **overrides: object,
) -> TrustedSpotV7OperationalPolicyBindingV1:
    value = _manifest() if manifest is None else manifest
    raw = canonical_json_bytes(value)
    arguments: dict[str, object] = {
        "expected_manifest_digest": spot_v7_operational_policy_manifest_digest_v1(raw),
        "expected_application_id": value["application_id"],
        "expected_chain_or_domain_id": value["chain_or_domain_id"],
        "expected_authority_manifest_sha256": value["authority_manifest_sha256"],
        "expected_release_binding_config_digest": value["release_binding_config_digest"],
        "current_epoch": 50,
    }
    arguments.update(overrides)
    return load_spot_v7_operational_policy_v1(raw, **arguments)  # type: ignore[arg-type]


def test_canonical_release_bound_manifest_mints_exact_private_policy() -> None:
    manifest = _manifest()
    raw = canonical_json_bytes(manifest)
    binding = _load(manifest)

    assert binding.manifest_digest == spot_v7_operational_policy_manifest_digest_v1(raw)
    assert binding.authority_manifest_sha256 == manifest["authority_manifest_sha256"]
    assert binding.release_binding_config_digest == manifest["release_binding_config_digest"]
    assert binding.valid_from_epoch == 41
    assert binding.valid_through_epoch == 400

    capability = binding._capability_for_operational_gate()
    assert type(capability) is _GovernedSpotV7OperationalPolicyV2
    assert capability._has_private_seal() is True
    store_policy = capability._policy_for_atomic_store()
    assert store_policy.application_id == manifest["application_id"]
    assert store_policy.chain_or_domain_id == manifest["chain_or_domain_id"]
    assert store_policy.data_schema_id == manifest["data_schema_id"]
    assert store_policy.storage_policy_hash == manifest["storage_policy_hash"]
    assert store_policy.minimum_retention_epochs == 100
    assert store_policy.minimum_remaining_epochs == 25
    assert store_policy.maximum_blob_bytes == 8 * 1024 * 1024


def test_trusted_policy_has_no_public_constructor_or_serialization_path() -> None:
    with pytest.raises(TypeError):
        TrustedSpotV7OperationalPolicyBindingV1()
    with pytest.raises(TypeError):
        pickle.dumps(_load())
    with pytest.raises((AttributeError, TypeError)):
        _load().valid_through_epoch = 401  # type: ignore[misc]


def test_duplicate_key_rejects_before_policy_construction() -> None:
    manifest = _manifest()
    canonical = canonical_json_bytes(manifest).decode("ascii")
    raw = canonical.replace(
        '"application_id":',
        f'"application_id":"{_root(99)}","application_id":',
        1,
    ).encode("ascii")
    with pytest.raises(SpotV7OperationalPolicyBindingError) as captured:
        spot_v7_operational_policy_manifest_digest_v1(raw)
    assert captured.value.code == "DUPLICATE_JSON_KEY"


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        (lambda value: value.update({"verified": True}), "FIELD_SET_MISMATCH"),
        (lambda value: value.update({"maximum_blob_bytes": 1.5}), "FLOAT_FORBIDDEN"),
        (lambda value: value.update({"application_id": _root(0)}), "APPLICATION_ID_INVALID"),
        (lambda value: value.update({"maximum_blob_bytes": 0}), "MAXIMUM_BLOB_BYTES_INVALID"),
        (
            lambda value: value.update({"maximum_blob_bytes": 8 * 1024 * 1024 + 1}),
            "MAXIMUM_BLOB_BYTES_INVALID",
        ),
        (
            lambda value: value.update({"valid_from_epoch": 401, "valid_through_epoch": 400}),
            "VALIDITY_RANGE_INVALID",
        ),
        (
            lambda value: value.update({"authority_manifest_sha256": "0x" + "11" * 32}),
            "AUTHORITY_MANIFEST_SHA256_INVALID",
        ),
    ),
)
def test_malformed_policy_material_rejects(
    mutation: object,
    code: str,
) -> None:
    manifest = _manifest()
    mutation(manifest)  # type: ignore[operator]
    with pytest.raises(SpotV7OperationalPolicyBindingError) as captured:
        spot_v7_operational_policy_manifest_digest_v1(canonical_json_bytes(manifest))
    assert captured.value.code == code


def test_noncanonical_json_rejects() -> None:
    raw = json.dumps(_manifest(), indent=2, sort_keys=True).encode("ascii")
    with pytest.raises(SpotV7OperationalPolicyBindingError) as captured:
        spot_v7_operational_policy_manifest_digest_v1(raw)
    assert captured.value.code == "NONCANONICAL_JSON"


@pytest.mark.parametrize(
    ("overrides", "code"),
    (
        ({"expected_manifest_digest": _root(100)}, "MANIFEST_DIGEST_MISMATCH"),
        ({"expected_application_id": _root(101)}, "APPLICATION_ID_MISMATCH"),
        ({"expected_chain_or_domain_id": _root(102)}, "DOMAIN_ID_MISMATCH"),
        (
            {"expected_authority_manifest_sha256": f"{103:064x}"},
            "AUTHORITY_MANIFEST_MISMATCH",
        ),
        ({"expected_release_binding_config_digest": _root(104)}, "RELEASE_BINDING_MISMATCH"),
        ({"current_epoch": 40}, "POLICY_NOT_CURRENT"),
        ({"current_epoch": 401}, "POLICY_NOT_CURRENT"),
    ),
)
def test_external_anchor_or_validity_substitution_rejects(
    overrides: dict[str, object],
    code: str,
) -> None:
    with pytest.raises(SpotV7OperationalPolicyBindingError) as captured:
        _load(**overrides)
    assert captured.value.code == code


def test_every_policy_field_changes_the_manifest_digest() -> None:
    baseline = _manifest()
    baseline_digest = spot_v7_operational_policy_manifest_digest_v1(
        canonical_json_bytes(baseline)
    )
    for index, field in enumerate(sorted(baseline), start=1000):
        if field == "schema":
            continue
        mutated = copy.deepcopy(baseline)
        original = mutated[field]
        if field == "maximum_blob_bytes":
            mutated[field] = int(original) - 1
        elif type(original) is int:
            mutated[field] = int(original) + 1
        elif field == "authority_manifest_sha256":
            mutated[field] = f"{index:064x}"
        else:
            mutated[field] = _root(index)
        assert (
            spot_v7_operational_policy_manifest_digest_v1(canonical_json_bytes(mutated))
            != baseline_digest
        ), field
