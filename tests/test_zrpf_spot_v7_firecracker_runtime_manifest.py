"""CBC tests for the proposal-only Spot V7 Firecracker runtime manifest."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Callable
from typing import Any

import pytest

from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_manifest
from tools import zrpf_spot_v7_firecracker_runtime_protocol as runtime_protocol
from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
)


def test_exact_manifest_binds_roles_config_profiles_and_nonclaims() -> None:
    config = _machine_config_bytes()
    raw = _manifest_bytes(config)

    decoded = runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
        raw,
        exact_machine_config_bytes=config,
    )

    assert decoded.canonical_bytes == raw
    assert len(raw) == 2_092
    assert hashlib.sha256(raw).hexdigest() == (
        "2c329ba1527e2159e55ea91c222de428497a7cb59d7e089e628bd5b873d3bf9b"
    )
    assert decoded.artifact_set_id.hex() == (
        "228344447908425e265a44d48d9b5eb0f45bdff26d8791b7d97b8512c662a7a0"
    )
    assert decoded.machine_config_sha256 == hashlib.sha256(config).digest()
    assert decoded.runtime_profile_sha256 == (
        runtime_protocol.SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    )
    assert decoded.authority_input_profile_sha256 == (
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1
    )
    assert decoded.guest_entrypoint == runtime_manifest.SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1
    assert tuple(row.role for row in decoded.artifacts) == (
        runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
    )
    assert decoded.runtime_manifest_schema_verified is True
    assert decoded.machine_config_binding_verified is True
    assert decoded.artifact_role_contract_verified is True
    assert decoded.artifact_bytes_verified is False
    assert decoded.governance_admission_verified is False
    assert decoded.governed_machine_config_verified is False
    assert decoded.governed_runtime_manifest_verified is False
    assert decoded.live_firecracker_execution_verified is False
    assert decoded.release_authority is False
    assert decoded.settlement_authority is False
    assert decoded.production_authority is False


def test_arbitrary_canonical_json_no_longer_counts_as_a_runtime_manifest() -> None:
    raw = _canonical({"schema": "zenodex/test_spot_v7_runtime_manifest/v1"})

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            raw,
            exact_machine_config_bytes=_machine_config_bytes(),
        )

    assert captured.value.code == "runtime_manifest_fields"


def test_runtime_artifact_role_names_are_runtime_immutable() -> None:
    artifact_names = runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1
    with pytest.raises(TypeError):
        artifact_names["kernel"] = "changed"  # type: ignore[index]


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    (
        (lambda value: value.update(schema="zenodex/wrong"), "runtime_manifest_version"),
        (lambda value: value.update(status="accepted"), "runtime_manifest_version"),
        (lambda value: value.update(architecture="aarch64"), "runtime_manifest_architecture"),
        (
            lambda value: value.update(runtime_profile_sha256="11" * 32),
            "runtime_manifest_runtime_profile",
        ),
        (
            lambda value: value.update(authority_input_profile_sha256="22" * 32),
            "runtime_manifest_authority_input_profile",
        ),
        (
            lambda value: value.update(guest_entrypoint="/sbin/other-init"),
            "runtime_manifest_guest_entrypoint",
        ),
        (
            lambda value: value.update(machine_config_sha256="33" * 32),
            "runtime_manifest_machine_config",
        ),
        (
            lambda value: value.update(v7_image_id=[0] * 8),
            "runtime_manifest_image_id",
        ),
        (
            lambda value: value.update(v6_image_id=[True] * 8),
            "runtime_manifest_image_id",
        ),
        (
            lambda value: value["authority"].update(production_authority=True),
            "runtime_manifest_authority",
        ),
        (
            lambda value: value["authority"].update(production_authority=0),
            "runtime_manifest_authority",
        ),
        (
            lambda value: value.update(non_claims=[]),
            "runtime_manifest_non_claims",
        ),
        (
            lambda value: value.update(artifact_set_id="44" * 32),
            "runtime_manifest_artifact_set",
        ),
    ),
)
def test_manifest_scalar_or_authority_substitution_fails_closed(
    mutation: Callable[[dict[str, Any]], None],
    expected_code: str,
) -> None:
    config = _machine_config_bytes()
    document = json.loads(_manifest_bytes(config))
    mutation(document)

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            _canonical(document),
            exact_machine_config_bytes=config,
        )

    assert captured.value.code == expected_code


@pytest.mark.parametrize(
    ("mutate", "expected_code"),
    (
        (
            lambda artifacts: artifacts.reverse(),
            "runtime_manifest_artifact_order",
        ),
        (
            lambda artifacts: artifacts[0].update(role="rootfs"),
            "runtime_manifest_artifact_order",
        ),
        (
            lambda artifacts: artifacts[0].update(artifact_name="wrong"),
            "runtime_manifest_artifact_name",
        ),
        (
            lambda artifacts: artifacts[0].update(sha256="00" * 32),
            "runtime_manifest_artifact_digest",
        ),
        (
            lambda artifacts: artifacts[0].update(sha256=artifacts[1]["sha256"]),
            "runtime_manifest_artifact_digest",
        ),
        (
            lambda artifacts: artifacts[0].update(size_bytes=True),
            "runtime_manifest_artifact_size",
        ),
        (
            lambda artifacts: artifacts[0].update(extra="field"),
            "runtime_manifest_artifact_fields",
        ),
    ),
)
def test_artifact_role_or_identity_substitution_fails_closed(
    mutate: Callable[[list[dict[str, Any]]], None],
    expected_code: str,
) -> None:
    config = _machine_config_bytes()
    document = json.loads(_manifest_bytes(config))
    artifacts = document["artifacts"]
    assert isinstance(artifacts, list)
    mutate(artifacts)

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            _canonical(document),
            exact_machine_config_bytes=config,
        )

    assert captured.value.code == expected_code


def test_machine_config_entrypoint_and_manifest_must_match_exactly() -> None:
    config = _machine_config_bytes()
    raw = _manifest_bytes(config)
    changed = _machine_config()
    boot = changed["boot-source"]
    assert isinstance(boot, dict)
    boot["boot_args"] = "init=/sbin/spot-v7-firecracker-protocol-init"

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            raw,
            exact_machine_config_bytes=_canonical(changed),
        )

    assert captured.value.code == "runtime_manifest_machine_config"


@pytest.mark.parametrize(
    "mutation",
    (
        lambda config: config["machine-config"].update(vcpu_count=True),
        lambda config: config["machine-config"].update(smt=0),
        lambda config: config["drives"][0].update(is_read_only=1),
    ),
)
def test_machine_config_rejects_bool_integer_type_aliases(
    mutation: Callable[[dict[str, Any]], None],
) -> None:
    exact_config = _machine_config_bytes()
    changed = _machine_config()
    mutation(changed)

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            _manifest_bytes(exact_config),
            exact_machine_config_bytes=_canonical(changed),
        )

    assert captured.value.code == "runtime_manifest_machine_config"


def test_v6_and_v7_image_ids_must_be_distinct() -> None:
    image_id = _image_id(0x10)

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.build_candidate_spot_v7_runtime_manifest_v1(
            exact_machine_config_bytes=_machine_config_bytes(),
            artifacts=_artifacts(),
            v7_image_id=image_id,
            v6_image_id=image_id,
        )

    assert captured.value.code == "runtime_manifest_image_id"


def test_coherently_changed_identities_remain_only_an_authority_false_proposal() -> None:
    artifacts = list(_artifacts())
    first = artifacts[0]
    artifacts[0] = runtime_manifest.SpotV7RuntimeArtifactIdentityV1.validated(
        role=first.role,
        artifact_name=first.artifact_name,
        sha256=bytes([0x41]) * 32,
        size_bytes=first.size_bytes,
    )
    config = _machine_config_bytes()
    raw = runtime_manifest.build_candidate_spot_v7_runtime_manifest_v1(
        exact_machine_config_bytes=config,
        artifacts=tuple(artifacts),
        v7_image_id=_image_id(0x20),
        v6_image_id=_image_id(0x90),
    )

    proposal = runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
        raw,
        exact_machine_config_bytes=config,
    )

    assert proposal.artifact_bytes_verified is False
    assert proposal.governance_admission_verified is False
    assert proposal.governed_machine_config_verified is False
    assert proposal.governed_runtime_manifest_verified is False
    assert proposal.live_firecracker_execution_verified is False
    assert proposal.release_authority is False
    assert proposal.settlement_authority is False
    assert proposal.production_authority is False


def test_validated_manifest_constructor_requires_module_private_seal() -> None:
    with pytest.raises(TypeError, match="module-private seal"):
        runtime_manifest.CandidateSpotV7FirecrackerRuntimeManifestV1._from_validated(
            canonical_bytes=b"forged",
            artifact_set_id=b"a" * 32,
            artifacts=(),
            machine_config_sha256=b"m" * 32,
            v7_image_id=(),
            v6_image_id=(),
            seal=object(),  # type: ignore[arg-type]
        )


@pytest.mark.parametrize(
    "raw",
    (
        b'{"schema":"a","schema":"b"}\n',
        b'{"ratio":1.5}\n',
        b'{"schema":"missing-canonical-newline"}',
    ),
)
def test_manifest_codec_rejects_duplicate_float_and_noncanonical_json(raw: bytes) -> None:
    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            raw,
            exact_machine_config_bytes=_machine_config_bytes(),
        )

    assert captured.value.code == "runtime_manifest_json"


def test_unknown_root_field_fails_closed() -> None:
    config = _machine_config_bytes()
    document = json.loads(_manifest_bytes(config))
    document["unknown"] = False

    with pytest.raises(runtime_manifest.SpotV7RuntimeManifestRejectV1) as captured:
        runtime_manifest.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            _canonical(document),
            exact_machine_config_bytes=config,
        )

    assert captured.value.code == "runtime_manifest_fields"


def _manifest_bytes(config: bytes) -> bytes:
    return runtime_manifest.build_candidate_spot_v7_runtime_manifest_v1(
        exact_machine_config_bytes=config,
        artifacts=_artifacts(),
        v7_image_id=_image_id(0x10),
        v6_image_id=_image_id(0x80),
    )


def _artifacts() -> tuple[runtime_manifest.SpotV7RuntimeArtifactIdentityV1, ...]:
    output: list[runtime_manifest.SpotV7RuntimeArtifactIdentityV1] = []
    for index, role in enumerate(runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1, start=1):
        output.append(
            runtime_manifest.SpotV7RuntimeArtifactIdentityV1.validated(
                role=role,
                artifact_name=runtime_manifest.SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[role],
                sha256=bytes([index]) * 32,
                size_bytes=4_096 + index,
            )
        )
    return tuple(output)


def _image_id(seed: int) -> tuple[int, ...]:
    return tuple(seed + index for index in range(8))


def _machine_config_bytes() -> bytes:
    return _canonical(_machine_config())


def _machine_config() -> dict[str, object]:
    return {
        "boot-source": {
            "boot_args": f"init={runtime_manifest.SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1}",
            "kernel_image_path": "/resources/kernel",
        },
        "drives": [
            {
                "drive_id": "rootfs",
                "is_read_only": True,
                "is_root_device": True,
                "path_on_host": "/resources/rootfs",
            },
            {
                "drive_id": "input",
                "is_read_only": True,
                "is_root_device": False,
                "path_on_host": "/resources/input",
            },
            {
                "drive_id": "output",
                "is_read_only": False,
                "is_root_device": False,
                "path_on_host": "/resources/output",
            },
        ],
        "machine-config": {
            "mem_size_mib": 256,
            "smt": False,
            "track_dirty_pages": False,
            "vcpu_count": 1,
        },
    }


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")
