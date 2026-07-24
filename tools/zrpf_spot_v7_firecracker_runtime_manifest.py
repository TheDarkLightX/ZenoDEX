"""Strict proposal-only identity manifest for the Spot V7 Firecracker lane.

The manifest fixes the artifact roles, authority-designated PID-1 entrypoint,
machine configuration, proof-input profile, and compiled image identities used
by one proposed run. Parsing proves only exact canonical data relationships.
Governance, artifact-byte verification, execution, release, settlement, and
production authority remain false.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Final, NoReturn, cast

from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
)

SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1: Final = "zenodex/zrpf_spot_v7_firecracker_runtime_manifest/v1"
SPOT_V7_RUNTIME_MANIFEST_STATUS_V1: Final = "candidate_exact_runtime_identity_authority_false"
SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1: Final = "/sbin/spot-v7-firecracker-authority-init"
SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1: Final = (
    "firecracker",
    "guest_init",
    "input",
    "jailer",
    "kernel",
    "rootfs",
)
SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1: Final[Mapping[str, str]] = MappingProxyType(
    {
        "firecracker": "firecracker",
        "guest_init": "spot-v7-firecracker-authority-init",
        "input": "input",
        "jailer": "jailer",
        "kernel": "kernel",
        "rootfs": "rootfs",
    }
)

_MAX_MANIFEST_BYTES_V1: Final = 256 * 1_024
_MAX_MACHINE_CONFIG_BYTES_V1: Final = 64 * 1_024
_MAX_ARTIFACT_BYTES_BY_ROLE_V1: Final = {
    "firecracker": 256 * 1_024 * 1_024,
    "guest_init": 256 * 1_024 * 1_024,
    "input": 64 * 1_024 * 1_024,
    "jailer": 256 * 1_024 * 1_024,
    "kernel": 512 * 1_024 * 1_024,
    "rootfs": 4 * 1_024 * 1_024 * 1_024,
}
_ARTIFACT_SET_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.firecracker.runtime_artifact_set.v1"
_ROOT_FIELDS_V1: Final = {
    "architecture",
    "artifact_set_id",
    "artifacts",
    "authority",
    "authority_input_profile_sha256",
    "guest_entrypoint",
    "machine_config_sha256",
    "non_claims",
    "runtime_profile_sha256",
    "schema",
    "status",
    "v6_image_id",
    "v7_image_id",
}
_ARTIFACT_FIELDS_V1: Final = {"artifact_name", "role", "sha256", "size_bytes"}
_AUTHORITY_FIELDS_V1: Final = (
    "artifact_bytes_verified",
    "governance_admission_verified",
    "governed_machine_config_verified",
    "governed_runtime_manifest_verified",
    "live_firecracker_execution_verified",
    "production_authority",
    "release_authority",
    "settlement_authority",
)
_NON_CLAIMS_V1: Final = (
    "no governance or release selection claim",
    "no local artifact-byte or source-to-binary claim",
    "no live Firecracker, Jailer, cgroup, network, or sandbox claim",
    "no settlement, ledger-admission, production, privacy, or side-channel claim",
)


class SpotV7RuntimeManifestRejectV1(ValueError):
    """Stable fail-closed rejection at the runtime-manifest boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


class _RuntimeManifestConstructionSealV1:
    __slots__ = ()


_RUNTIME_MANIFEST_CONSTRUCTION_SEAL_V1 = _RuntimeManifestConstructionSealV1()


@dataclass(frozen=True, slots=True, init=False)
class SpotV7RuntimeArtifactIdentityV1:
    """One exact artifact identity in the fixed Spot V7 role inventory."""

    role: str
    artifact_name: str
    sha256: bytes
    size_bytes: int

    def __new__(cls) -> SpotV7RuntimeArtifactIdentityV1:
        raise TypeError("artifact identity requires validated construction")

    @classmethod
    def validated(
        cls,
        *,
        role: str,
        artifact_name: str,
        sha256: bytes,
        size_bytes: int,
    ) -> SpotV7RuntimeArtifactIdentityV1:
        _require_artifact_role(role)
        if artifact_name != SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[role]:
            raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_name")
        _require_digest_bytes(sha256, "runtime_manifest_artifact_digest")
        _require_artifact_size(role, size_bytes)
        value = object.__new__(cls)
        object.__setattr__(value, "role", role)
        object.__setattr__(value, "artifact_name", artifact_name)
        object.__setattr__(value, "sha256", sha256)
        object.__setattr__(value, "size_bytes", size_bytes)
        return value

    def to_document(self) -> dict[str, object]:
        return {
            "artifact_name": self.artifact_name,
            "role": self.role,
            "sha256": self.sha256.hex(),
            "size_bytes": self.size_bytes,
        }


@dataclass(frozen=True, slots=True, init=False)
class CandidateSpotV7FirecrackerRuntimeManifestV1:
    """Exact validated proposal carrying no governance or execution authority."""

    canonical_bytes: bytes
    artifact_set_id: bytes
    artifacts: tuple[SpotV7RuntimeArtifactIdentityV1, ...]
    machine_config_sha256: bytes
    runtime_profile_sha256: bytes
    authority_input_profile_sha256: bytes
    guest_entrypoint: str
    v7_image_id: tuple[int, ...]
    v6_image_id: tuple[int, ...]

    def __new__(cls) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
        raise TypeError("runtime manifest requires exact validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        canonical_bytes: bytes,
        artifact_set_id: bytes,
        artifacts: tuple[SpotV7RuntimeArtifactIdentityV1, ...],
        machine_config_sha256: bytes,
        v7_image_id: tuple[int, ...],
        v6_image_id: tuple[int, ...],
        seal: _RuntimeManifestConstructionSealV1,
    ) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
        if seal is not _RUNTIME_MANIFEST_CONSTRUCTION_SEAL_V1:
            raise TypeError("runtime manifest requires the module-private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "canonical_bytes", canonical_bytes)
        object.__setattr__(value, "artifact_set_id", artifact_set_id)
        object.__setattr__(value, "artifacts", artifacts)
        object.__setattr__(value, "machine_config_sha256", machine_config_sha256)
        object.__setattr__(
            value,
            "runtime_profile_sha256",
            SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
        )
        object.__setattr__(
            value,
            "authority_input_profile_sha256",
            SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
        )
        object.__setattr__(
            value,
            "guest_entrypoint",
            SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1,
        )
        object.__setattr__(value, "v7_image_id", v7_image_id)
        object.__setattr__(value, "v6_image_id", v6_image_id)
        return value

    @property
    def runtime_manifest_schema_verified(self) -> bool:
        return True

    @property
    def machine_config_binding_verified(self) -> bool:
        return True

    @property
    def artifact_role_contract_verified(self) -> bool:
        return True

    @property
    def artifact_bytes_verified(self) -> bool:
        return False

    @property
    def governance_admission_verified(self) -> bool:
        return False

    @property
    def governed_machine_config_verified(self) -> bool:
        return False

    @property
    def governed_runtime_manifest_verified(self) -> bool:
        return False

    @property
    def live_firecracker_execution_verified(self) -> bool:
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


def build_candidate_spot_v7_runtime_manifest_v1(
    *,
    exact_machine_config_bytes: bytes,
    artifacts: tuple[SpotV7RuntimeArtifactIdentityV1, ...],
    v7_image_id: tuple[int, ...],
    v6_image_id: tuple[int, ...],
) -> bytes:
    """Build and self-validate one exact authority-false proposal manifest."""

    _validate_machine_config(exact_machine_config_bytes)
    artifacts_value = _require_exact_artifact_inventory(artifacts)
    v7_value = _require_image_id(v7_image_id)
    v6_value = _require_image_id(v6_image_id)
    _require_distinct_image_ids(v7_value, v6_value)
    machine_config_sha256 = hashlib.sha256(exact_machine_config_bytes).digest()
    identity = _artifact_set_identity_document(
        artifacts=artifacts_value,
        machine_config_sha256=machine_config_sha256,
        v7_image_id=v7_value,
        v6_image_id=v6_value,
    )
    document = {
        **identity,
        "artifact_set_id": _artifact_set_id(identity).hex(),
        "authority": {name: False for name in _AUTHORITY_FIELDS_V1},
        "non_claims": list(_NON_CLAIMS_V1),
        "status": SPOT_V7_RUNTIME_MANIFEST_STATUS_V1,
    }
    raw = canonical_document_bytes_v1(document)
    return parse_exact_candidate_spot_v7_runtime_manifest_v1(
        raw,
        exact_machine_config_bytes=exact_machine_config_bytes,
    ).canonical_bytes


def parse_exact_candidate_spot_v7_runtime_manifest_v1(
    raw: bytes,
    *,
    exact_machine_config_bytes: bytes,
) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
    """Decode the exact schema and bind it to one canonical machine config."""

    document = _decode_exact_document(raw)
    _validate_manifest_header(document)
    machine_config_sha256 = _validate_machine_config(exact_machine_config_bytes)
    _require_exact_digest_hex(
        document["machine_config_sha256"],
        expected=machine_config_sha256,
        code="runtime_manifest_machine_config",
    )
    artifacts = _parse_artifacts(document["artifacts"])
    v7_image_id = _parse_image_id(document["v7_image_id"])
    v6_image_id = _parse_image_id(document["v6_image_id"])
    _require_distinct_image_ids(v7_image_id, v6_image_id)
    identity = _artifact_set_identity_document(
        artifacts=artifacts,
        machine_config_sha256=machine_config_sha256,
        v7_image_id=v7_image_id,
        v6_image_id=v6_image_id,
    )
    expected_artifact_set_id = _artifact_set_id(identity)
    _require_exact_digest_hex(
        document["artifact_set_id"],
        expected=expected_artifact_set_id,
        code="runtime_manifest_artifact_set",
    )
    return CandidateSpotV7FirecrackerRuntimeManifestV1._from_validated(
        canonical_bytes=raw,
        artifact_set_id=expected_artifact_set_id,
        artifacts=artifacts,
        machine_config_sha256=machine_config_sha256,
        v7_image_id=v7_image_id,
        v6_image_id=v6_image_id,
        seal=_RUNTIME_MANIFEST_CONSTRUCTION_SEAL_V1,
    )


def _validate_manifest_header(document: dict[str, Any]) -> None:
    if set(document) != _ROOT_FIELDS_V1:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_fields")
    if (
        document["schema"] != SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1
        or document["status"] != SPOT_V7_RUNTIME_MANIFEST_STATUS_V1
    ):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_version")
    if document["architecture"] != "x86_64":
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_architecture")
    _require_exact_digest_hex(
        document["runtime_profile_sha256"],
        expected=SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
        code="runtime_manifest_runtime_profile",
    )
    _require_exact_digest_hex(
        document["authority_input_profile_sha256"],
        expected=SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1,
        code="runtime_manifest_authority_input_profile",
    )
    if document["guest_entrypoint"] != SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_guest_entrypoint")
    _validate_authority(document["authority"])
    if type(document["non_claims"]) is not list or document["non_claims"] != list(
        _NON_CLAIMS_V1
    ):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_non_claims")


def canonical_document_bytes_v1(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _decode_exact_document(raw: bytes) -> dict[str, Any]:
    if type(raw) is not bytes or not 0 < len(raw) <= _MAX_MANIFEST_BYTES_V1:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_json")
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        ValueError,
    ) as exc:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_json") from exc
    if type(document) is not dict or canonical_document_bytes_v1(document) != raw:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_json")
    return document


def _artifact_set_identity_document(
    *,
    artifacts: tuple[SpotV7RuntimeArtifactIdentityV1, ...],
    machine_config_sha256: bytes,
    v7_image_id: tuple[int, ...],
    v6_image_id: tuple[int, ...],
) -> dict[str, object]:
    return {
        "architecture": "x86_64",
        "artifacts": [row.to_document() for row in artifacts],
        "authority_input_profile_sha256": (
            SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1.hex()
        ),
        "guest_entrypoint": SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1,
        "machine_config_sha256": machine_config_sha256.hex(),
        "runtime_profile_sha256": (SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1.hex()),
        "schema": SPOT_V7_RUNTIME_MANIFEST_SCHEMA_V1,
        "v6_image_id": list(v6_image_id),
        "v7_image_id": list(v7_image_id),
    }


def _artifact_set_id(identity: dict[str, object]) -> bytes:
    body = canonical_document_bytes_v1(identity)
    return hashlib.sha256(
        len(_ARTIFACT_SET_DOMAIN_V1).to_bytes(2, "big") + _ARTIFACT_SET_DOMAIN_V1 + body
    ).digest()


def _parse_artifacts(value: object) -> tuple[SpotV7RuntimeArtifactIdentityV1, ...]:
    if type(value) is not list or len(value) != len(SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_order")
    output: list[SpotV7RuntimeArtifactIdentityV1] = []
    for index, role in enumerate(SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1):
        row = value[index]
        if type(row) is not dict or set(row) != _ARTIFACT_FIELDS_V1:
            raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_fields")
        if row["role"] != role:
            raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_order")
        digest = _require_digest_hex(
            row["sha256"],
            "runtime_manifest_artifact_digest",
        )
        output.append(
            SpotV7RuntimeArtifactIdentityV1.validated(
                role=role,
                artifact_name=row["artifact_name"],
                sha256=digest,
                size_bytes=row["size_bytes"],
            )
        )
    if len({row.sha256 for row in output}) != len(output):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_digest")
    return tuple(output)


def _require_exact_artifact_inventory(
    value: tuple[SpotV7RuntimeArtifactIdentityV1, ...],
) -> tuple[SpotV7RuntimeArtifactIdentityV1, ...]:
    if (
        type(value) is not tuple
        or len(value) != len(SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1)
        or any(type(row) is not SpotV7RuntimeArtifactIdentityV1 for row in value)
        or tuple(row.role for row in value) != SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
        or len({row.sha256 for row in value}) != len(value)
    ):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_order")
    return value


def _validate_machine_config(raw: bytes) -> bytes:
    if type(raw) is not bytes or not 0 < len(raw) <= _MAX_MACHINE_CONFIG_BYTES_V1:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_machine_config")
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        ValueError,
    ) as exc:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_machine_config") from exc
    if type(document) is not dict or canonical_document_bytes_v1(document) != raw:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_machine_config")
    expected = _expected_machine_config_v1()
    if not _exact_json_tree_equal(document, expected):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_machine_config")
    return hashlib.sha256(raw).digest()


def _expected_machine_config_v1() -> dict[str, object]:
    return {
        "boot-source": {
            "boot_args": f"init={SPOT_V7_AUTHORITY_GUEST_ENTRYPOINT_V1}",
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


def _validate_authority(value: object) -> None:
    if type(value) is not dict or set(value) != set(_AUTHORITY_FIELDS_V1):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_authority")
    if any(type(value[name]) is not bool or value[name] is not False for name in value):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_authority")


def _exact_json_tree_equal(actual: object, expected: object) -> bool:
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        actual_map = cast(dict[str, object], actual)
        expected_map = cast(dict[str, object], expected)
        return set(actual_map) == set(expected_map) and all(
            _exact_json_tree_equal(actual_map[key], expected_map[key])
            for key in expected_map
        )
    if type(expected) is list:
        actual_list = cast(list[object], actual)
        expected_list = cast(list[object], expected)
        return len(actual_list) == len(expected_list) and all(
            _exact_json_tree_equal(actual_item, expected_item)
            for actual_item, expected_item in zip(
                actual_list,
                expected_list,
                strict=True,
            )
        )
    return actual == expected


def _parse_image_id(value: object) -> tuple[int, ...]:
    if type(value) is not list:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_image_id")
    return _require_image_id(tuple(value))


def _require_image_id(value: tuple[int, ...]) -> tuple[int, ...]:
    if (
        type(value) is not tuple
        or len(value) != 8
        or any(type(word) is not int or not 0 <= word <= 0xFFFF_FFFF for word in value)
        or not any(value)
    ):
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_image_id")
    return value


def _require_distinct_image_ids(
    v7_image_id: tuple[int, ...],
    v6_image_id: tuple[int, ...],
) -> None:
    if v7_image_id == v6_image_id:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_image_id")


def _require_artifact_role(value: object) -> str:
    if type(value) is not str or value not in SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_order")
    return value


def _require_artifact_size(role: str, value: object) -> int:
    maximum = _MAX_ARTIFACT_BYTES_BY_ROLE_V1[role]
    if type(value) is not int or not 0 < value <= maximum:
        raise SpotV7RuntimeManifestRejectV1("runtime_manifest_artifact_size")
    return value


def _require_exact_digest_hex(value: object, *, expected: bytes, code: str) -> None:
    if _require_digest_hex(value, code) != expected:
        raise SpotV7RuntimeManifestRejectV1(code)


def _require_digest_hex(value: object, code: str) -> bytes:
    if type(value) is not str or len(value) != 64 or value != value.lower():
        raise SpotV7RuntimeManifestRejectV1(code)
    try:
        raw = bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7RuntimeManifestRejectV1(code) from exc
    _require_digest_bytes(raw, code)
    return raw


def _require_digest_bytes(value: object, code: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7RuntimeManifestRejectV1(code)
    return value


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate JSON key")
        output[key] = value
    return output


def _reject_json_number(_value: str) -> NoReturn:
    raise ValueError("non-integer JSON number")
