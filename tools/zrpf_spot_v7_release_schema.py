"""Exact schemas and declared build identities for the Spot V7 release lane."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools import zrpf_v6_v7_child_policy_materialization as child_materializer

PLAN_SCHEMA = "zenodex/zrpf_spot_v7_release_closure_plan/v1"
EVIDENCE_SCHEMA = "zenodex/zrpf_spot_v7_release_closure_evidence/v1"
RUNTIME_IDENTITY_SCHEMA = "zenodex/zrpf_build_runtime_identity/v1"
V7_WORKSPACE_MANIFEST = "zk/spot_settlement_v7_risc0/Cargo.toml"
V7_CHILD_POLICY_PATH = child_materializer.V7_CHILD_POLICY_PATH
V7_CHILD_POLICY_SYMBOL = child_materializer.V7_CHILD_POLICY_SYMBOL

MAX_RUNTIME_STRING_CHARS = 512
MAX_RUNTIME_BINARY_BYTES = 256 * 1024 * 1024

AUTHORITY_FIELDS = (
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "data_availability_verified",
    "finality_verified",
    "proofs_generated",
    "receipts_verified",
    "release_authority",
    "settlement_authority",
    "source_to_program_binary_provenance_verified",
    "production_authority",
)
NON_CLAIMS = (
    "plan_and_evidence_bind_committed_source_and_declared_build_inputs_only",
    "runtime_identity_is_caller_observed_and_not_live_attested_by_this_checker",
    "build_scripts_may_read_inputs_not_discoverable_from_cargo_path_dependencies",
    "no_complete_build_input_closure",
    "no_cross_host_reproducible_build",
    "no_program_binary_or_image_identity_generated",
    "no_proof_or_receipt_generation_or_verification",
    "no_data_availability_or_finality_authority",
    "no_release_authority",
    "no_settlement_authority",
    "no_production_authority",
)

PLAN_FIELDS = {
    "schema",
    "status",
    "ancestry",
    "v7_child_pin",
    "source_closure",
    "build_closure",
    "required_future_release_evidence",
    "authority",
    "non_claims",
}
_RUNTIME_FIELDS = {
    "schema",
    "container_engine",
    "build_image",
    "cargo_registry",
    "observation",
}
_ENGINE_FIELDS = {
    "name",
    "client_executable_sha256",
    "client_executable_bytes",
    "client_version",
    "server_version",
    "server_api_version",
    "oci_runtime_name",
    "oci_runtime_version",
    "server_architecture",
    "server_os",
    "kernel_release",
    "cgroup_mode",
}
_REGISTRY_FIELDS = {
    "schema",
    "root_sha256",
    "file_count",
    "total_bytes",
    "components",
    "maximum_files",
    "maximum_total_bytes",
    "maximum_file_bytes",
}
_OBSERVATION_FIELDS = {
    "network_disabled_before_build",
    "clean_target_verified",
    "cargo_locked",
    "cargo_offline",
    "runtime_observation_is_live_attested",
}


class ReleaseClosureError(ValueError):
    """Stable fail-closed V7 release-closure rejection."""


def canonical_bytes(document: Any) -> bytes:
    return v6_planner.canonical_bytes(document)


def canonical_sha256(document: Any) -> str:
    return hashlib.sha256(canonical_bytes(document)).hexdigest()


def validate_runtime_identity(value: Any) -> dict[str, Any]:
    """Validate and detach the authority-neutral runner observation."""

    require_exact_fields(value, _RUNTIME_FIELDS, "runtime identity")
    require_equal(value["schema"], RUNTIME_IDENTITY_SCHEMA, "runtime schema")
    _validate_engine(value["container_engine"])
    _validate_image(value["build_image"])
    _validate_registry(value["cargo_registry"])
    require_exact_fields(value["observation"], _OBSERVATION_FIELDS, "observation")
    require_equal(
        value["observation"],
        {
            "network_disabled_before_build": True,
            "clean_target_verified": True,
            "cargo_locked": True,
            "cargo_offline": True,
            "runtime_observation_is_live_attested": False,
        },
        "runtime observation",
    )
    return json.loads(canonical_bytes(value))


def build_closure(runtime: dict[str, Any]) -> dict[str, Any]:
    """Bind fixed toolchain/container policy and one exact runtime record."""

    return {
        "toolchain": dict(v6_planner.TOOLCHAIN),
        "build_container": {
            "image_id": v6_planner.BUILD_IMAGE,
            "parent_digest": v6_planner.BUILD_IMAGE_PARENT,
            "canonical_source_root": v6_planner.CANONICAL_SOURCE_ROOT,
            "outer_cargo_path": v6_planner.CANONICAL_CARGO,
            "nested_cargo_path": v6_planner.CANONICAL_CARGO,
            "rustc_path": v6_planner.CANONICAL_RUSTC,
            "r0vm_path": v6_planner.CANONICAL_R0VM,
            "cargo_risczero_path": v6_planner.CANONICAL_CARGO_RISCZERO,
            "nested_cargo_wrapper_sha256": v6_planner.NESTED_CARGO_WRAPPER_SHA256,
            "cargo_locked": True,
            "cargo_offline": True,
            "network_disabled": True,
            "fresh_target_required": True,
            "fresh_output_required": True,
        },
        "runtime_identity": runtime,
        "runtime_identity_sha256": canonical_sha256(runtime),
        "complete_build_input_closure_verified": False,
    }


def _validate_engine(value: Any) -> None:
    require_exact_fields(value, _ENGINE_FIELDS, "container engine")
    require_equal(value["name"], "docker", "container engine name")
    require_nonzero_hex(value["client_executable_sha256"], 64, "container client SHA-256")
    require_positive_int(
        value["client_executable_bytes"],
        MAX_RUNTIME_BINARY_BYTES,
        "container client bytes",
    )
    for field in (
        "client_version",
        "server_version",
        "server_api_version",
        "oci_runtime_name",
        "oci_runtime_version",
        "server_architecture",
        "kernel_release",
    ):
        require_bounded_text(value[field], f"container engine {field}")
    require_equal(value["server_os"], "linux", "container server OS")
    require_equal(value["cgroup_mode"], "v2", "container cgroup mode")


def _validate_image(value: Any) -> None:
    require_exact_fields(value, {"image_id", "parent_digest"}, "build image")
    require_equal(value["image_id"], v6_planner.BUILD_IMAGE, "build image ID")
    require_equal(
        value["parent_digest"],
        v6_planner.BUILD_IMAGE_PARENT,
        "build image parent digest",
    )


def _validate_registry(value: Any) -> None:
    require_exact_fields(value, _REGISTRY_FIELDS, "Cargo registry identity")
    require_equal(
        value["schema"],
        v6_planner.CARGO_REGISTRY_IDENTITY_SCHEMA,
        "Cargo registry schema",
    )
    require_nonzero_hex(value["root_sha256"], 64, "Cargo registry root")
    require_positive_int(value["file_count"], v6_planner.MAX_CARGO_REGISTRY_FILES, "registry files")
    require_positive_int(
        value["total_bytes"], v6_planner.MAX_CARGO_REGISTRY_BYTES, "registry bytes"
    )
    require_equal(value["components"], ["cache", "index", "src"], "registry parts")
    for field, expected in (
        ("maximum_files", v6_planner.MAX_CARGO_REGISTRY_FILES),
        ("maximum_total_bytes", v6_planner.MAX_CARGO_REGISTRY_BYTES),
        ("maximum_file_bytes", v6_planner.MAX_CARGO_REGISTRY_FILE_BYTES),
    ):
        require_equal(value[field], expected, f"Cargo registry {field}")


def require_exact_fields(value: Any, expected: set[str], label: str) -> None:
    if type(value) is not dict or set(value) != expected:
        raise ReleaseClosureError(f"{label} fields differ from the exact schema")


def require_equal(actual: Any, expected: Any, label: str) -> None:
    if type(actual) is not type(expected) or actual != expected:
        raise ReleaseClosureError(f"{label} mismatch")


def require_nonzero_hex(value: Any, length: int, label: str) -> None:
    if (
        type(value) is not str
        or re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is None
        or not any(character != "0" for character in value)
    ):
        raise ReleaseClosureError(f"{label} must be nonzero lowercase hexadecimal")


def require_positive_int(value: Any, maximum: int, label: str) -> None:
    if type(value) is not int or not 0 < value <= maximum:
        raise ReleaseClosureError(f"{label} is outside its positive bound")


def require_bounded_text(value: Any, label: str) -> None:
    if (
        type(value) is not str
        or not value
        or len(value) > MAX_RUNTIME_STRING_CHARS
        or any(ord(character) < 32 or ord(character) == 127 for character in value)
    ):
        raise ReleaseClosureError(f"{label} is empty, unbounded, or contains controls")
