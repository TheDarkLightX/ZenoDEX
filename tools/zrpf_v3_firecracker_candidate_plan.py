"""Pure compiler for a non-executable ZRPF Firecracker candidate plan."""

from __future__ import annotations

import hashlib
import importlib
import json
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from tools.zrpf_v3_firecracker_artifact_set import (
        LocallyBoundRuntimeArtifactSetV1,
    )
    from tools.zrpf_v3_firecracker_output_protocol import FirecrackerRequestV1
    from tools.zrpf_v3_firecracker_runtime_manifest import (
        PinnedRuntimeManifestV1,
    )

_MODULE_PREFIX = "tools." if __package__ else ""
artifacts = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_artifact_set")
runtime = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")
protocol = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_output_protocol")

INTENT_SCHEMA = "zenodex/zrpf_firecracker_replay_intent/v1"
PLAN_SCHEMA = "zenodex/zrpf_firecracker_candidate_launch_plan/v1"
_INTENT_FIELDS = {
    "expected_output_payload_sha256",
    "expected_output_payload_size_bytes",
    "input_bundle_root",
    "input_drive_sha256",
    "input_size_bytes",
    "schema",
}
_AUTHORITY_FIELDS = (
    "guest_boot_verified",
    "microvm_replay_verified",
    "production_authority",
    "release_authority",
    "root_launcher_ready",
    "runtime_artifacts_authorized_for_path_reuse",
    "sandbox_escape_resistance",
    "settlement_authority",
)
_ROOT_ALLOCATIONS = (
    "cgroup_path",
    "gid",
    "jail_id",
    "netns_identity",
    "output_object",
    "run_nonce_256",
    "uid",
)
_ALWAYS_BLOCKERS = (
    "binary_request_pending_root_nonce_allocation",
    "measured_numeric_resource_envelope_pending",
    "root_owned_artifact_staging_pending",
    "root_owned_launcher_pending",
    "sandbox_escape_controls_pending",
)
_RATE_LIMITER = {
    "bandwidth": {
        "one_time_burst": 0,
        "refill_time": 1_000,
        "size": 67_108_864,
    },
    "ops": {"one_time_burst": 0, "refill_time": 1_000, "size": 4_096},
}


class CandidatePlanError(ValueError):
    """Stable fail-closed error raised at intent or plan compilation."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True, init=False)
class ValidatedReplayIntentV1:
    """Canonical public replay intent; it carries no launch authority."""

    expected_output_payload_sha256: str
    expected_output_payload_size_bytes: int
    input_bundle_root: str
    input_drive_sha256: str
    input_size_bytes: int
    intent_sha256: str

    def __new__(cls) -> ValidatedReplayIntentV1:
        raise TypeError("ValidatedReplayIntentV1 requires validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        expected_output_payload_sha256: str,
        expected_output_payload_size_bytes: int,
        input_bundle_root: str,
        input_drive_sha256: str,
        input_size_bytes: int,
        intent_sha256: str,
    ) -> ValidatedReplayIntentV1:
        value = object.__new__(cls)
        object.__setattr__(
            value,
            "expected_output_payload_sha256",
            expected_output_payload_sha256,
        )
        object.__setattr__(
            value,
            "expected_output_payload_size_bytes",
            expected_output_payload_size_bytes,
        )
        object.__setattr__(value, "input_bundle_root", input_bundle_root)
        object.__setattr__(value, "input_drive_sha256", input_drive_sha256)
        object.__setattr__(value, "input_size_bytes", input_size_bytes)
        object.__setattr__(value, "intent_sha256", intent_sha256)
        return value

    def to_document(self) -> dict[str, Any]:
        return {
            "expected_output_payload_sha256": self.expected_output_payload_sha256,
            "expected_output_payload_size_bytes": (self.expected_output_payload_size_bytes),
            "input_bundle_root": self.input_bundle_root,
            "input_drive_sha256": self.input_drive_sha256,
            "input_size_bytes": self.input_size_bytes,
            "schema": INTENT_SCHEMA,
        }


@dataclass(frozen=True, slots=True, init=False)
class CompiledCandidateLaunchPlanV1:
    """Deterministic plan data that is deliberately insufficient to execute."""

    _document_without_id_bytes: bytes
    candidate_plan_id: str

    def __new__(cls) -> CompiledCandidateLaunchPlanV1:
        raise TypeError("CompiledCandidateLaunchPlanV1 requires deterministic compilation")

    @classmethod
    def _from_compiled(
        cls,
        document_without_id: dict[str, Any],
    ) -> CompiledCandidateLaunchPlanV1:
        value = object.__new__(cls)
        object.__setattr__(
            value,
            "_document_without_id_bytes",
            runtime.canonical_document_bytes(document_without_id),
        )
        object.__setattr__(
            value,
            "candidate_plan_id",
            runtime.canonical_sha256_hex(
                {
                    "domain": "zenodex/zrpf_firecracker_candidate_plan_id/v1",
                    "plan": document_without_id,
                }
            ),
        )
        return value

    def to_document(self) -> dict[str, Any]:
        document = json.loads(self._document_without_id_bytes)
        if not isinstance(document, dict):  # pragma: no cover - internal invariant
            raise RuntimeError("compiled candidate plan lost its object shape")
        document["candidate_plan_id"] = self.candidate_plan_id
        return document

    def canonical_bytes(self) -> bytes:
        return runtime.canonical_document_bytes(self.to_document())


def parse_replay_intent_bytes(raw: bytes) -> ValidatedReplayIntentV1:
    """Decode one bounded canonical intent for later root-owned request creation."""

    if not 0 < len(raw) <= runtime.PAYLOAD_CAP_BYTES:
        raise CandidatePlanError("candidate_intent_size_invalid")
    try:
        document = _strict_json_loads(raw)
    except (RecursionError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise CandidatePlanError("candidate_intent_input_rejected") from exc
    if not isinstance(document, dict):
        raise CandidatePlanError("candidate_intent_root_not_object")
    if raw != runtime.canonical_document_bytes(document):
        raise CandidatePlanError("candidate_intent_noncanonical")
    if set(document) != _INTENT_FIELDS:
        raise CandidatePlanError("candidate_intent_fields_mismatch")
    if document["schema"] != INTENT_SCHEMA:
        raise CandidatePlanError("candidate_intent_schema_mismatch")
    expected_payload_sha256 = _sha256(document["expected_output_payload_sha256"])
    expected_payload_size = _positive_int(
        document["expected_output_payload_size_bytes"],
        maximum=runtime.PAYLOAD_CAP_BYTES,
        code="candidate_intent_output_payload_size_invalid",
    )
    input_bundle_root = _sha256(document["input_bundle_root"])
    input_drive_sha256 = _sha256(document["input_drive_sha256"])
    input_size_bytes = _positive_int(
        document["input_size_bytes"],
        maximum=runtime.MAX_INPUT_IMAGE_BYTES,
        code="candidate_intent_input_size_invalid",
    )
    return ValidatedReplayIntentV1._from_validated(
        expected_output_payload_sha256=expected_payload_sha256,
        expected_output_payload_size_bytes=expected_payload_size,
        input_bundle_root=input_bundle_root,
        input_drive_sha256=input_drive_sha256,
        input_size_bytes=input_size_bytes,
        intent_sha256=hashlib.sha256(raw).hexdigest(),
    )


def compile_candidate_plan(
    manifest: PinnedRuntimeManifestV1,
    intent: ValidatedReplayIntentV1,
    *,
    locally_bound_artifacts: LocallyBoundRuntimeArtifactSetV1 | None = None,
) -> CompiledCandidateLaunchPlanV1:
    """Compile a path-free plan whose authority and readiness remain false."""

    _verify_intent_input_binding(manifest, intent)
    artifact_status = "not_supplied"
    blockers = list(_ALWAYS_BLOCKERS)
    if locally_bound_artifacts is None:
        blockers.insert(0, "artifact_bytes_not_locally_bound")
    else:
        _verify_local_binding(manifest, locally_bound_artifacts)
        artifact_status = "exact_match"
    replay_binding = {
        "expected_output_payload_sha256": intent.expected_output_payload_sha256,
        "expected_output_payload_size_bytes": (intent.expected_output_payload_size_bytes),
        "input_bundle_root": intent.input_bundle_root,
        "input_drive_sha256": intent.input_drive_sha256,
        "input_protocol_id": runtime.INPUT_PROTOCOL_ID,
        "input_size_bytes": intent.input_size_bytes,
        "intent_protocol_id": INTENT_SCHEMA,
        "intent_sha256": intent.intent_sha256,
        "output_protocol_id": runtime.OUTPUT_PROTOCOL_ID,
        "output_size_bytes": runtime.OUTPUT_SIZE_BYTES,
        "request_protocol_id": runtime.REQUEST_PROTOCOL_ID,
    }
    runtime_identities = {
        "artifact_set_id": manifest.artifact_set_id,
        "guest_kernel_sha256": manifest.guest_kernel.artifact.sha256,
        "guest_kernel_size_bytes": manifest.guest_kernel.artifact.size_bytes,
        "guest_payload_manifest_sha256": (manifest.rootfs.guest_payload_manifest_sha256),
        "input_image_sha256": manifest.input_image.artifact.sha256,
        "input_image_size_bytes": manifest.input_image.artifact.size_bytes,
        "rootfs_sha256": manifest.rootfs.artifact.sha256,
        "rootfs_size_bytes": manifest.rootfs.artifact.size_bytes,
    }
    document = {
        "artifact_bytes_status": artifact_status,
        "authority": {name: False for name in _AUTHORITY_FIELDS},
        "execution_blockers": blockers,
        "firecracker_profile_canonical_sha256": (runtime.PROFILE_CANONICAL_SHA256),
        "microvm_configuration_template": candidate_microvm_configuration(manifest),
        "replay_binding": replay_binding,
        "root_owned_allocations": list(_ROOT_ALLOCATIONS),
        "runtime_identities": runtime_identities,
        "runtime_manifest_canonical_sha256": manifest.canonical_sha256,
        "schema": PLAN_SCHEMA,
        "status": "candidate_compiled_non_executable",
    }
    return CompiledCandidateLaunchPlanV1._from_compiled(document)


def candidate_microvm_configuration(
    manifest: PinnedRuntimeManifestV1,
) -> dict[str, Any]:
    """Return the exact candidate configuration before root-owned path staging."""

    drives = (
        (
            "rootfs",
            "/rootfs",
            True,
            True,
        ),
        (
            "input",
            "/input",
            False,
            True,
        ),
        (
            "output",
            "/output",
            False,
            False,
        ),
    )
    return {
        "boot-source": {
            "boot_args": manifest.boot_contract.kernel_cmdline,
            "kernel_image_path": "/kernel",
        },
        "drives": [
            {
                "cache_type": "Writeback",
                "drive_id": drive_id,
                "io_engine": "Sync",
                "is_read_only": read_only,
                "is_root_device": root_device,
                "path_on_host": path,
                "rate_limiter": _fresh_rate_limiter(),
            }
            for drive_id, path, root_device, read_only in drives
        ],
        "machine-config": {
            "cpu_template": "None",
            "huge_pages": "None",
            "mem_size_mib": 256,
            "smt": False,
            "track_dirty_pages": False,
            "vcpu_count": 1,
        },
    }


def compile_binary_request(
    plan: CompiledCandidateLaunchPlanV1,
    *,
    run_nonce_256: bytes,
) -> FirecrackerRequestV1:
    """Bind a root-supplied nonce to the exact manifest, input, and intent."""

    document = plan.to_document()
    replay_binding = document["replay_binding"]
    return protocol.FirecrackerRequestV1.validated(
        run_nonce_256=run_nonce_256,
        runtime_manifest_sha256=bytes.fromhex(document["runtime_manifest_canonical_sha256"]),
        input_drive_sha256=bytes.fromhex(replay_binding["input_drive_sha256"]),
        replay_intent_sha256=bytes.fromhex(replay_binding["intent_sha256"]),
    )


def _fresh_rate_limiter() -> dict[str, Any]:
    return {category: dict(bucket) for category, bucket in _RATE_LIMITER.items()}


def _verify_local_binding(
    manifest: PinnedRuntimeManifestV1,
    bound: LocallyBoundRuntimeArtifactSetV1,
) -> None:
    expected = (
        manifest.artifact_set_id,
        "guest_kernel",
        manifest.guest_kernel.artifact.sha256,
        manifest.guest_kernel.artifact.size_bytes,
        "input_image",
        manifest.input_image.artifact.sha256,
        manifest.input_image.artifact.size_bytes,
        "rootfs",
        manifest.rootfs.artifact.sha256,
        manifest.rootfs.artifact.size_bytes,
    )
    actual = (
        bound.artifact_set_id,
        bound.guest_kernel.role,
        bound.guest_kernel.sha256,
        bound.guest_kernel.size_bytes,
        bound.input_image.role,
        bound.input_image.sha256,
        bound.input_image.size_bytes,
        bound.rootfs.role,
        bound.rootfs.sha256,
        bound.rootfs.size_bytes,
    )
    if actual != expected:
        raise CandidatePlanError("candidate_plan_artifact_binding_mismatch")


def _verify_intent_input_binding(
    manifest: PinnedRuntimeManifestV1,
    intent: ValidatedReplayIntentV1,
) -> None:
    expected = (
        manifest.input_image.artifact.sha256,
        manifest.input_image.artifact.size_bytes,
        manifest.input_image.input_bundle_root,
    )
    actual = (
        intent.input_drive_sha256,
        intent.input_size_bytes,
        intent.input_bundle_root,
    )
    if actual != expected:
        raise CandidatePlanError("candidate_plan_input_binding_mismatch")


def _sha256(value: Any) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or value == "0" * 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise CandidatePlanError("candidate_intent_digest_invalid")
    return value


def _positive_int(value: Any, *, maximum: int, code: str) -> int:
    if type(value) is not int or not 0 < value <= maximum:
        raise CandidatePlanError(code)
    return value


def _strict_json_loads(raw: bytes) -> Any:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise ValueError("duplicate key")
            output[key] = value
        return output

    def reject_constant(_value: str) -> None:
        raise ValueError("non-finite number")

    return json.loads(
        raw.decode("ascii"),
        object_pairs_hook=unique_object,
        parse_constant=reject_constant,
    )
