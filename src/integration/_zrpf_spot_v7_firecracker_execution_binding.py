"""Authority-false exact binding for a proposed Spot V7 Firecracker run.

The current jailed process controller returns ordinary observation documents.
Those documents can be checked for exact internal consistency, but they are
not an attestation and cannot mint the private settlement capability.  This
module closes the data join while keeping the missing runner-owned capability
explicit.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any, Final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_output import (
    SpotV7CommittedOutputRejectV1,
    _bind_decoded_spot_v7_output_to_candidate_v1,
    _BoundCommittedSpotV7CandidateV1,
    _decode_exact_committed_spot_v7_output_v1,
)

SPOT_V7_FIRECRACKER_STATIC_BINDING_BLOCKER_V1: Final = (
    "governed_live_jailed_execution_result_capability_missing"
)

_PROFILE_CANONICAL_SHA256_V1: Final = (
    "e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e"
)
_EXECUTION_RECORD_SCHEMA_V1: Final = (
    "zenodex/zrpf_spot_v7_firecracker_static_execution_record/v1"
)
_MAX_RUNTIME_MANIFEST_BYTES_V1: Final = 256 * 1_024
_MAX_LIFECYCLE_OBSERVATION_BYTES_V1: Final = 64 * 1_024
_LOWER_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_CGROUP_RELATIVE_PATH = re.compile(
    r"/[a-z0-9][a-z0-9-]{7,63}(?:/[a-z0-9][a-z0-9-]{7,63}){1,7}\Z"
)

_LIFECYCLE_AUTHORITY_NONCLAIM_ITEMS_V1: Final = (
    ("chroot_base_live_verified", False),
    ("cgroup_limits_live_verified", False),
    ("cgroup_membership_live_verified", False),
    ("descriptor_bound_exec_handoff_verified", False),
    ("external_watchdog_live_verified", False),
    ("firecracker_jailer_live_verified", False),
    ("io_backing_device_binding_live_verified", False),
    ("network_namespace_exclusive_live_verified", False),
    ("network_namespace_live_verified", False),
    ("production_authority", False),
    ("root_owned_launcher_live_verified", False),
    ("sandbox_escape_resistance", False),
    ("settlement_authority", False),
)
_LAUNCH_CONTROL_FACT_ITEMS_V1: Final = (
    ("cgroup_descendant_set_verified", True),
    ("executable_bytes_reverified_after_spawn", True),
    ("network_namespace_membership_verified", True),
)
_FINISH_CONTROL_FACT_ITEMS_V1: Final = (
    ("cgroup_populated_zero_verified", True),
    ("cgroup_removed_after_kill", True),
    ("network_namespace_path_identity_preserved", True),
    ("process_exit_observed", True),
)


class SpotV7FirecrackerExecutionBindingRejectV1(ValueError):
    """Stable rejection at the authority-false execution data join."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class _ProposedSpotV7FirecrackerExecutionPolicyV1:
    """Exact expected run inputs from a future governed policy source.

    Construction validates shape only.  This value does not establish that the
    caller obtained the expectations from governance.
    """

    exact_runtime_manifest_bytes: bytes
    run_nonce_256: bytes
    input_drive_sha256: bytes
    replay_intent_sha256: bytes
    artifact_set_id: str
    firecracker_sha256: str
    jailer_sha256: str
    guest_kernel_sha256: str
    rootfs_sha256: str
    input_image_sha256: str
    guest_init_sha256: str
    cgroup_relative_path: str

    def __post_init__(self) -> None:
        if (
            type(self.exact_runtime_manifest_bytes) is not bytes
            or not self.exact_runtime_manifest_bytes
            or len(self.exact_runtime_manifest_bytes) > _MAX_RUNTIME_MANIFEST_BYTES_V1
        ):
            raise SpotV7FirecrackerExecutionBindingRejectV1(
                "policy_runtime_manifest"
            )
        for value, code in (
            (self.run_nonce_256, "policy_nonce"),
            (self.input_drive_sha256, "policy_input"),
            (self.replay_intent_sha256, "policy_intent"),
        ):
            _require_digest_bytes(value, code)
        for name in _ARTIFACT_IDENTITY_FIELDS_V1:
            _require_sha256_hex(getattr(self, name), f"policy_{name}")
        if (
            type(self.cgroup_relative_path) is not str
            or _CGROUP_RELATIVE_PATH.fullmatch(self.cgroup_relative_path) is None
        ):
            raise SpotV7FirecrackerExecutionBindingRejectV1("policy_cgroup_path")

    @property
    def runtime_manifest_sha256(self) -> str:
        return hashlib.sha256(self.exact_runtime_manifest_bytes).hexdigest()


_ARTIFACT_IDENTITY_FIELDS_V1: Final = (
    "artifact_set_id",
    "firecracker_sha256",
    "jailer_sha256",
    "guest_kernel_sha256",
    "rootfs_sha256",
    "input_image_sha256",
    "guest_init_sha256",
)


@dataclass(frozen=True, slots=True)
class _ObservedSpotV7FirecrackerArtifactSetV1:
    """Artifact identities reported by staging; still ordinary data."""

    runtime_manifest_sha256: str
    artifact_set_id: str
    firecracker_sha256: str
    jailer_sha256: str
    guest_kernel_sha256: str
    rootfs_sha256: str
    input_image_sha256: str
    guest_init_sha256: str

    def __post_init__(self) -> None:
        _require_sha256_hex(
            self.runtime_manifest_sha256,
            "observed_runtime_manifest_sha256",
        )
        for name in _ARTIFACT_IDENTITY_FIELDS_V1:
            _require_sha256_hex(getattr(self, name), f"observed_{name}")


@dataclass(frozen=True, slots=True, init=False)
class _AuthorityFalseSpotV7FirecrackerExecutionBindingV1:
    """Internally consistent run data with permanently false authority."""

    execution_record_bytes: bytes
    request_sha256: str
    output_device_sha256: str

    def __new__(cls) -> _AuthorityFalseSpotV7FirecrackerExecutionBindingV1:
        raise TypeError(
            "authority-false Firecracker binding requires exact verification"
        )

    @property
    def static_binding_verified(self) -> bool:
        return True

    @property
    def governed_execution_result_verified(self) -> bool:
        return False

    @property
    def firecracker_execution_verified(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def authority_blocker(self) -> str:
        return SPOT_V7_FIRECRACKER_STATIC_BINDING_BLOCKER_V1


@dataclass(frozen=True, slots=True)
class _InspectedSpotV7FirecrackerExecutionV1:
    execution_record_bytes: bytes
    bound_output: _BoundCommittedSpotV7CandidateV1


def _derive_authority_false_spot_v7_execution_record_v1(
    *,
    policy: object,
    observed_artifacts: object,
    request_bytes: object,
    output_device_bytes: object,
    candidate: object,
    launch_observation_bytes: object,
    finish_observation_bytes: object,
) -> bytes:
    """Derive the canonical audit record without checking its candidate copy."""

    return _inspect_authority_false_spot_v7_execution_v1(
        policy=policy,
        observed_artifacts=observed_artifacts,
        request_bytes=request_bytes,
        output_device_bytes=output_device_bytes,
        candidate=candidate,
        launch_observation_bytes=launch_observation_bytes,
        finish_observation_bytes=finish_observation_bytes,
    ).execution_record_bytes


def _verify_authority_false_spot_v7_firecracker_execution_binding_v1(
    *,
    policy: object,
    observed_artifacts: object,
    request_bytes: object,
    output_device_bytes: object,
    candidate: object,
    launch_observation_bytes: object,
    finish_observation_bytes: object,
) -> _AuthorityFalseSpotV7FirecrackerExecutionBindingV1:
    """Verify one complete static join without minting runtime authority."""

    inspected = _inspect_authority_false_spot_v7_execution_v1(
        policy=policy,
        observed_artifacts=observed_artifacts,
        request_bytes=request_bytes,
        output_device_bytes=output_device_bytes,
        candidate=candidate,
        launch_observation_bytes=launch_observation_bytes,
        finish_observation_bytes=finish_observation_bytes,
    )
    exact_candidate = inspected.bound_output.candidate
    if exact_candidate.exact_firecracker_execution_record_bytes != (
        inspected.execution_record_bytes
    ):
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "execution_record_binding"
        )
    result = object.__new__(_AuthorityFalseSpotV7FirecrackerExecutionBindingV1)
    object.__setattr__(
        result,
        "execution_record_bytes",
        inspected.execution_record_bytes,
    )
    object.__setattr__(
        result,
        "request_sha256",
        inspected.bound_output.decoded_output.request_sha256.hex(),
    )
    object.__setattr__(
        result,
        "output_device_sha256",
        inspected.bound_output.decoded_output.output_device_sha256.hex(),
    )
    return result


def _inspect_authority_false_spot_v7_execution_v1(
    *,
    policy: object,
    observed_artifacts: object,
    request_bytes: object,
    output_device_bytes: object,
    candidate: object,
    launch_observation_bytes: object,
    finish_observation_bytes: object,
) -> _InspectedSpotV7FirecrackerExecutionV1:
    if type(policy) is not _ProposedSpotV7FirecrackerExecutionPolicyV1:
        raise TypeError("policy must be exact proposed Spot V7 Firecracker policy")
    if type(observed_artifacts) is not _ObservedSpotV7FirecrackerArtifactSetV1:
        raise TypeError("observed_artifacts must be exact Spot V7 artifact data")
    if type(candidate) is not _SpotV7SettlementCandidateInputV1:
        raise TypeError("candidate must be exact Spot V7 settlement candidate")
    if type(request_bytes) is not bytes or type(output_device_bytes) is not bytes:
        raise TypeError("request and output device must be exact bytes")

    _require_artifact_binding(policy, observed_artifacts)
    try:
        decoded = _decode_exact_committed_spot_v7_output_v1(
            request_bytes=request_bytes,
            output_device_bytes=output_device_bytes,
        )
    except SpotV7CommittedOutputRejectV1 as exc:
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            f"output_{exc.code}"
        ) from exc
    _require_request_binding(policy, request_bytes)
    try:
        bound = _bind_decoded_spot_v7_output_to_candidate_v1(
            decoded_output=decoded,
            candidate=candidate,
        )
    except (SpotV7CommittedOutputRejectV1, TypeError, ValueError) as exc:
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "v7_candidate_binding"
        ) from exc
    launch = _validate_launch_observation(
        launch_observation_bytes,
        expected_cgroup_relative_path=policy.cgroup_relative_path,
    )
    finish = _validate_finish_observation(
        finish_observation_bytes,
        launch_observation_bytes=launch_observation_bytes,
        launch=launch,
    )
    record = _execution_record_bytes(
        policy=policy,
        observed_artifacts=observed_artifacts,
        request_bytes=request_bytes,
        output_device_bytes=output_device_bytes,
        bound_output=bound,
        launch_observation_bytes=launch_observation_bytes,
        finish_observation_bytes=finish_observation_bytes,
        launch=launch,
        finish=finish,
    )
    return _InspectedSpotV7FirecrackerExecutionV1(record, bound)


def _require_artifact_binding(
    policy: _ProposedSpotV7FirecrackerExecutionPolicyV1,
    observed: _ObservedSpotV7FirecrackerArtifactSetV1,
) -> None:
    expected = (
        policy.runtime_manifest_sha256,
        *(getattr(policy, name) for name in _ARTIFACT_IDENTITY_FIELDS_V1),
    )
    actual = (
        observed.runtime_manifest_sha256,
        *(getattr(observed, name) for name in _ARTIFACT_IDENTITY_FIELDS_V1),
    )
    if actual != expected:
        raise SpotV7FirecrackerExecutionBindingRejectV1("artifact_binding")


def _require_request_binding(
    policy: _ProposedSpotV7FirecrackerExecutionPolicyV1,
    request: bytes,
) -> None:
    comparisons = (
        (request[16:48], policy.run_nonce_256, "request_nonce_binding"),
        (
            request[48:80].hex(),
            _PROFILE_CANONICAL_SHA256_V1,
            "request_profile_binding",
        ),
        (
            request[80:112].hex(),
            policy.runtime_manifest_sha256,
            "request_runtime_manifest_binding",
        ),
        (request[112:144], policy.input_drive_sha256, "request_input_binding"),
        (request[156:188], policy.replay_intent_sha256, "request_intent_binding"),
    )
    for actual, expected, code in comparisons:
        if actual != expected:
            raise SpotV7FirecrackerExecutionBindingRejectV1(code)


def _validate_launch_observation(
    raw: object,
    *,
    expected_cgroup_relative_path: str,
) -> dict[str, Any]:
    document = _parse_canonical_document(raw, label="lifecycle_launch")
    if set(document) != {
        "authority",
        "cgroup_relative_path",
        "control_facts",
        "jailer_pid",
        "observed_process_count",
        "schema",
        "scope",
    }:
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "lifecycle_launch_fields"
        )
    _require_exact_bool_document(
        document["authority"],
        expected_items=_LIFECYCLE_AUTHORITY_NONCLAIM_ITEMS_V1,
        code="lifecycle_launch_authority",
    )
    _require_exact_bool_document(
        document["control_facts"],
        expected_items=_LAUNCH_CONTROL_FACT_ITEMS_V1,
        code="lifecycle_launch_binding",
    )
    if (
        document["schema"]
        != "zenodex/zrpf_firecracker_jailer_launch_observation/v1"
        or document["scope"] != "live_process_placement_control_only"
        or document["cgroup_relative_path"] != expected_cgroup_relative_path
        or not _bounded_positive_int(document["jailer_pid"], maximum=(1 << 31) - 1)
        or not _bounded_positive_int(document["observed_process_count"], maximum=64)
    ):
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "lifecycle_launch_binding"
        )
    return document


def _validate_finish_observation(
    raw: object,
    *,
    launch_observation_bytes: object,
    launch: dict[str, Any],
) -> dict[str, Any]:
    document = _parse_canonical_document(raw, label="lifecycle_finish")
    if set(document) != {
        "authority",
        "cgroup_relative_path",
        "control_facts",
        "exit_code",
        "jailer_pid",
        "launch_observation_sha256",
        "observed_process_count",
        "schema",
        "scope",
    }:
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "lifecycle_finish_fields"
        )
    _require_exact_bool_document(
        document["authority"],
        expected_items=_LIFECYCLE_AUTHORITY_NONCLAIM_ITEMS_V1,
        code="lifecycle_finish_authority",
    )
    _require_exact_bool_document(
        document["control_facts"],
        expected_items=_FINISH_CONTROL_FACT_ITEMS_V1,
        code="lifecycle_finish_binding",
    )
    if (
        document["cgroup_relative_path"] != launch["cgroup_relative_path"]
        or document["jailer_pid"] != launch["jailer_pid"]
        or document["observed_process_count"] != launch["observed_process_count"]
        or document["launch_observation_sha256"]
        != _sha256_object_bytes(launch_observation_bytes)
    ):
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "lifecycle_finish_launch_binding"
        )
    exit_code = document["exit_code"]
    if (
        document["schema"]
        != "zenodex/zrpf_firecracker_jailer_finish_observation/v2"
        or document["scope"]
        != "live_process_exit_and_exact_launch_teardown_control_only"
        or type(exit_code) is not int
        or not -(1 << 31) <= exit_code <= (1 << 31) - 1
    ):
        raise SpotV7FirecrackerExecutionBindingRejectV1(
            "lifecycle_finish_binding"
        )
    return document


def _execution_record_bytes(
    *,
    policy: _ProposedSpotV7FirecrackerExecutionPolicyV1,
    observed_artifacts: _ObservedSpotV7FirecrackerArtifactSetV1,
    request_bytes: bytes,
    output_device_bytes: bytes,
    bound_output: _BoundCommittedSpotV7CandidateV1,
    launch_observation_bytes: object,
    finish_observation_bytes: object,
    launch: dict[str, Any],
    finish: dict[str, Any],
) -> bytes:
    candidate = bound_output.candidate
    decoded = bound_output.decoded_output
    document = {
        "artifact_binding": {
            name: getattr(observed_artifacts, name)
            for name in ("runtime_manifest_sha256", *_ARTIFACT_IDENTITY_FIELDS_V1)
        },
        "authority": {
            "firecracker_execution_verified": False,
            "governed_execution_result_verified": False,
            "production_authority": False,
            "settlement_authority": False,
        },
        "authority_blocker": SPOT_V7_FIRECRACKER_STATIC_BINDING_BLOCKER_V1,
        "candidate_data": {
            "application_id_unverified": candidate.application_id,
            "chain_or_domain_id_unverified": candidate.chain_or_domain_id,
            "epoch_id_unverified": candidate.epoch_id,
            "retained_receipt_sha256_unverified": hashlib.sha256(
                candidate.exact_v7_receipt_bytes
            ).hexdigest(),
        },
        "output_bound_candidate_data": {
            "journal_sha256": hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest(),
            "plan_b_sha256": hashlib.sha256(candidate.exact_plan_b_bytes).hexdigest(),
        },
        "lifecycle_binding": {
            "cgroup_relative_path": policy.cgroup_relative_path,
            "exit_code": finish["exit_code"],
            "finish_observation_sha256": _sha256_object_bytes(finish_observation_bytes),
            "jailer_pid": launch["jailer_pid"],
            "launch_observation_sha256": _sha256_object_bytes(launch_observation_bytes),
            "observed_process_count": launch["observed_process_count"],
        },
        "output_binding": {
            "output_device_sha256": hashlib.sha256(output_device_bytes).hexdigest(),
            "output_device_size_bytes": len(output_device_bytes),
            "output_payload_sha256": decoded.output_payload_sha256.hex(),
            "output_payload_size_bytes": len(decoded.output_payload_bytes),
        },
        "request_binding": {
            "firecracker_profile_canonical_sha256": _PROFILE_CANONICAL_SHA256_V1,
            "input_drive_sha256": policy.input_drive_sha256.hex(),
            "replay_intent_sha256": policy.replay_intent_sha256.hex(),
            "request_sha256": hashlib.sha256(request_bytes).hexdigest(),
            "run_nonce_256": policy.run_nonce_256.hex(),
            "runtime_manifest_sha256": policy.runtime_manifest_sha256,
        },
        "schema": _EXECUTION_RECORD_SCHEMA_V1,
        "status": "static_binding_verified_authority_false",
    }
    return _canonical_document_bytes(document)


def _parse_canonical_document(raw: object, *, label: str) -> dict[str, Any]:
    if (
        type(raw) is not bytes
        or not raw
        or len(raw) > _MAX_LIFECYCLE_OBSERVATION_BYTES_V1
    ):
        raise SpotV7FirecrackerExecutionBindingRejectV1(f"{label}_bytes")
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        ValueError,
    ) as exc:
        raise SpotV7FirecrackerExecutionBindingRejectV1(f"{label}_parse") from exc
    if type(document) is not dict:
        raise SpotV7FirecrackerExecutionBindingRejectV1(f"{label}_object")
    if raw != _canonical_document_bytes(document):
        raise SpotV7FirecrackerExecutionBindingRejectV1(f"{label}_noncanonical")
    return document


def _canonical_document_bytes(document: object) -> bytes:
    return (
        json.dumps(document, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def _sha256_object_bytes(value: object) -> str:
    if type(value) is not bytes:
        raise TypeError("canonical observation must be bytes")
    return hashlib.sha256(value).hexdigest()


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate key")
        output[key] = value
    return output


def _reject_constant(_value: str) -> None:
    raise ValueError("non-finite number")


def _bounded_positive_int(value: object, *, maximum: int) -> bool:
    return type(value) is int and 0 < value <= maximum


def _require_exact_bool_document(
    value: object,
    *,
    expected_items: tuple[tuple[str, bool], ...],
    code: str,
) -> None:
    if type(value) is not dict or set(value) != {name for name, _ in expected_items}:
        raise SpotV7FirecrackerExecutionBindingRejectV1(code)
    for name, expected in expected_items:
        actual = value[name]
        if type(actual) is not bool or actual is not expected:
            raise SpotV7FirecrackerExecutionBindingRejectV1(code)


def _require_digest_bytes(value: bytes, code: str) -> None:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7FirecrackerExecutionBindingRejectV1(code)


def _require_sha256_hex(value: object, code: str) -> None:
    if type(value) is not str or _LOWER_SHA256.fullmatch(value) is None or not int(value, 16):
        raise SpotV7FirecrackerExecutionBindingRejectV1(code)
