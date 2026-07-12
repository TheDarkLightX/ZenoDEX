#!/usr/bin/env python3
"""Fail closed over the governed ZRPF direct Firecracker replay evidence."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""

candidate_plan = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_candidate_plan")
profile_checker = importlib.import_module(
    f"{_MODULE_PREFIX}check_zrpf_v3_firecracker_replay_profile"
)
protocol = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_output_protocol")
runtime = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")

REPO_ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = (
    REPO_ROOT / "docs/research/ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260712.json"
)
OUTPUT_PAYLOAD_PATH = (
    REPO_ROOT / "evidence/zrpf-v3-retained-structural-replay-v1/"
    "firecracker-governed-output-payload.json"
)
DIRECT_RECORD_ROOT = (
    REPO_ROOT / "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-direct-v2"
)
EXECUTED_CONFIG_PATH = DIRECT_RECORD_ROOT / "config.json"
LOCAL_REPORT_PATH = DIRECT_RECORD_ROOT / "local-report.json"
FIRECRACKER_STDOUT_PATH = DIRECT_RECORD_ROOT / "firecracker.stdout"
MANIFEST_PATH = (
    REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v2.json"
)
INTENT_PATH = REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_intent_v1.json"
PROFILE_PATH = REPO_ROOT / "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json"

EXPECTED_EVIDENCE_RAW_SHA256 = "4f67cb91262f4451ab26c97d46f88cd1028b92841f2ab1ea196ae31126bc213f"
EXPECTED_MANIFEST_CANONICAL_SHA256 = (
    "a4f1509fe13cdd3d6888bca12ffaddd368cd4b9dea7ab1c84783e466c245e405"
)
EXPECTED_PROFILE_CANONICAL_SHA256 = (
    "e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e"
)
EXPECTED_CANDIDATE_PLAN_ID = "f182caf46a909a269f76781aeaa9b2e6a44e0282fe29f579ff8ff40108f465f4"
EXPECTED_CANDIDATE_PLAN_CANONICAL_SHA256 = (
    "000e5ebb324d29d3d63345dc4b0c0a5d4f85e937de29c49ba6db0bcf5d8e6a94"
)
EXPECTED_EXECUTED_CONFIG_SHA256 = "57ec01c81848cb388e88c51e4278ff1ab05af494e8e733eb7fe8653292f68f96"
EXPECTED_REQUEST_SHA256 = "8b81d4cd696d12c73166ad7c66b32cc3f713ad97eec9693c3051a9025b0ef079"
EXPECTED_OUTPUT_SHA256 = "c95d42b86acae77241cb683ef8c1863ade95e986752da58ba6c4d592a3cfd9ee"
EXPECTED_COMMIT_MARKER = "c13a7b7cb689016a0f50a8e139819e219e6b6d6069d973a136b8e908734e5c01"
EXPECTED_STDOUT_SHA256 = "44fae3c7478b249d1fe50d6578ccf323d5c32218ccce127f5e1959d45eed2294"
EXPECTED_LOCAL_REPORT_SHA256 = "bd89f599026944c060d8717ea2a5ed17907413480c5d628d705f27064c6f5f9e"
EXPECTED_OUTPUT_PAYLOAD_SHA256 = "7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288"
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
MAX_EVIDENCE_BYTES = 64 * 1024
REPORT_SCHEMA = "zenodex/zrpf_firecracker_direct_replay_evidence_check/v2"
EVIDENCE_SCHEMA = "zenodex/zrpf_firecracker_governed_direct_replay_evidence/v2"

_ROOT_FIELDS = {
    "artifacts",
    "candidate_plan",
    "claims",
    "configuration",
    "execution",
    "governed_bindings",
    "historical_observation_basis",
    "non_claims",
    "output",
    "privacy_scan",
    "request",
    "schema",
    "scope",
    "status",
    "retained_local_report_identity",
}
SCOPED_TRUE_CLAIMS = frozenset(
    {
        "direct_local_microvm_replay_reported",
        "governed_runtime_artifact_manifest_integrity_verified",
        "governed_runtime_intent_integrity_verified",
        "publisher_reported_governed_runtime_artifact_bytes_locally_matched",
        "reconstructed_output_protocol_verified",
        "retained_execution_record_integrity_verified",
    }
)
REQUIRED_FALSE_CLAIMS = frozenset(
    {
        "artifact_privacy_scan_passed",
        "cgroup_limits_installed",
        "coherent_repository_rewrite_resistance_verified",
        "complete_build_input_closure_verified",
        "covert_channel_freedom",
        "cross_host_reproducible_build",
        "data_availability_verified",
        "durable_atomic_admission_verified",
        "guest_source_to_binary_verified",
        "hardware_side_channel_resistance",
        "historical_vm_execution_provenance_verified",
        "jailer_execution_verified",
        "microvm_replay_release_authority",
        "production_authority",
        "proofs_regenerated",
        "release_authority",
        "root_owned_launcher_verified",
        "sandbox_escape_resistance",
        "semantic_composition_verified",
        "settlement_authority",
        "witness_privacy",
        "zero_knowledge_privacy",
    }
)
_EXPECTED_CLAIMS = {
    **{name: True for name in SCOPED_TRUE_CLAIMS},
    **{name: False for name in REQUIRED_FALSE_CLAIMS},
}
REPORT_AUTHORITY_FIELDS = tuple(sorted(REQUIRED_FALSE_CLAIMS))
_EXPECTED_PRIVACY_SCAN = {
    "confidential_name_policy_evaluated": False,
    "guest_binary_complete_path_privacy_scan_passed": False,
    "publishable_probe_records_private_path_scan_passed": True,
    "user_or_workspace_paths_present_in_publishable_records": False,
}
_EXPECTED_NON_CLAIMS = (
    "no jailer or root-owned launcher execution",
    "no cgroup or namespace-lifecycle enforcement",
    "no sandbox escape-resistance result",
    "no malicious-host, measured-boot, or hardware-attestation result",
    "no complete build-input closure or independent cross-host reproduction",
    "no complete guest-binary path-privacy claim because generic toolchain builder paths remain",
    "no proof regeneration, semantic ZenoDEX composition, data availability, or durable ledger admission",
    "no release, settlement, production, witness-privacy, zero-knowledge, covert-channel, or hardware-side-channel authority",
    "the publisher reports the direct run; the raw output image is not committed, while the executed configuration, local report, and stdout are retained",
    "static checking establishes retained-record integrity, reconstructed output protocol, and internal binding, not historical VM execution provenance",
    "the pinned checker rejects evidence-only promotion; coherent evidence, checker-policy, test, and CI rewrites require separate review and an external trust anchor",
    "no public confidential-name allowlist or absence claim; private pre-publication policy remains external",
)


@dataclass(frozen=True, slots=True)
class GovernedReferences:
    manifest: Any
    manifest_raw_sha256: str
    profile: dict[str, Any]
    profile_canonical_sha256: str
    intent: Any
    output_payload: bytes
    plan: Any


def build_report(*, evidence_path: Path = EVIDENCE_PATH) -> dict[str, Any]:
    """Validate the static evidence and its governed source records."""

    errors: list[str] = []
    document, evidence_raw_sha256 = _load_evidence(evidence_path, errors)
    references = _load_governed_references(errors)
    if document is not None:
        _validate_identity_and_claims(document, errors)
        if references is not None:
            _validate_governed_bindings(document, references, errors)
            _validate_artifacts(document, references, errors)
            _validate_request(document, references, errors)
            _validate_output(document, references, errors)
            _validate_retained_execution_records(document, references, errors)
        _validate_process_and_retained_report(document, errors)
    return {
        "authority": {name: False for name in REPORT_AUTHORITY_FIELDS},
        "claim_policy_scope": "evidence_only_mutations_against_pinned_checker_policy",
        "errors": errors,
        "evidence_raw_sha256": evidence_raw_sha256,
        "ok": not errors,
        "schema": REPORT_SCHEMA,
        "status": "accepted_static_record_integrity_and_internal_binding_only"
        if not errors
        else "rejected",
        "validation_scope": (
            "static_record_integrity_and_internal_binding_no_historical_execution_provenance"
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, default=EVIDENCE_PATH)
    arguments = parser.parse_args(argv)
    report = build_report(evidence_path=arguments.evidence)
    sys.stdout.buffer.write(runtime.canonical_document_bytes(report))
    return 0 if report["ok"] else 1


def _load_evidence(
    path: Path,
    errors: list[str],
) -> tuple[dict[str, Any] | None, str | None]:
    try:
        raw = runtime.read_bounded_regular(path, maximum=MAX_EVIDENCE_BYTES)
    except (OSError, runtime.RuntimeManifestError):
        _append_once(errors, "evidence_input_rejected")
        return None, None
    raw_sha256 = hashlib.sha256(raw).hexdigest()
    if raw_sha256 != EXPECTED_EVIDENCE_RAW_SHA256:
        _append_once(errors, "evidence_hash_mismatch")
    try:
        value = support.strict_json_loads(raw)
    except (RecursionError, UnicodeDecodeError, json.JSONDecodeError, ValueError):
        _append_once(errors, "evidence_json_rejected")
        return None, raw_sha256
    if type(value) is not dict:
        _append_once(errors, "evidence_root_not_object")
        return None, raw_sha256
    if raw != runtime.canonical_document_bytes(value):
        _append_once(errors, "evidence_noncanonical")
    if set(value) != _ROOT_FIELDS:
        _append_once(errors, "evidence_shape_mismatch")
    return value, raw_sha256


def _load_governed_references(errors: list[str]) -> GovernedReferences | None:
    try:
        manifest_raw = runtime.read_bounded_regular(
            MANIFEST_PATH,
            maximum=runtime.MAX_MANIFEST_BYTES,
        )
        manifest = runtime.parse_runtime_manifest_bytes(
            manifest_raw,
            expected_canonical_sha256=EXPECTED_MANIFEST_CANONICAL_SHA256,
        )
    except (OSError, runtime.RuntimeManifestError):
        _append_once(errors, "governed_manifest_rejected")
        return None
    profile = _load_profile(errors)
    intent = _load_intent(errors)
    output_payload = _load_output_payload(errors)
    if profile is None or intent is None or output_payload is None:
        return None
    profile_sha256 = runtime.canonical_sha256_hex(profile)
    if profile_sha256 != EXPECTED_PROFILE_CANONICAL_SHA256:
        _append_once(errors, "governed_profile_rejected")
    if profile_sha256 != protocol.CANDIDATE_PROFILE_CANONICAL_SHA256_V1.hex():
        _append_once(errors, "governed_profile_rejected")
    if profile_sha256 != runtime.PROFILE_CANONICAL_SHA256:
        _append_once(errors, "governed_profile_rejected")
    try:
        plan = candidate_plan.compile_candidate_plan(manifest, intent)
    except candidate_plan.CandidatePlanError:
        _append_once(errors, "governed_candidate_plan_rejected")
        return None
    if (
        plan.candidate_plan_id != EXPECTED_CANDIDATE_PLAN_ID
        or hashlib.sha256(plan.canonical_bytes()).hexdigest()
        != EXPECTED_CANDIDATE_PLAN_CANONICAL_SHA256
    ):
        _append_once(errors, "governed_candidate_plan_rejected")
    return GovernedReferences(
        manifest=manifest,
        manifest_raw_sha256=hashlib.sha256(manifest_raw).hexdigest(),
        profile=profile,
        profile_canonical_sha256=profile_sha256,
        intent=intent,
        output_payload=output_payload,
        plan=plan,
    )


def _load_profile(errors: list[str]) -> dict[str, Any] | None:
    try:
        raw = runtime.read_bounded_regular(
            PROFILE_PATH,
            maximum=profile_checker.MAX_PROFILE_BYTES,
        )
        value = support.strict_json_loads(raw)
    except (
        OSError,
        RecursionError,
        UnicodeDecodeError,
        ValueError,
        runtime.RuntimeManifestError,
    ):
        _append_once(errors, "governed_profile_rejected")
        return None
    if type(value) is not dict or raw != runtime.canonical_document_bytes(value):
        _append_once(errors, "governed_profile_rejected")
        return None
    return value


def _load_intent(errors: list[str]) -> Any | None:
    try:
        raw = runtime.read_bounded_regular(INTENT_PATH, maximum=runtime.PAYLOAD_CAP_BYTES)
        return candidate_plan.parse_replay_intent_bytes(raw)
    except (
        OSError,
        candidate_plan.CandidatePlanError,
        runtime.RuntimeManifestError,
    ):
        _append_once(errors, "governed_intent_rejected")
        return None


def _load_output_payload(errors: list[str]) -> bytes | None:
    try:
        raw = runtime.read_bounded_regular(
            OUTPUT_PAYLOAD_PATH,
            maximum=protocol.OUTPUT_PAYLOAD_CAP_BYTES_V1,
        )
        value = support.strict_json_loads(raw)
        canonical = (
            json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
        ).encode("ascii")
    except (
        OSError,
        RecursionError,
        UnicodeDecodeError,
        ValueError,
        runtime.RuntimeManifestError,
    ):
        _append_once(errors, "governed_output_payload_rejected")
        return None
    if (
        type(value) is not dict
        or raw != canonical
        or len(raw) != 5_920
        or hashlib.sha256(raw).hexdigest() != EXPECTED_OUTPUT_PAYLOAD_SHA256
    ):
        _append_once(errors, "governed_output_payload_rejected")
        return None
    return raw


def _validate_identity_and_claims(document: dict[str, Any], errors: list[str]) -> None:
    identity = {
        "schema": EVIDENCE_SCHEMA,
        "scope": (
            "publisher_reported_direct_unjailed_firecracker_governed_artifact_and_"
            "intent_local_replay"
        ),
        "status": (
            "governed_direct_local_replay_report_recorded_without_launcher_or_settlement_authority"
        ),
    }
    if any(
        type(document.get(key)) is not str or document.get(key) != value
        for key, value in identity.items()
    ):
        _append_once(errors, "evidence_identity_mismatch")
    if not _exact_boolean_map(document.get("claims"), _EXPECTED_CLAIMS):
        _append_once(errors, "claim_boundary_mismatch")
    if document.get("historical_observation_basis") != (
        "publisher_reported_retained_local_report_identity_only"
    ):
        _append_once(errors, "historical_observation_basis_mismatch")
    if not _exact_boolean_map(document.get("privacy_scan"), _EXPECTED_PRIVACY_SCAN):
        _append_once(errors, "privacy_boundary_mismatch")
    non_claims = document.get("non_claims")
    if type(non_claims) is not list or tuple(non_claims) != _EXPECTED_NON_CLAIMS:
        _append_once(errors, "non_claims_mismatch")


def _validate_governed_bindings(
    document: dict[str, Any],
    references: GovernedReferences,
    errors: list[str],
) -> None:
    bindings = document.get("governed_bindings")
    expected = {
        "artifact_set_id": references.manifest.artifact_set_id,
        "input_bundle_root": references.manifest.input_image.input_bundle_root,
        "profile_canonical_sha256": references.profile_canonical_sha256,
        "replay_intent_sha256": references.intent.intent_sha256,
        "runtime_manifest_canonical_sha256": references.manifest.canonical_sha256,
        "runtime_manifest_raw_sha256": references.manifest_raw_sha256,
    }
    if not _exact_string_map(bindings, expected):
        _append_once(errors, "governed_binding_mismatch")
    candidate = document.get("candidate_plan")
    if not _exact_string_map(
        candidate,
        {
            "candidate_plan_id": references.plan.candidate_plan_id,
            "canonical_sha256": hashlib.sha256(references.plan.canonical_bytes()).hexdigest(),
        },
    ):
        _append_once(errors, "candidate_plan_binding_mismatch")
    configuration = document.get("configuration")
    expected_configuration = {
        "canonical_sha256": EXPECTED_EXECUTED_CONFIG_SHA256,
        "drive_count": 3,
        "memory_mib": 256,
        "no_api": True,
        "retained_path": (
            "evidence/zrpf-v3-retained-structural-replay-v1/"
            "firecracker-direct-v2/config.json"
        ),
        "smt": False,
        "vcpu_count": 1,
    }
    if not _exact_typed_map(configuration, expected_configuration):
        _append_once(errors, "configuration_binding_mismatch")


def _validate_artifacts(
    document: dict[str, Any],
    references: GovernedReferences,
    errors: list[str],
) -> None:
    profile_artifacts = references.profile.get("artifacts")
    release_binary = (
        profile_artifacts.get("firecracker_release_binary")
        if type(profile_artifacts) is dict
        else None
    )
    expected = {
        "firecracker": _artifact_summary(release_binary),
        "input_image": _artifact_identity(references.manifest.input_image.artifact),
        "kernel": _artifact_identity(references.manifest.guest_kernel.artifact),
        "rootfs": _artifact_identity(references.manifest.rootfs.artifact),
    }
    artifacts = document.get("artifacts")
    if type(artifacts) is not dict or set(artifacts) != set(expected):
        _append_once(errors, "artifact_binding_mismatch")
        return
    if any(
        not _exact_typed_map(artifacts.get(name), identity) for name, identity in expected.items()
    ):
        _append_once(errors, "artifact_binding_mismatch")


def _validate_request(
    document: dict[str, Any],
    references: GovernedReferences,
    errors: list[str],
) -> None:
    request = document.get("request")
    reconstructed = _reconstruct_request(request, references)
    if type(request) is not dict or reconstructed is None:
        _append_once(errors, "request_binding_mismatch")
        return
    expected_request, encoded = reconstructed
    nonce = expected_request.run_nonce_256
    expected = {
        "input_drive_sha256": references.intent.input_drive_sha256,
        "output_payload_cap_bytes": protocol.OUTPUT_PAYLOAD_CAP_BYTES_V1,
        "output_size_bytes": protocol.OUTPUT_BYTES_V1,
        "profile_sha256": references.profile_canonical_sha256,
        "replay_intent_sha256": references.intent.intent_sha256,
        "reserved_bytes_zero": True,
        "run_nonce_256": nonce.hex(),
        "runtime_manifest_sha256": references.manifest.canonical_sha256,
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "size_bytes": protocol.REQUEST_BYTES_V1,
    }
    if not _exact_typed_map(request, expected):
        _append_once(errors, "request_binding_mismatch")
    if expected_request.sha256.hex() != EXPECTED_REQUEST_SHA256:
        _append_once(errors, "request_binding_mismatch")


def _validate_output(
    document: dict[str, Any],
    references: GovernedReferences,
    errors: list[str],
) -> None:
    output = document.get("output")
    reconstructed_request = _reconstruct_request(document.get("request"), references)
    if reconstructed_request is None:
        _append_once(errors, "output_reconstruction_failed")
        return
    expected_request, _ = reconstructed_request
    try:
        reconstructed_output = protocol.build_committed_output(
            expected_request,
            observed_input_drive_sha256=expected_request.input_drive_sha256,
            payload=references.output_payload,
        )
        reconstructed_payload = protocol.validate_committed_output(
            reconstructed_output,
            expected_request,
        )
    except protocol.FirecrackerProtocolReject:
        _append_once(errors, "output_reconstruction_failed")
        return
    reconstructed_marker = reconstructed_output[-protocol.OUTPUT_COMMIT_BYTES_V1 :].hex()
    if (
        reconstructed_payload != references.output_payload
        or hashlib.sha256(reconstructed_output).hexdigest() != EXPECTED_OUTPUT_SHA256
        or reconstructed_marker != EXPECTED_COMMIT_MARKER
    ):
        _append_once(errors, "output_reconstruction_failed")
    trailing_count = (
        protocol.OUTPUT_BYTES_V1
        - protocol.OUTPUT_HEADER_BYTES_V1
        - references.intent.expected_output_payload_size_bytes
        - protocol.OUTPUT_COMMIT_BYTES_V1
    )
    expected = {
        "commit_marker_actual": EXPECTED_COMMIT_MARKER,
        "commit_marker_expected": EXPECTED_COMMIT_MARKER,
        "commit_marker_matches": True,
        "payload_matches_governed_intent": True,
        "payload_sha256": references.intent.expected_output_payload_sha256,
        "payload_size_bytes": references.intent.expected_output_payload_size_bytes,
        "sha256": EXPECTED_OUTPUT_SHA256,
        "size_bytes": protocol.OUTPUT_BYTES_V1,
        "stable_read_after_exit": True,
        "trailing_zero_bytes_count": trailing_count,
        "trailing_zero_region_all_zero": True,
    }
    if not _exact_typed_map(output, expected):
        _append_once(errors, "output_fact_mismatch")


def _reconstruct_request(
    value: Any,
    references: GovernedReferences,
) -> tuple[Any, bytes] | None:
    if type(value) is not dict:
        return None
    try:
        nonce = bytes.fromhex(_required_string(value, "run_nonce_256"))
        request = protocol.FirecrackerRequestV1.validated(
            run_nonce_256=nonce,
            runtime_manifest_sha256=bytes.fromhex(references.manifest.canonical_sha256),
            input_drive_sha256=bytes.fromhex(references.intent.input_drive_sha256),
            replay_intent_sha256=bytes.fromhex(references.intent.intent_sha256),
        )
        encoded = request.encode()
        protocol.decode_request(encoded)
    except (KeyError, TypeError, ValueError, protocol.FirecrackerProtocolReject):
        return None
    return request, encoded


def _validate_retained_execution_records(
    document: dict[str, Any],
    references: GovernedReferences,
    errors: list[str],
) -> None:
    try:
        config_raw = runtime.read_bounded_regular(EXECUTED_CONFIG_PATH, maximum=64 * 1024)
        config = support.strict_json_loads(config_raw)
    except (
        OSError,
        RecursionError,
        UnicodeDecodeError,
        ValueError,
        runtime.RuntimeManifestError,
    ):
        _append_once(errors, "retained_config_rejected")
    else:
        expected_config = references.plan.to_document()["microvm_configuration_template"]
        expected_config["boot-source"]["kernel_image_path"] = "kernel"
        expected_config["drives"][0]["path_on_host"] = "rootfs.squashfs"
        expected_config["drives"][1]["path_on_host"] = "input.squashfs"
        expected_config["drives"][2]["path_on_host"] = "output.raw"
        if (
            type(config) is not dict
            or config != expected_config
            or config_raw != runtime.canonical_document_bytes(config)
            or hashlib.sha256(config_raw).hexdigest() != EXPECTED_EXECUTED_CONFIG_SHA256
        ):
            _append_once(errors, "retained_config_rejected")

    try:
        stdout = runtime.read_bounded_regular(FIRECRACKER_STDOUT_PATH, maximum=64 * 1024)
    except (OSError, runtime.RuntimeManifestError):
        _append_once(errors, "retained_stdout_rejected")
    else:
        if len(stdout) != 1_095 or hashlib.sha256(stdout).hexdigest() != EXPECTED_STDOUT_SHA256:
            _append_once(errors, "retained_stdout_rejected")

    try:
        report_raw = runtime.read_bounded_regular(LOCAL_REPORT_PATH, maximum=64 * 1024)
        report = support.strict_json_loads(report_raw)
    except (
        OSError,
        RecursionError,
        UnicodeDecodeError,
        ValueError,
        runtime.RuntimeManifestError,
    ):
        _append_once(errors, "retained_local_report_rejected")
        return
    expected_report = _expected_retained_report(document, references)
    if (
        type(report) is not dict
        or report != expected_report
        or report_raw != runtime.canonical_document_bytes(report)
        or hashlib.sha256(report_raw).hexdigest() != EXPECTED_LOCAL_REPORT_SHA256
    ):
        _append_once(errors, "retained_local_report_rejected")


def _expected_retained_report(
    document: dict[str, Any],
    references: GovernedReferences,
) -> dict[str, Any]:
    artifacts = document.get("artifacts")
    execution = document.get("execution")
    output = document.get("output")
    request = document.get("request")
    if (
        type(artifacts) is not dict
        or type(execution) is not dict
        or type(output) is not dict
        or type(request) is not dict
    ):
        return {}
    local_artifacts = {
        "firecracker": artifacts.get("firecracker"),
        "input": artifacts.get("input_image"),
        "kernel": artifacts.get("kernel"),
        "rootfs": artifacts.get("rootfs"),
    }
    return {
        "artifacts_after": local_artifacts,
        "artifacts_before": local_artifacts,
        "candidate_plan_canonical_sha256": hashlib.sha256(
            references.plan.canonical_bytes()
        ).hexdigest(),
        "candidate_plan_id": references.plan.candidate_plan_id,
        "configuration_sha256": EXPECTED_EXECUTED_CONFIG_SHA256,
        "elapsed_monotonic_ns": execution.get("elapsed_monotonic_ns"),
        "exit_code": execution.get("exit_code"),
        "manifest_canonical_sha256": references.manifest.canonical_sha256,
        "manifest_raw_sha256": references.manifest_raw_sha256,
        "output_commit_marker": output.get("commit_marker_actual"),
        "output_payload_sha256": output.get("payload_sha256"),
        "output_payload_size_bytes": output.get("payload_size_bytes"),
        "output_sha256": output.get("sha256"),
        "output_size_bytes": output.get("size_bytes"),
        "profile_canonical_sha256": references.profile_canonical_sha256,
        "request_sha256": request.get("sha256"),
        "request_size_bytes": request.get("size_bytes"),
        "run_nonce_256": request.get("run_nonce_256"),
        "schema": "zenodex/zrpf_firecracker_unjailed_local_report/v2",
        "stable_output_read_after_exit": output.get("stable_read_after_exit"),
        "stderr_sha256": execution.get("stderr_sha256"),
        "stderr_size_bytes": execution.get("stderr_size_bytes"),
        "stdout_sha256": execution.get("stdout_sha256"),
        "stdout_size_bytes": execution.get("stdout_size_bytes"),
        "timed_out": execution.get("timed_out"),
    }


def _validate_process_and_retained_report(
    document: dict[str, Any],
    errors: list[str],
) -> None:
    execution = document.get("execution")
    expected_execution = {
        "exit_code": 0,
        "stderr_sha256": EMPTY_SHA256,
        "stderr_size_bytes": 0,
        "stdout_sha256": EXPECTED_STDOUT_SHA256,
        "stdout_size_bytes": 1_095,
        "stdout_retained_path": (
            "evidence/zrpf-v3-retained-structural-replay-v1/"
            "firecracker-direct-v2/firecracker.stdout"
        ),
        "timed_out": False,
    }
    if not _exact_subset(execution, expected_execution):
        _append_once(errors, "process_fact_mismatch")
    if type(execution) is not dict or not _positive_int(execution.get("elapsed_monotonic_ns")):
        _append_once(errors, "process_fact_mismatch")
    retained = document.get("retained_local_report_identity")
    if not _exact_typed_map(
        retained,
        {
            "canonical_sha256": EXPECTED_LOCAL_REPORT_SHA256,
            "path": (
                "evidence/zrpf-v3-retained-structural-replay-v1/"
                "firecracker-direct-v2/local-report.json"
            ),
            "publicly_available": True,
            "size_bytes": 2_691,
        },
    ):
        _append_once(errors, "retained_report_binding_mismatch")


def _artifact_identity(value: Any) -> dict[str, Any]:
    return {"sha256": value.sha256, "size_bytes": value.size_bytes}


def _artifact_summary(value: Any) -> dict[str, Any]:
    if type(value) is not dict:
        return {}
    return {"sha256": value.get("sha256"), "size_bytes": value.get("size_bytes")}


def _exact_boolean_map(value: Any, expected: dict[str, bool]) -> bool:
    if type(value) is not dict or set(value) != set(expected):
        return False
    return all(
        type(value[name]) is bool and value[name] is wanted for name, wanted in expected.items()
    )


def _exact_string_map(value: Any, expected: dict[str, str]) -> bool:
    if type(value) is not dict or set(value) != set(expected):
        return False
    return all(
        type(value[name]) is str and value[name] == wanted for name, wanted in expected.items()
    )


def _exact_typed_map(value: Any, expected: dict[str, Any]) -> bool:
    if type(value) is not dict or set(value) != set(expected):
        return False
    return all(
        type(value[name]) is type(wanted) and value[name] == wanted
        for name, wanted in expected.items()
    )


def _exact_subset(value: Any, expected: dict[str, Any]) -> bool:
    if type(value) is not dict:
        return False
    expected_keys = {*expected, "elapsed_monotonic_ns"}
    if set(value) != expected_keys:
        return False
    return all(
        type(value[name]) is type(wanted) and value[name] == wanted
        for name, wanted in expected.items()
    )


def _required_string(value: dict[str, Any], name: str) -> str:
    selected = value[name]
    if type(selected) is not str:
        raise TypeError(name)
    return selected


def _positive_int(value: Any) -> bool:
    return type(value) is int and value > 0


def _append_once(errors: list[str], code: str) -> None:
    if code not in errors:
        errors.append(code)


if __name__ == "__main__":
    raise SystemExit(main())
