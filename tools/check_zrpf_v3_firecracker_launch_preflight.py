#!/usr/bin/env python3
"""Compile a non-executable ZRPF Firecracker candidate plan and report."""

from __future__ import annotations

import argparse
import importlib
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from tools.zrpf_v3_firecracker_candidate_plan import (
        ValidatedReplayIntentV1,
    )
    from tools.zrpf_v3_firecracker_runtime_manifest import (
        PinnedRuntimeManifestV1,
    )

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""

artifact_set = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_artifact_set")
candidate_plan = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_candidate_plan")
runtime_manifest = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_firecracker_runtime_manifest")

REPORT_SCHEMA = "zenodex/zrpf_firecracker_launch_preflight_report/v1"
_AUTHORITY_FIELDS = (
    "guest_boot_verified",
    "microvm_replay_verified",
    "production_authority",
    "release_authority",
    "root_launcher_ready",
    "runtime_artifacts_authorized_for_path_reuse",
    "sandbox_escape_resistance",
    "settlement_authority",
    "witness_privacy",
    "zero_knowledge_privacy",
)


def build_report(
    *,
    manifest_path: Path,
    expected_manifest_sha256: str,
    intent_path: Path,
    artifact_directory: Path | None,
) -> dict[str, Any]:
    """Build a canonicalizable report without executing privileged operations."""

    try:
        manifest = runtime_manifest.load_runtime_manifest(
            manifest_path,
            expected_canonical_sha256=expected_manifest_sha256,
        )
    except runtime_manifest.RuntimeManifestError as exc:
        return _rejected_report(exc.code)
    try:
        intent = _load_intent(intent_path)
    except candidate_plan.CandidatePlanError as exc:
        return _rejected_report(exc.code, manifest=manifest)
    try:
        bound = (
            None
            if artifact_directory is None
            else artifact_set.verify_artifact_set(artifact_directory, manifest)
        )
    except artifact_set.ArtifactSetError as exc:
        return _rejected_report(exc.code, manifest=manifest)
    try:
        plan = candidate_plan.compile_candidate_plan(
            manifest,
            intent,
            locally_bound_artifacts=bound,
        )
    except candidate_plan.CandidatePlanError as exc:
        return _rejected_report(exc.code, manifest=manifest)
    plan_document = plan.to_document()
    artifact_status = plan_document["artifact_bytes_status"]
    return {
        "artifact_bytes_status": artifact_status,
        "authority": {name: False for name in _AUTHORITY_FIELDS},
        "candidate_plan": plan_document,
        "candidate_plan_compiled": True,
        "candidate_profile_binding_valid": True,
        "decision": (
            "candidate_plan_compiled_artifacts_locally_bound"
            if artifact_status == "exact_match"
            else "candidate_plan_compiled_artifacts_unavailable"
        ),
        "errors": [],
        "executable_prerequisites_satisfied": False,
        "microvm_replay_verified": False,
        "manifest_anchor_scope": "caller_supplied_preflight_only",
        "root_launcher_ready": False,
        "runtime_manifest_canonical_sha256": manifest.canonical_sha256,
        "runtime_manifest_integrity_valid": True,
        "schema": REPORT_SCHEMA,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--intent", type=Path, required=True)
    parser.add_argument("--artifact-dir", type=Path)
    parser.add_argument("--require-executable", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        report = build_report(
            manifest_path=arguments.manifest,
            expected_manifest_sha256=arguments.expected_manifest_sha256,
            intent_path=arguments.intent,
            artifact_directory=arguments.artifact_dir,
        )
    except (OSError, RecursionError, ValueError):
        report = _rejected_report("preflight_internal_boundary_rejected")
    sys.stdout.buffer.write(runtime_manifest.canonical_document_bytes(report))
    if not report["candidate_plan_compiled"]:
        return 1
    if arguments.require_executable:
        return 1
    return 0


def _load_intent(path: Path) -> ValidatedReplayIntentV1:
    try:
        raw = runtime_manifest.read_bounded_regular(
            path,
            maximum=runtime_manifest.PAYLOAD_CAP_BYTES,
        )
    except runtime_manifest.RuntimeManifestError as exc:
        raise candidate_plan.CandidatePlanError("candidate_intent_input_rejected") from exc
    return candidate_plan.parse_replay_intent_bytes(raw)


def _rejected_report(
    code: str,
    *,
    manifest: PinnedRuntimeManifestV1 | None = None,
) -> dict[str, Any]:
    manifest_valid = manifest is not None
    return {
        "artifact_bytes_status": "rejected",
        "authority": {name: False for name in _AUTHORITY_FIELDS},
        "candidate_plan": None,
        "candidate_plan_compiled": False,
        "candidate_profile_binding_valid": manifest_valid,
        "decision": "candidate_plan_rejected",
        "errors": [code],
        "executable_prerequisites_satisfied": False,
        "microvm_replay_verified": False,
        "manifest_anchor_scope": "caller_supplied_preflight_only",
        "root_launcher_ready": False,
        "runtime_manifest_canonical_sha256": (
            manifest.canonical_sha256 if manifest is not None else None
        ),
        "runtime_manifest_integrity_valid": manifest_valid,
        "schema": REPORT_SCHEMA,
    }


if __name__ == "__main__":
    raise SystemExit(main())
