#!/usr/bin/env python3
"""Validate the retained V1 live-replay record without replaying it."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import check_risc0_recursive_live_replay as live
from tools import check_risc0_recursive_rebuild_evidence as rebuild

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = ROOT / "docs/research/RISC0_RECURSIVE_V1_LIVE_REPLAY_EVIDENCE_20260712.json"
REPORT_SCHEMA = "zenodex/risc0_recursive_v1_live_replay_evidence_check/v1"
ACCEPTED_STATUS = "retained_same_host_v1_live_replay_record_accepted"
EXPECTED_EVIDENCE_CANONICAL_SHA256 = (
    "8038750bfd9a9c249e6a86703265458d9cf59dc4d94f530b9fcf22ec92245858"
)
MAX_EVIDENCE_BYTES = 64 * 1024

TRUE_FIELDS = frozenset(
    {
        "ambient_dev_mode_enabled_values_rejected",
        "ambient_dev_mode_zero_parity_verified",
        "artifact_evidence_verified",
        "exact_seal_mutation_rejected",
        "ok",
        "positive_request_verified",
        "same_host_pinned_v1_verifier_live_replay",
    }
)
FALSE_FIELDS = frozenset(
    {
        "covert_channel_freedom",
        "data_availability_verified",
        "durable_atomic_admission_verified",
        "hardware_side_channel_resistance",
        "historical_execution_provenance_verified",
        "network_isolation_verified",
        "production_authority",
        "proofs_regenerated",
        "release_authority",
        "sandbox_escape_controls_passed",
        "semantic_composition_verified",
        "settlement_authority",
        "zero_knowledge_privacy",
    }
)
TOP_LEVEL_KEYS = frozenset(
    {
        *TRUE_FIELDS,
        *FALSE_FIELDS,
        "artifact_evidence",
        "checker_source_closure",
        "claim_scope",
        "error_codes",
        "errors",
        "evidence_basis",
        "live_runs",
        "runtime_limits",
        "runtime_transports",
        "schema",
        "status",
        "verifier_identity",
    }
)


class RecordError(ValueError):
    """Stable retained-record rejection."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code


def _reject(code: str, detail: str) -> RecordError:
    return RecordError(code, detail)


def _canonical_sha256(value: object) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _mapping(value: object, *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise _reject("SCHEMA", f"{label} must be an object")
    return value


def _validate_boolean_fields(document: Mapping[str, Any]) -> None:
    for field in TRUE_FIELDS:
        if document.get(field) is not True:
            raise _reject("CLAIM", f"{field} must be true")
    for field in FALSE_FIELDS:
        if document.get(field) is not False:
            raise _reject("NON_CLAIM", f"{field} must be false")


def _expected_outcome(stdout_sha256: str, stdout_size_bytes: int) -> dict[str, object]:
    return {
        "exit_code": 0,
        "stderr_sha256": live.support.ZERO_SHA256,
        "stderr_size_bytes": 0,
        "stdout_sha256": stdout_sha256,
        "stdout_size_bytes": stdout_size_bytes,
    }


def _validate_outcome(
    raw: object,
    *,
    environment_profile: str,
    stdout_sha256: str,
    stdout_size_bytes: int,
    label: str,
) -> None:
    outcome = _mapping(raw, label=label)
    expected = {
        "environment_profile": environment_profile,
        **_expected_outcome(stdout_sha256, stdout_size_bytes),
    }
    if dict(outcome) != expected:
        raise _reject("LIVE_RUN", label)


def _validate_live_runs(document: Mapping[str, Any]) -> None:
    runs = _mapping(document.get("live_runs"), label="live_runs")
    if set(runs) != {
        "ambient_dev_mode_disabled_parity",
        "ambient_dev_mode_enabled_rejections",
        "malformed_exact_seal_mutation",
        "positive",
    }:
        raise _reject("LIVE_RUN", "unexpected live-run keys")
    _validate_outcome(
        runs["positive"],
        environment_profile=live.support.ENVIRONMENT_PROFILE_ABSENT,
        stdout_sha256="af2a660f10f3b4eb01811cb4215f01546679618296dcd369e3f6d542bfae5c8a",
        stdout_size_bytes=1_305,
        label="positive",
    )
    _validate_outcome(
        runs["malformed_exact_seal_mutation"],
        environment_profile=live.support.ENVIRONMENT_PROFILE_ABSENT,
        stdout_sha256="e48455659dacb176d08ef6a70efcbb7aa9a4a268f5d7d6d44b696c7ffef386e0",
        stdout_size_bytes=91,
        label="malformed_exact_seal_mutation",
    )
    disabled = _mapping(
        runs["ambient_dev_mode_disabled_parity"],
        label="ambient_dev_mode_disabled_parity",
    )
    if set(disabled) != set(live.support.DEV_MODE_DISABLED_VALUES):
        raise _reject("LIVE_RUN", "disabled dev-mode values")
    for value in live.support.DEV_MODE_DISABLED_VALUES:
        _validate_outcome(
            disabled[value],
            environment_profile=f"minimal_environment_risc0_dev_mode_{value}_v1",
            stdout_sha256="af2a660f10f3b4eb01811cb4215f01546679618296dcd369e3f6d542bfae5c8a",
            stdout_size_bytes=1_305,
            label=f"ambient_dev_mode_disabled_parity.{value}",
        )
    enabled = _mapping(
        runs["ambient_dev_mode_enabled_rejections"],
        label="ambient_dev_mode_enabled_rejections",
    )
    if set(enabled) != set(live.support.DEV_MODE_ENABLED_VALUES):
        raise _reject("LIVE_RUN", "enabled dev-mode values")
    for value in live.support.DEV_MODE_ENABLED_VALUES:
        _validate_outcome(
            enabled[value],
            environment_profile=f"minimal_environment_risc0_dev_mode_{value}_v1",
            stdout_sha256="2430bc5b247da01f02b5238f3f8393bf45a7ed53b55a4388885e604bac9008e4",
            stdout_size_bytes=77,
            label=f"ambient_dev_mode_enabled_rejections.{value}",
        )


def _validate_artifact_evidence(
    document: Mapping[str, Any],
    reference: Mapping[str, Any],
) -> None:
    evidence = _mapping(document.get("artifact_evidence"), label="artifact_evidence")
    expected_pairs = {
        "artifact_report_sha256": reference["artifact_report"]["sha256"],
        "malformed_reject_transcript_sha256": reference["malformed_proof_reject"][
            "reject_transcript"
        ]["sha256"],
        "malformed_root_proof_sha256": reference["malformed_proof_reject"][
            "mutated_root_proof"
        ]["sha256"],
        "malformed_verify_request_sha256": reference["malformed_proof_reject"][
            "verify_request"
        ]["sha256"],
        "positive_verify_request_sha256": reference["positive_verify_request"]["sha256"],
        "reference_canonical_sha256": rebuild.EXPECTED_REFERENCE_CANONICAL_SHA256,
        "root_proof_sha256": reference["root_proof"]["sha256"],
        "source_compile_root_sha256": reference["source_compile"]["root_sha256"],
        "static_verifier_sha256": reference["static_verifier"]["sha256"],
        "verified_transcript_sha256": reference["verified_transcript"]["sha256"],
        "workspace_archive_sha256": reference["workspace_archive"]["sha256"],
        "workspace_archive_source_root_sha256": reference["source_compile"]["root_sha256"],
    }
    for field, expected in expected_pairs.items():
        if evidence.get(field) != expected:
            raise _reject("ARTIFACT_EVIDENCE", field)
    for field in (
        "build_command_authenticated",
        "build_environment_authenticated",
        "clean_target_verified",
        "cross_environment_reproducibility",
        "independent_rebuild",
        "production_ready",
        "public_claim_allowed",
        "public_replay",
        "reproducible_release",
        "same_host_clean_rebuild",
        "settlement_authorization",
        "source_archive_provenance_authenticated",
        "toolchain_execution_authenticated",
    ):
        if evidence.get(field) is not False:
            raise _reject("ARTIFACT_NON_CLAIM", field)
    if evidence.get("ok") is not True or evidence.get("pinned_rebuild_artifact_match") is not True:
        raise _reject("ARTIFACT_EVIDENCE", "artifact checker did not accept")


def validate_evidence(
    document: object,
    *,
    repository_root: Path = ROOT,
) -> Mapping[str, Any]:
    evidence = _mapping(document, label="evidence")
    if set(evidence) != TOP_LEVEL_KEYS:
        raise _reject("SCHEMA", "top-level keys mismatch")
    actual_digest = _canonical_sha256(evidence)
    if actual_digest != EXPECTED_EVIDENCE_CANONICAL_SHA256:
        raise _reject("EVIDENCE_DIGEST", actual_digest)
    if evidence.get("schema") != live.REPORT_SCHEMA:
        raise _reject("SCHEMA", "live report schema")
    if evidence.get("status") != live.ACCEPTED_STATUS:
        raise _reject("STATUS", "live report did not accept")
    if evidence.get("claim_scope") != live.CLAIM_SCOPE:
        raise _reject("CLAIM_SCOPE", "unexpected claim scope")
    if evidence.get("error_codes") != [] or evidence.get("errors") != []:
        raise _reject("STATUS", "accepted record contains errors")
    _validate_boolean_fields(evidence)
    if evidence.get("checker_source_closure") != live.support.checker_source_closure(
        repository_root
    ):
        raise _reject("CHECKER_SOURCE", "source closure mismatch")
    if evidence.get("runtime_limits") != {
        "input_bytes": live.support.MAX_RUNTIME_INPUT_BYTES,
        "output_bytes": live.support.MAX_RUNTIME_OUTPUT_BYTES,
        "timeout_seconds": live.support.RUNTIME_TIMEOUT_SECONDS,
    }:
        raise _reject("RUNTIME_LIMITS", "runtime limits mismatch")
    if evidence.get("runtime_transports") != {
        "executable": "linux_memfd_full_seals_v1",
        "stdin": live.support.replay_process.STDIN_TRANSPORT,
    }:
        raise _reject("RUNTIME_TRANSPORTS", "runtime transports mismatch")
    reference = live.support.authenticated_reference(
        repository_root / "config/proof_profiles/risc0_recursive_rebuild_reference.json"
    )
    if evidence.get("verifier_identity") != {
        "sha256": reference["static_verifier"]["sha256"],
        "size_bytes": reference["static_verifier"]["size_bytes"],
        "transport": "linux_memfd_full_seals_v1",
    }:
        raise _reject("VERIFIER_IDENTITY", "verifier identity mismatch")
    _validate_live_runs(evidence)
    _validate_artifact_evidence(evidence, reference)
    return evidence


def check_retained_evidence(
    path: Path | None = None,
    *,
    repository_root: Path = ROOT,
) -> dict[str, Any]:
    report = {
        "schema": REPORT_SCHEMA,
        "record_integrity_verified": False,
        "live_replay_execution_performed_now": False,
        "historical_execution_provenance_verified": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    try:
        evidence_path = (
            repository_root
            / "docs/research/RISC0_RECURSIVE_V1_LIVE_REPLAY_EVIDENCE_20260712.json"
            if path is None
            else path
        )
        raw = rebuild._read_regular_path(
            evidence_path,
            label="live_replay_evidence",
            max_bytes=MAX_EVIDENCE_BYTES,
        )
        document = rebuild._parse_json(raw.raw, label="LIVE_REPLAY_EVIDENCE")
        validate_evidence(document, repository_root=repository_root)
    except (rebuild.EvidenceError, live.support.LiveReplayError, RecordError) as exc:
        code = (
            exc.code
            if isinstance(exc, (live.support.LiveReplayError, RecordError))
            else "EVIDENCE_READ"
        )
        return {
            **report,
            "error_codes": [code],
            "errors": [str(exc)],
            "ok": False,
            "status": "rejected",
        }
    return {
        **report,
        "canonical_evidence_sha256": EXPECTED_EVIDENCE_CANONICAL_SHA256,
        "error_codes": [],
        "errors": [],
        "ok": True,
        "record_integrity_verified": True,
        "status": ACCEPTED_STATUS,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, default=ROOT)
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = check_retained_evidence(
        args.evidence,
        repository_root=args.repository_root,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print(
            f"ok: {ACCEPTED_STATUS}; static record integrity only; "
            "historical provenance and authority claims false"
        )
    else:
        for error in report["errors"]:
            print(error, file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
