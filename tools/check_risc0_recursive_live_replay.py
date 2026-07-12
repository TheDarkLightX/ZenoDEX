#!/usr/bin/env python3
"""Execute the exact pinned V1 verifier against governed retained requests."""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools import check_risc0_recursive_rebuild_evidence as rebuild
from tools import risc0_recursive_live_replay_support as support

REPORT_SCHEMA = "zenodex/risc0_recursive_v1_live_replay_check/v1"
ACCEPTED_STATUS = "same_host_pinned_v1_verifier_live_replay_accepted"
CLAIM_SCOPE = "same_host_pinned_v1_retained_receipt_replay_without_ledger_authority"
def _base_report() -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "claim_scope": CLAIM_SCOPE,
        "evidence_basis": (
            "byte_pinned_rebuild_evidence_plus_sealed_exact_verifier_live_execution"
        ),
        "artifact_evidence_verified": False,
        "same_host_pinned_v1_verifier_live_replay": False,
        "positive_request_verified": False,
        "ambient_dev_mode_zero_parity_verified": False,
        "ambient_dev_mode_enabled_values_rejected": False,
        "exact_seal_mutation_rejected": False,
        "historical_execution_provenance_verified": False,
        "network_isolation_verified": False,
        "sandbox_escape_controls_passed": False,
        "proofs_regenerated": False,
        "semantic_composition_verified": False,
        "data_availability_verified": False,
        "durable_atomic_admission_verified": False,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
        "zero_knowledge_privacy": False,
        "hardware_side_channel_resistance": False,
        "covert_channel_freedom": False,
    }


def _failure(report: dict[str, Any], error: support.LiveReplayError) -> dict[str, Any]:
    return {
        **report,
        "error_codes": [error.code],
        "errors": [str(error)],
        "ok": False,
        "status": "rejected",
    }


def check_risc0_recursive_live_replay(
    paths: rebuild.RebuildEvidencePaths,
    *,
    runtime_directory: Path,
) -> dict[str, Any]:
    """Authenticate all artifacts, then execute every governed replay control."""

    report = _base_report()
    artifact_report = rebuild.check_risc0_recursive_rebuild_evidence(paths)
    report["artifact_evidence"] = artifact_report
    if artifact_report.get("ok") is not True:
        rejected = support.reject("ARTIFACT_EVIDENCE", "pinned rebuild evidence rejected")
        return _failure(report, rejected)
    report["artifact_evidence_verified"] = True
    try:
        support.require_unprivileged_linux()
        reference = support.authenticated_reference()
        inputs = support.capture_inputs(paths, artifact_report, reference)
        execution = support.execute_controls(
            paths,
            artifact_report,
            reference,
            inputs,
            runtime_directory,
        )
        checker_source_closure = support.checker_source_closure()
    except (support.LiveReplayError, RuntimeError, OSError) as exc:
        error = (
            exc
            if isinstance(exc, support.LiveReplayError)
            else support.reject("LIVE_REPLAY", str(exc))
        )
        return _failure(report, error)

    report.update(
        {
            "live_runs": execution.live_runs,
            "checker_source_closure": checker_source_closure,
            "runtime_limits": {
                "input_bytes": support.MAX_RUNTIME_INPUT_BYTES,
                "output_bytes": support.MAX_RUNTIME_OUTPUT_BYTES,
                "timeout_seconds": support.RUNTIME_TIMEOUT_SECONDS,
            },
            "runtime_transports": {
                "executable": "linux_memfd_full_seals_v1",
                "stdin": support.replay_process.STDIN_TRANSPORT,
            },
            "verifier_identity": execution.verifier_identity,
            "same_host_pinned_v1_verifier_live_replay": True,
            "positive_request_verified": True,
            "ambient_dev_mode_zero_parity_verified": True,
            "ambient_dev_mode_enabled_values_rejected": True,
            "exact_seal_mutation_rejected": True,
            "error_codes": [],
            "errors": [],
            "ok": True,
            "status": ACCEPTED_STATUS,
        }
    )
    return report


def _print_human(report: Mapping[str, Any]) -> None:
    if report.get("ok") is True:
        print(
            f"ok: {ACCEPTED_STATUS}; historical provenance, sandbox, release, "
            "settlement, privacy, and production claims false"
        )
        return
    print("error: recursive RISC0 live replay rejected", file=sys.stderr)
    for error in report.get("errors", []):
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace-root", type=Path, required=True)
    parser.add_argument("--workspace-archive", type=Path, required=True)
    parser.add_argument("--artifact-report", type=Path, required=True)
    parser.add_argument("--program-directory", type=Path, required=True)
    parser.add_argument("--static-verifier", type=Path, required=True)
    parser.add_argument("--root-proof", type=Path, required=True)
    parser.add_argument("--positive-verify-request", type=Path, required=True)
    parser.add_argument("--verified-transcript", type=Path, required=True)
    parser.add_argument("--malformed-root-proof", type=Path, required=True)
    parser.add_argument("--malformed-verify-request", type=Path, required=True)
    parser.add_argument("--malformed-reject-transcript", type=Path, required=True)
    parser.add_argument("--runtime-directory", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = check_risc0_recursive_live_replay(
        rebuild.RebuildEvidencePaths(
            workspace_root=args.workspace_root,
            workspace_archive=args.workspace_archive,
            artifact_report=args.artifact_report,
            program_directory=args.program_directory,
            static_verifier=args.static_verifier,
            root_proof=args.root_proof,
            positive_verify_request=args.positive_verify_request,
            verified_transcript=args.verified_transcript,
            malformed_root_proof=args.malformed_root_proof,
            malformed_verify_request=args.malformed_verify_request,
            malformed_reject_transcript=args.malformed_reject_transcript,
        ),
        runtime_directory=args.runtime_directory,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
