#!/usr/bin/env python3
"""Fail-closed production-readiness status for the current ZenoDEX checkout."""

# ruff: noqa: E402, I001

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_public_testnet_v0_1_16_evidence import (  # noqa: E402
    REQUIRED_ARTIFACTS as PUBLIC_TESTNET_REQUIRED_ARTIFACTS,
    check_evidence_manifest,
)
from tools.check_zeno_ledger_two_machine_evidence import (  # noqa: E402
    validate_two_machine_evidence_v0,
)

REPORT_SCHEMA = "zenodex.production_readiness_status.v1"
RELEASE_GATE_REPORT_SCHEMA = "zenodex.release_gate_report.v1"
REQUIRED_RELEASE_GATE_CHECKS = (
    "kernel_assurance",
    "container_hardening",
    "python_tests",
    "ui_audit",
    "production_image_build",
    "trivy_scan",
)

DEFAULT_PUBLIC_TESTNET_MANIFEST = (
    ROOT / "runs" / "production_readiness" / "public_testnet_v0_1_16" / "evidence_manifest.json"
)
DEFAULT_TWO_MACHINE_EVIDENCE = (
    ROOT / "runs" / "production_readiness" / "zeno_ledger_two_machine" / "two_machine_evidence.json"
)
DEFAULT_RELEASE_GATE_REPORT = (
    ROOT / "runs" / "production_readiness" / "release_gate" / "prod_gate_report.json"
)


def build_readiness_status(
    *,
    public_testnet_manifest: Path = DEFAULT_PUBLIC_TESTNET_MANIFEST,
    two_machine_evidence: Path = DEFAULT_TWO_MACHINE_EVIDENCE,
    release_gate_report: Path = DEFAULT_RELEASE_GATE_REPORT,
    expected_commit: str | None = None,
    run_internal_gates: bool = True,
    timeout_sec: int = 900,
) -> dict[str, Any]:
    """Return the current production-readiness status.

    Missing external artifacts are blockers. They are never treated as a local
    pass, because public-testnet and two-machine evidence must come from an
    actual run, then be checked by the dedicated artifact validators.
    """
    commit = expected_commit or _git_head()
    lanes = [
        _production_boundary_lane(run_internal_gates=run_internal_gates, timeout_sec=timeout_sec),
        _traceability_lane(run_internal_gates=run_internal_gates, timeout_sec=timeout_sec),
        _key_management_lane(run_internal_gates=run_internal_gates, timeout_sec=timeout_sec),
        _key_management_bypass_lane(run_internal_gates=run_internal_gates, timeout_sec=timeout_sec),
        _autogov_node_apply_lane(run_internal_gates=run_internal_gates, timeout_sec=timeout_sec),
        _public_testnet_lane(public_testnet_manifest),
        _two_machine_lane(two_machine_evidence, expected_commit=commit),
        _release_gate_lane(release_gate_report, expected_commit=commit),
    ]
    blocked_lanes = [
        str(lane["lane_id"])
        for lane in lanes
        if lane.get("ok") is not True
    ]
    production_ready = not blocked_lanes
    return {
        "schema": REPORT_SCHEMA,
        "ok": production_ready,
        "status": "ready" if production_ready else "blocked",
        "production_ready": production_ready,
        "production_security_claim": False,
        "production_security_claim_reason": (
            "This checker aggregates readiness evidence. It does not publish "
            "or flip a production-security claim."
        ),
        "expected_commit": commit,
        "summary": {
            "lane_count": len(lanes),
            "accepted_lane_count": sum(1 for lane in lanes if lane.get("ok") is True),
            "blocked_lane_count": len(blocked_lanes),
        },
        "blocked_lanes": blocked_lanes,
        "lanes": lanes,
        "non_claims": [
            "does_not_claim_mainnet_live_value_ready",
            "does_not_replace_external_security_audit",
            "does_not_synthesize_public_testnet_or_two_machine_evidence",
        ],
    }


def _production_boundary_lane(*, run_internal_gates: bool, timeout_sec: int) -> dict[str, Any]:
    return _json_command_lane(
        lane_id="production_boundary",
        command=("python3", "tools/check_production_boundary.py", "--json"),
        category="internal_gate",
        run_internal_gates=run_internal_gates,
        timeout_sec=timeout_sec,
    )


def _traceability_lane(*, run_internal_gates: bool, timeout_sec: int) -> dict[str, Any]:
    return _json_command_lane(
        lane_id="production_traceability_matrix",
        command=("python3", "tools/check_production_traceability_matrix.py"),
        category="internal_gate",
        run_internal_gates=run_internal_gates,
        timeout_sec=timeout_sec,
    )


def _key_management_lane(*, run_internal_gates: bool, timeout_sec: int) -> dict[str, Any]:
    return _json_command_lane(
        lane_id="production_key_management_completion",
        command=("python3", "tools/check_production_key_management_completion.py"),
        category="internal_gate",
        run_internal_gates=run_internal_gates,
        timeout_sec=timeout_sec,
    )


def _key_management_bypass_lane(*, run_internal_gates: bool, timeout_sec: int) -> dict[str, Any]:
    return _json_command_lane(
        lane_id="production_key_management_bypasses",
        command=("python3", "tools/check_production_key_management_bypasses.py"),
        category="internal_gate",
        run_internal_gates=run_internal_gates,
        timeout_sec=timeout_sec,
    )


def _autogov_node_apply_lane(*, run_internal_gates: bool, timeout_sec: int) -> dict[str, Any]:
    command = (
        "python3",
        "-m",
        "pytest",
        "-q",
        "tests/integration/test_autonomous_governance_live_registry.py",
        "tests/integration/test_autogov_live_apply_api.py",
        "tests/integration/test_autonomous_governance_policy_pin.py",
        "tests/integration/test_zeno_governance_authority.py",
        "tests/integration/test_zeno_ledger_signature_bls_backend_guard.py",
    )
    return _plain_command_lane(
        lane_id="autogovnext_node_apply_path",
        command=command,
        category="internal_gate",
        run_internal_gates=run_internal_gates,
        timeout_sec=timeout_sec,
        blocker_if_skipped="AutoGovNEXT node/apply path tests were not run.",
    )


def _json_command_lane(
    *,
    lane_id: str,
    command: tuple[str, ...],
    category: str,
    run_internal_gates: bool,
    timeout_sec: int,
) -> dict[str, Any]:
    if not run_internal_gates:
        return _blocked_lane(
            lane_id=lane_id,
            category=category,
            command=command,
            blockers=["internal gate not run"],
        )
    proc = _run_command(command, timeout_sec=timeout_sec)
    details: dict[str, Any] = {"returncode": proc["returncode"]}
    errors: list[str] = list(proc["errors"])
    parsed: Any = None
    if proc["stdout"]:
        try:
            parsed = json.loads(str(proc["stdout"]))
            details["report"] = parsed
        except json.JSONDecodeError as exc:
            errors.append(f"stdout was not JSON: {exc}")
    ok = proc["returncode"] == 0 and isinstance(parsed, Mapping) and parsed.get("ok") is True and not errors
    return _lane(
        lane_id=lane_id,
        category=category,
        ok=ok,
        status="accepted" if ok else "rejected",
        command=command,
        errors=errors,
        details=details,
    )


def _plain_command_lane(
    *,
    lane_id: str,
    command: tuple[str, ...],
    category: str,
    run_internal_gates: bool,
    timeout_sec: int,
    blocker_if_skipped: str,
) -> dict[str, Any]:
    if not run_internal_gates:
        return _blocked_lane(
            lane_id=lane_id,
            category=category,
            command=command,
            blockers=[blocker_if_skipped],
        )
    proc = _run_command(command, timeout_sec=timeout_sec)
    ok = proc["returncode"] == 0 and not proc["errors"]
    return _lane(
        lane_id=lane_id,
        category=category,
        ok=ok,
        status="accepted" if ok else "rejected",
        command=command,
        errors=list(proc["errors"]),
        details={
            "returncode": proc["returncode"],
            "stdout_tail": _tail(str(proc["stdout"])),
            "stderr_tail": _tail(str(proc["stderr"])),
        },
    )


def _public_testnet_lane(manifest_path: Path) -> dict[str, Any]:
    command = ("python3", "tools/check_public_testnet_v0_1_16_evidence.py", _rel(manifest_path))
    if not manifest_path.is_file():
        return _blocked_lane(
            lane_id="public_testnet_v0_1_16_evidence",
            category="external_artifact",
            command=command,
            blockers=[
                f"missing public-testnet evidence manifest: {_rel(manifest_path)}",
                "required artifacts: " + ", ".join(PUBLIC_TESTNET_REQUIRED_ARTIFACTS),
            ],
            details={"manifest_path": _rel(manifest_path)},
        )
    try:
        report = check_evidence_manifest(manifest_path)
    except Exception as exc:
        report = {"ok": False, "errors": [f"{type(exc).__name__}: {exc}"]}
    ok = report.get("ok") is True
    return _lane(
        lane_id="public_testnet_v0_1_16_evidence",
        category="external_artifact",
        ok=ok,
        status="accepted" if ok else "rejected",
        command=command,
        errors=[str(error) for error in report.get("errors", [])],
        details={"report": report, "manifest_path": _rel(manifest_path)},
    )


def _two_machine_lane(evidence_path: Path, *, expected_commit: str | None) -> dict[str, Any]:
    command_parts = ["python3", "tools/check_zeno_ledger_two_machine_evidence.py", _rel(evidence_path)]
    if expected_commit:
        command_parts.extend(["--expected-commit", expected_commit])
    command = tuple(command_parts)
    if not evidence_path.is_file():
        return _blocked_lane(
            lane_id="zeno_ledger_two_machine_latest_main_evidence",
            category="external_artifact",
            command=command,
            blockers=[f"missing two-machine evidence archive: {_rel(evidence_path)}"],
            details={"evidence_path": _rel(evidence_path), "expected_commit": expected_commit},
        )
    try:
        raw = json.loads(evidence_path.read_text(encoding="utf-8"))
        report = validate_two_machine_evidence_v0(raw, expected_commit=expected_commit)
    except Exception as exc:
        report = {"ok": False, "errors": [f"{type(exc).__name__}: {exc}"]}
    required = report.get("required_evidence_fields")
    missing_required = (
        [
            str(key)
            for key, value in required.items()
            if value is not True
        ]
        if isinstance(required, Mapping)
        else []
    )
    errors = [str(error) for error in report.get("errors", [])]
    if missing_required:
        errors.append("required_evidence_fields false: " + ",".join(sorted(missing_required)))
    ok = report.get("ok") is True and not missing_required
    return _lane(
        lane_id="zeno_ledger_two_machine_latest_main_evidence",
        category="external_artifact",
        ok=ok,
        status="accepted" if ok else "rejected",
        command=command,
        errors=errors,
        details={"report": report, "evidence_path": _rel(evidence_path), "expected_commit": expected_commit},
    )


def _release_gate_lane(report_path: Path, *, expected_commit: str | None) -> dict[str, Any]:
    command = ("bash", "tools/prod_gate.sh")
    if not report_path.is_file():
        return _blocked_lane(
            lane_id="full_release_gate_artifact",
            category="external_artifact",
            command=command,
            blockers=[f"missing archived release-gate report: {_rel(report_path)}"],
            details={
                "report_path": _rel(report_path),
                "accepted_report_schema": RELEASE_GATE_REPORT_SCHEMA,
                "expected_commit": expected_commit,
            },
        )
    errors: list[str] = []
    try:
        report = _load_mapping(report_path)
    except Exception as exc:
        report = {}
        errors.append(f"{type(exc).__name__}: {exc}")
    if report.get("schema") != RELEASE_GATE_REPORT_SCHEMA:
        errors.append(f"schema must be {RELEASE_GATE_REPORT_SCHEMA}")
    if report.get("ok") is not True:
        errors.append("release-gate report must have ok=true")
    if report.get("command") != "bash tools/prod_gate.sh":
        errors.append("release-gate report command must be bash tools/prod_gate.sh")
    if expected_commit and report.get("commit_sha") != expected_commit:
        errors.append("release-gate report commit_sha must match expected_commit")
    if not isinstance(report.get("completed_at"), str) or not str(report.get("completed_at")).strip():
        errors.append("release-gate report completed_at must be a non-empty string")
    check_results = report.get("check_results")
    if not isinstance(check_results, Mapping):
        errors.append("release-gate report check_results must be an object")
        check_results = {}
    for check_id in REQUIRED_RELEASE_GATE_CHECKS:
        check = check_results.get(check_id)
        if not isinstance(check, Mapping) or check.get("ok") is not True:
            errors.append(f"release-gate check {check_id} must have ok=true")
    return _lane(
        lane_id="full_release_gate_artifact",
        category="external_artifact",
        ok=not errors,
        status="accepted" if not errors else "rejected",
        command=command,
        errors=errors,
        details={"report": report, "report_path": _rel(report_path), "expected_commit": expected_commit},
    )


def _blocked_lane(
    *,
    lane_id: str,
    category: str,
    command: tuple[str, ...],
    blockers: list[str],
    details: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return _lane(
        lane_id=lane_id,
        category=category,
        ok=False,
        status="blocked",
        command=command,
        blockers=blockers,
        details=dict(details or {}),
    )


def _lane(
    *,
    lane_id: str,
    category: str,
    ok: bool,
    status: str,
    command: tuple[str, ...],
    blockers: list[str] | None = None,
    errors: list[str] | None = None,
    details: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "lane_id": lane_id,
        "category": category,
        "ok": ok,
        "status": status,
        "replay_command": _command_string(command),
        "argv": list(command),
        "blockers": list(blockers or []),
        "errors": list(errors or []),
        "details": dict(details or {}),
    }


def _run_command(command: tuple[str, ...], *, timeout_sec: int) -> dict[str, Any]:
    argv = [sys.executable if part == "python3" else part for part in command]
    try:
        proc = subprocess.run(
            argv,
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        return {
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "errors": [] if proc.returncode == 0 else [_tail(proc.stderr or proc.stdout)],
        }
    except Exception as exc:  # pragma: no cover - defensive CLI path
        return {
            "returncode": None,
            "stdout": "",
            "stderr": "",
            "errors": [f"{type(exc).__name__}: {exc}"],
        }


def _load_mapping(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{_rel(path)} must decode to a JSON object")
    return obj


def _git_head() -> str | None:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except Exception:
        return None
    head = proc.stdout.strip()
    return head if proc.returncode == 0 and head else None


def _rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def _command_string(command: tuple[str, ...]) -> str:
    return " ".join(command)


def _tail(text: str, *, limit: int = 4000) -> str:
    return text[-limit:] if len(text) > limit else text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON. This is the default output format.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON.")
    parser.add_argument("--public-testnet-manifest", type=Path, default=DEFAULT_PUBLIC_TESTNET_MANIFEST)
    parser.add_argument("--two-machine-evidence", type=Path, default=DEFAULT_TWO_MACHINE_EVIDENCE)
    parser.add_argument("--release-gate-report", type=Path, default=DEFAULT_RELEASE_GATE_REPORT)
    parser.add_argument("--expected-commit")
    parser.add_argument(
        "--skip-internal",
        action="store_true",
        help="Do not run local internal gates; they are reported as blockers.",
    )
    parser.add_argument("--timeout-sec", type=int, default=900)
    args = parser.parse_args(argv)

    report = build_readiness_status(
        public_testnet_manifest=args.public_testnet_manifest,
        two_machine_evidence=args.two_machine_evidence,
        release_gate_report=args.release_gate_report,
        expected_commit=args.expected_commit,
        run_internal_gates=not args.skip_internal,
        timeout_sec=args.timeout_sec,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["production_ready"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
