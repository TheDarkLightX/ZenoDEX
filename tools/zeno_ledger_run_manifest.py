#!/usr/bin/env python3
"""Execute and verify a ZenoLedger testnet manifest."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Sequence


REPORT_SCHEMA = "zenodex.zeno_ledger.run_manifest_report.v0"
MANIFEST_SCHEMA = "zenodex.zeno_ledger.testnet_bundle.v0"


def _load_manifest(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("manifest must decode to a JSON object")
    if obj.get("schema") != MANIFEST_SCHEMA:
        raise ValueError("manifest schema mismatch")
    return obj


def _require_command(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise ValueError(f"{name} must be a non-empty list")
    out: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or item == "":
            raise ValueError(f"{name}[{index}] must be a non-empty string")
        out.append(item)
    return out


def _require_commands(value: object, *, name: str) -> list[list[str]]:
    if not isinstance(value, list) or not value:
        raise ValueError(f"{name} must be a non-empty list")
    return [_require_command(item, name=f"{name}[{index}]") for index, item in enumerate(value)]


def _require_optional_commands(value: object, *, name: str) -> list[list[str]]:
    if value is None:
        return []
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    return [_require_command(item, name=f"{name}[{index}]") for index, item in enumerate(value)]


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _run_command(command: Sequence[str], *, cwd: Path) -> dict[str, Any]:
    proc = subprocess.run(
        list(command),
        cwd=cwd,
        text=True,
        capture_output=True,
    )
    parsed_stdout: object | None = None
    if proc.stdout.strip():
        try:
            parsed_stdout = json.loads(proc.stdout)
        except json.JSONDecodeError:
            parsed_stdout = None
    return {
        "command": list(command),
        "returncode": int(proc.returncode),
        "stdout_json": parsed_stdout,
        "stderr": proc.stderr,
    }


def run_manifest_v0(*, manifest_path: Path, cwd: Path) -> dict[str, Any]:
    manifest = _load_manifest(manifest_path)
    run_commands = _require_commands(manifest.get("run_commands"), name="run_commands")
    verify_command = _require_command(manifest.get("verify_command"), name="verify_command")
    feature_gate_commands = _require_optional_commands(
        manifest.get("feature_gate_commands"),
        name="feature_gate_commands",
    )
    feature_gate_report_path: Path | None = None
    if "feature_gate_report_path" in manifest:
        raw_report_path = manifest.get("feature_gate_report_path")
        if not isinstance(raw_report_path, str) or raw_report_path == "":
            raise ValueError("feature_gate_report_path must be a non-empty string")
        feature_gate_report_path = Path(raw_report_path)
    attest_command: list[str] | None = None
    if "attest_command" in manifest:
        attest_command = _require_command(manifest.get("attest_command"), name="attest_command")
    mirror_index_command: list[str] | None = None
    if "mirror_index_command" in manifest:
        mirror_index_command = _require_command(
            manifest.get("mirror_index_command"),
            name="mirror_index_command",
        )

    block_reports = []
    for command in run_commands:
        report = _run_command(command, cwd=cwd)
        block_reports.append(report)
        if report["returncode"] != 0:
            raise RuntimeError(f"block command failed: {command}")
        stdout_json = report.get("stdout_json")
        if not isinstance(stdout_json, dict) or stdout_json.get("ok") is not True:
            raise RuntimeError(f"block command did not return ok=true: {command}")

    verify_report = _run_command(verify_command, cwd=cwd)
    if verify_report["returncode"] != 0:
        raise RuntimeError("verify command failed")
    verify_stdout = verify_report.get("stdout_json")
    if not isinstance(verify_stdout, dict) or verify_stdout.get("ok") is not True:
        raise RuntimeError("verify command did not return ok=true")

    feature_gate_reports = []
    for index, command in enumerate(feature_gate_commands):
        report = _run_command(command, cwd=cwd)
        feature_gate_reports.append(report)
        if report["returncode"] != 0:
            raise RuntimeError(f"feature gate command failed: {command}")
        stdout_json = report.get("stdout_json")
        if isinstance(stdout_json, dict) and stdout_json.get("ok") is False:
            raise RuntimeError(f"feature gate command returned ok=false: {command}")
    if feature_gate_report_path is not None:
        _write_json(
            feature_gate_report_path,
            {
                "schema": "zenodex.zeno_ledger.feature_gate_report.v0",
                "ok": True,
                "status": "accepted",
                "manifest_path": str(manifest_path),
                "gate_count": len(feature_gate_reports),
                "gate_reports": feature_gate_reports,
            },
        )

    attest_report: dict[str, Any] | None = None
    if attest_command is not None:
        raw_attest_report = _run_command(attest_command, cwd=cwd)
        if raw_attest_report["returncode"] != 0:
            raise RuntimeError("attest command failed")
        attest_stdout = raw_attest_report.get("stdout_json")
        if not isinstance(attest_stdout, dict) or attest_stdout.get("ok") is not True:
            raise RuntimeError("attest command did not return ok=true")
        attest_report = raw_attest_report

    mirror_index_report: dict[str, Any] | None = None
    if mirror_index_command is not None:
        raw_mirror_index_report = _run_command(mirror_index_command, cwd=cwd)
        if raw_mirror_index_report["returncode"] != 0:
            raise RuntimeError("mirror index command failed")
        mirror_stdout = raw_mirror_index_report.get("stdout_json")
        if not isinstance(mirror_stdout, dict) or mirror_stdout.get("ok") is not True:
            raise RuntimeError("mirror index command did not return ok=true")
        mirror_index_report = raw_mirror_index_report

    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "manifest_path": str(manifest_path),
        "checked_heights": verify_stdout.get("checked_heights", []),
        "last_header_hash": verify_stdout.get("last_header_hash"),
        "block_reports": block_reports,
        "verify_report": verify_report,
        "feature_gate_reports": feature_gate_reports,
        "attest_report": attest_report,
        "mirror_index_report": mirror_index_report,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Execute and verify a ZenoLedger testnet manifest")
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    args = parser.parse_args(argv)

    try:
        report = run_manifest_v0(manifest_path=args.manifest, cwd=args.cwd)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
