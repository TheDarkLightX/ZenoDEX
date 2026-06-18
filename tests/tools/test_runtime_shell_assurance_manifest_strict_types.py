from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest

import tools.check_runtime_shell_assurance_manifest as checker


def _valid_report() -> dict[str, Any]:
    return {
        "ok": True,
        "command": "verify-shell",
        "ir_hash": "ir123",
        "mode": "bmc",
        "seed": 17,
        "traces": 64,
        "max_steps": 12,
        "determinism_trials": 3,
        "failure": None,
        "adapter": {"spec": "shell-adapter-v1"},
        "model": "/tmp/runtime_shell.yaml",
        "determinism": {
            "ok": True,
            "fingerprints": ["fp123", "fp123"],
        },
    }


def _valid_entry(report_path: Path) -> dict[str, Any]:
    return {
        "report_path": str(report_path),
        "ir_hash": "ir123",
        "mode": "bmc",
        "seed": 17,
        "traces": 64,
        "max_steps": 12,
        "determinism_trials": 3,
        "adapter_spec": "shell-adapter-v1",
        "kernel_path": "kernels/runtime_shell.yaml",
        "fingerprint": "fp123",
    }


def _write_report(tmp_path: Path, report: dict[str, Any]) -> Path:
    path = tmp_path / "verify_shell.json"
    path.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
    return path


def test_runtime_shell_verify_shell_accepts_strictly_typed_report(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _valid_report())

    checker._check_verify_shell(_valid_entry(report_path))


@pytest.mark.parametrize(
    ("field", "value", "match"),
    [
        ("seed", "17", "seed: expected int"),
        ("traces", True, "traces: expected int"),
        ("max_steps", "12", "max_steps: expected int"),
        ("determinism_trials", False, "determinism_trials: expected int"),
    ],
)
def test_runtime_shell_verify_shell_rejects_coerced_report_counts(
    tmp_path: Path,
    field: str,
    value: object,
    match: str,
) -> None:
    report = _valid_report()
    report[field] = value
    report_path = _write_report(tmp_path, report)

    with pytest.raises(checker.ManifestError, match=match):
        checker._check_verify_shell(_valid_entry(report_path))


def test_runtime_shell_verify_shell_rejects_coerced_expected_counts(tmp_path: Path) -> None:
    report_path = _write_report(tmp_path, _valid_report())
    entry = copy.deepcopy(_valid_entry(report_path))
    entry["traces"] = "64"

    with pytest.raises(checker.ManifestError, match="expected traces: expected int"):
        checker._check_verify_shell(entry)
