from __future__ import annotations

import json
from pathlib import Path

from tools.check_zenodex_production_readiness import (
    RELEASE_GATE_REPORT_SCHEMA,
    REQUIRED_RELEASE_GATE_CHECKS,
)
from tools.run_prod_gate_report import STAGE_MARKERS, run_prod_gate_report


def _write_gate(path: Path, *, exit_code: int = 0, markers: bool = True) -> None:
    lines = ["#!/usr/bin/env bash", "set -euo pipefail"]
    if markers:
        for marker in STAGE_MARKERS.values():
            lines.append(f"echo {marker!r}")
    lines.append(f"exit {exit_code}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    path.chmod(0o755)


def test_prod_gate_report_accepts_successful_gate_with_all_markers(tmp_path: Path) -> None:
    gate = tmp_path / "fake_prod_gate.sh"
    out = tmp_path / "prod_gate_report.json"
    _write_gate(gate)

    report = run_prod_gate_report(
        out_path=out,
        gate_script=gate,
        timeout_sec=30,
        allow_dirty=True,
    )
    persisted = json.loads(out.read_text(encoding="utf-8"))

    assert report["schema"] == RELEASE_GATE_REPORT_SCHEMA
    assert persisted["schema"] == RELEASE_GATE_REPORT_SCHEMA
    assert report["ok"] is True
    assert report["returncode"] == 0
    assert report["allow_dirty"] is True
    assert set(report["check_results"]) == set(REQUIRED_RELEASE_GATE_CHECKS)
    assert all(item["ok"] is True for item in report["check_results"].values())
    assert (tmp_path / "prod_gate_stdout.log").is_file()
    assert (tmp_path / "prod_gate_stderr.log").is_file()


def test_prod_gate_report_rejects_failed_gate(tmp_path: Path) -> None:
    gate = tmp_path / "fake_prod_gate.sh"
    out = tmp_path / "prod_gate_report.json"
    _write_gate(gate, exit_code=7)

    report = run_prod_gate_report(
        out_path=out,
        gate_script=gate,
        timeout_sec=30,
        allow_dirty=True,
    )

    assert report["ok"] is False
    assert report["returncode"] == 7
    assert "prod_gate_returncode:7" in report["incomplete_reasons"]
    assert any(
        reason.startswith("release_gate_checks_not_accepted:")
        for reason in report["incomplete_reasons"]
    )
    assert all(item["ok"] is False for item in report["check_results"].values())


def test_prod_gate_report_rejects_missing_stage_markers(tmp_path: Path) -> None:
    gate = tmp_path / "fake_prod_gate.sh"
    out = tmp_path / "prod_gate_report.json"
    _write_gate(gate, markers=False)

    report = run_prod_gate_report(
        out_path=out,
        gate_script=gate,
        timeout_sec=30,
        allow_dirty=True,
    )

    assert report["ok"] is False
    assert report["returncode"] == 0
    assert any(
        reason.startswith("release_gate_checks_not_accepted:")
        for reason in report["incomplete_reasons"]
    )
    assert all(item["marker_seen"] is False for item in report["check_results"].values())
