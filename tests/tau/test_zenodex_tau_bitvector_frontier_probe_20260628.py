from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_bitvector_frontier_probe_20260628" / "report.json"


def test_tau_bitvector_frontier_probe_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_bitvector_frontier_probe_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    summary = report["summary"]

    assert report["direct_spec"] == "src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau"
    assert report["projected_spec"] == "src/tau_specs/recommended/receipt_sequence_projected_guard_v1.tau"
    assert summary["breakthrough_supported"] is True
    assert summary["invalid_accepts"] == 0
    assert summary["direct_ok_count"] >= 1
    assert summary["projected_ok_count"] >= 1
    assert summary["equivalent_count"] >= 1
    assert any(
        label == "workspace_latest" or label.startswith("bitblasting")
        for label in summary["fast_direct_labels"]
    )

    latest_row = next(row for row in report["tau_binaries"] if row["label"] == "workspace_latest")
    assert latest_row["direct"]["ok"] is True
    assert latest_row["projected"]["ok"] is True
    assert latest_row["behavior_equivalent"] is True
    assert latest_row["invalid_accepts"] == 0
