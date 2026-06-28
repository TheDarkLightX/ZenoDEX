from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_bitvector_frontier_decision_20260628" / "report.json"


def test_tau_bitvector_frontier_decision_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_bitvector_frontier_decision_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    decision = report["decision"]

    assert report["ok"] is True
    assert decision["small_direct_bv16_island_supported"] is True
    assert decision["broad_host_projection_refuted"] is False
    assert decision["host_projection_default_preserved"] is True
    assert decision["profile_gate_required"] is True
    assert decision["invalid_accepts"] == 0
    assert decision["checked_tau_binaries"] >= 1
    assert "workspace_latest" in decision["fast_direct_labels"]
    assert "upstream_main" in decision["slow_or_worse_direct_labels"]
    assert report["frontier_resolution"]["answer"].startswith("No for the broad default")
