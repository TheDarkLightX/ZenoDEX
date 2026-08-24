from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin

ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_perp_risk_antichain_breakthrough_20260628" / "report.json"


def test_perp_risk_antichain_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_perp_risk_antichain_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["lattice"]["primitive_axis_count"] == 12
    assert report["lattice"]["dense_state_count"] == 4096
    assert report["lattice"]["overall_minimal_reject_count"] == 12
    assert report["lattice"]["compression_ratio_dense_to_overall_antichain"] == "4096:12"
    assert report["lattice"]["monotonicity_ok"] is True
    assert report["lattice"]["overall_antichain_minimal_ok"] is True
    assert report["lattice"]["component_antichain_coverage_ok"] is True
    assert report["lattice"]["stale_breaker_fail_closed_ok"] is True
    assert report["numeric_boundary"]["ok"] is True
    assert report["numeric_boundary"]["stale_only_risk_envelope_ok"] is False
    assert report["numeric_boundary"]["breaker_only_risk_envelope_ok"] is False
    assert report["containment_replay"]["ok"] is True
    assert report["tau"]["risk_envelope_direct"]["ok"] is True
    assert report["tau"]["antichain_certificate"]["ok"] is True
    assert report["tau"]["antichain_certificate"]["invalid_accepts"] == 0

    cases = {case["case_id"]: case for case in report["tau"]["antichain_certificate"]["cases"]}
    assert cases["antichain_certificate_pass"]["got"]["o5"] == 1
    assert cases["monotonicity_reject"]["got"]["o5"] == 0
    assert cases["minimal_antichain_reject"]["got"]["o5"] == 0
    assert cases["component_coverage_reject"]["got"]["o5"] == 0
    assert cases["containment_replay_reject"]["got"]["o5"] == 0
    assert cases["tau_parity_reject"]["got"]["o5"] == 0
    assert cases["stale_breaker_fail_closed_reject"]["got"]["o5"] == 0
    assert cases["authority_reject"]["got"]["o5"] == 0
    assert cases["inactive_safe"]["got"]["o6"] == 1
