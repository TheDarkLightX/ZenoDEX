from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_performance_frontier_breakthrough_20260628" / "report.json"


def test_tau_performance_frontier_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest") or not find_tau_bin(ROOT, profile="runtime"):
        pytest.skip("Tau binaries not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_performance_frontier_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "tau_performance_frontier_certificate_v1"
    assert report["breakthrough"]["frontier_atom"] == "atom_3d38c5d1362f4f9c"
    assert report["breakthrough"]["invalid_accepts"] == 0
    assert report["breakthrough"]["negative_rejections"] >= 12
    assert report["profile_summary"]["budget_lattice_ok"] is True
    assert report["contract_summary"]["semantic_contract_count"] >= 30
    assert report["contract_summary"]["host_projection_contract_count"] >= 10
    assert report["candidate_scan"]["max_bv_width"] <= 32
    assert report["candidate_scan"]["has_width_cast"] is False
    assert report["bitvector_decision"]["host_projection_default_preserved"] is True
    assert all(value == 1 for value in report["certificate_facts"].values())

    for profile_key in ("latest_tau", "runtime_tau"):
        cases = {case["case_id"]: case for case in report[profile_key]["case_results"]}
        assert cases["performance_frontier_pass"]["got"]["o6"] == 1
        for case_id in (
            "missing_profile_lattice_reject",
            "latest_budget_reject",
            "direct_bv_unprofiled_reject",
            "invalid_accepts_reject",
            "coverage_reject",
            "authority_reject",
        ):
            assert cases[case_id]["got"]["o6"] == 0
