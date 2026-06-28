from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_breakthrough_specs_20260627" / "report.json"


def test_zenodex_tau_breakthrough_specs_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_breakthrough_specs_20260627.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["breakthrough"]["spec_id"] == "frontier_certificate_menu_v1"
    assert report["rankings"]["tau_spec_ebrm_v1"][0] == "frontier_certificate_menu_v1"
    assert {row["spec_id"] for row in report["candidates"]} == {
        "frontier_certificate_menu_v1",
        "route_dominance_frontier_envelope_v1",
        "oracle_polytope_frontier_envelope_v1",
        "ab_cow_exact_solver_envelope_v1",
    }
    assert all(row["latest"]["ok"] for row in report["candidates"])
    assert all(row["features"]["direct_bv_ops"] == 0 for row in report["candidates"])
    assert report["algorithm_work_items"]["1"]["artifact"] == "ab_cow_exact_solver_envelope_v1"
    assert report["algorithm_work_items"]["2"]["artifact"] == "ab_cow_exact_solver_envelope_v1"
