from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_evidence_dag_hitting_set_breakthrough_20260628" / "report.json"


def test_evidence_dag_hitting_set_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_evidence_dag_hitting_set_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["base_scenario"]["claim_count"] == 3
    assert report["base_scenario"]["blocker_count"] == 8
    assert report["base_scenario"]["task_count"] == 13
    assert report["base_scenario"]["exact_solution"]["subset_count"] == 4096
    assert report["compression"]["naive_single_purpose_task_count"] == 8
    assert report["compression"]["selected_task_count"] == 3
    assert report["compression"]["reduction_ratio"] == "8:3"
    assert report["base_scenario"]["exact_solution"]["selected_task_ids"] == [
        "public_claim_gate_bundle",
        "research_kernel_packet",
        "tau_replay_bundle",
    ]
    assert report["base_scenario"]["certificate"]["objective_minimal_ok"] is True
    assert report["base_scenario"]["certificate"]["deterministic_tie_ok"] is True
    assert report["base_scenario"]["certificate"]["redundancy_pruned_ok"] is True

    assert report["negative_scenarios"]["cycle"]["ok"] is False
    assert report["negative_scenarios"]["cycle"]["dependency"]["acyclic_ok"] is False
    assert report["negative_scenarios"]["missing_path"]["ok"] is False
    assert report["negative_scenarios"]["missing_path"]["every_claim_has_path_ok"] is False
    assert report["negative_scenarios"]["nonminimal_certificate"]["ok"] is False
    assert report["negative_scenarios"]["nonminimal_certificate"]["certificate"]["objective_minimal_ok"] is False
    assert report["negative_scenarios"]["deterministic_tie"]["certificate"]["objective_minimal_ok"] is True
    assert report["negative_scenarios"]["deterministic_tie"]["certificate"]["deterministic_tie_ok"] is False

    assert report["tau"]["certificate"]["ok"] is True
    assert report["tau"]["certificate"]["invalid_accepts"] == 0

    cases = {case["case_id"]: case for case in report["tau"]["certificate"]["cases"]}
    assert cases["certificate_pass"]["got"]["o5"] == 1
    assert cases["cycle_guard_reject"]["got"]["o5"] == 0
    assert cases["missing_path_guard_reject"]["got"]["o5"] == 0
    assert cases["minimality_reject"]["got"]["o5"] == 0
    assert cases["tie_break_reject"]["got"]["o5"] == 0
    assert cases["quality_floor_reject"]["got"]["o5"] == 0
    assert cases["authority_boundary_reject"]["got"]["o5"] == 0
    assert cases["inactive_safe"]["got"]["o6"] == 1
