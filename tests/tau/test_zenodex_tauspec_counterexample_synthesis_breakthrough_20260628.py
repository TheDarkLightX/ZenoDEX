from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tauspec_counterexample_synthesis_breakthrough_20260628" / "report.json"


def test_tauspec_counterexample_synthesis_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tauspec_counterexample_synthesis_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "tauspec_counterexample_synthesis_certificate_v1"
    assert report["breakthrough"]["frontier_atom"] == "atom_cf063839e779437f"
    assert report["breakthrough"]["invalid_accepts"] == 0
    assert report["breakthrough"]["negative_rejections"] >= 6
    assert report["breakthrough"]["work_items_covered"] == {"AB": True, "CoW": True}
    assert report["spec"]["features"]["direct_bv_ops"] == 0
    assert all(value == 1 for value in report["certificate_facts"].values())

    cases = {case["case_id"]: case for case in report["tau"]["case_results"]}
    assert cases["synthesis_certificate_pass"]["got"]["o6"] == 1
    for case_id in (
        "parse_or_lint_reject",
        "missing_negative_trace_reject",
        "mutation_accepts_reject",
        "baseline_value_reject",
        "authority_leak_reject",
        "work_item_1_reject",
        "work_item_2_reject",
    ):
        assert cases[case_id]["got"]["o6"] == 0

    specs = {item["spec_id"]: item for item in report["new_specifications"]}
    assert specs["tauspec_counterexample_synthesis_certificate_v1"]["status"] == "implemented_replayed"
    assert "cow_capacity_scope_counterexample_gate_v1" in specs
