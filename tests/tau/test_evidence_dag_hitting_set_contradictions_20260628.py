from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_evidence_dag_hitting_set_contradictions import (
    REPORT_JSON,
    build_report,
    exact_minimal_bundle,
    evidence_dag_scenarios,
)


ROOT = Path(__file__).resolve().parents[2]


def test_evidence_dag_hitting_set_contradiction_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["spec_id"] == "evidence_dag_hitting_set_certificate_v1"
    assert report["scenario_count"] == 6
    assert report["negative_case_count"] == 5
    assert report["false_accept_count"] == 0
    assert report["max_exact_subset_count"] <= 1024
    assert report["tau"]["ok"] is True
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_evidence_dag_hitting_set_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_evidence_dag_hitting_set_contradictions.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["false_accept_count"] == 0


def test_exact_optimizer_selects_canonical_tie_minimum() -> None:
    scenario = next(row for row in evidence_dag_scenarios() if row.scenario_id == "tie_break_violation_reject")
    exact = exact_minimal_bundle(scenario.tasks, scenario.blocker_ids, scenario.claim_blockers)

    assert exact["selected_task_ids"] == ["a_manifest_combo", "claim_scope_scan", "quote_receipt_replay"]
    assert tuple(scenario.presented_task_ids) == ("claim_scope_scan", "quote_receipt_replay", "z_manifest_combo")


def test_negative_scenarios_name_expected_reject_reason() -> None:
    report = build_report()
    by_id = {row["scenario_id"]: row for row in report["scenarios"]}

    for scenario in evidence_dag_scenarios():
        if scenario.expected_reject_reason is None:
            continue
        assert scenario.expected_reject_reason in by_id[scenario.scenario_id]["reject_reasons"]
