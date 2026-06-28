from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tau_solver_portfolio_breakthrough_20260628 import (
    REPORT_JSON,
    build_report,
    portfolio_facts,
    supporting_reports,
    tau_cases,
)


ROOT = Path(__file__).resolve().parents[2]


def test_solver_portfolio_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["schema"] == "zenodex.tau_solver_portfolio_breakthrough_report.v1"
    assert all(value == 1 for value in report["portfolio_facts"].values())
    assert report["tau"]["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0
    assert len(report["tau"]["case_results"]) == 8
    assert report["supporting_reports"]["ab_n12_proxy_ratio"] >= 100
    assert report["supporting_reports"]["cow_n20_proxy_ratio"] >= 1000


def test_solver_portfolio_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau"]["invalid_accepts"] == 0


def test_solver_portfolio_negative_cases_cover_performance_and_rollback() -> None:
    facts = portfolio_facts(supporting_reports())
    cases = {case.case_id: case for case in tau_cases(facts)}

    assert cases["performance_reject"].step["i10"] == 0
    assert cases["performance_reject"].expected["o6"] == 0
    assert cases["rollback_reject"].step["i13"] == 0
    assert cases["rollback_reject"].expected["o6"] == 0
    assert cases["authority_reject"].step["i15"] == 0
    assert cases["authority_reject"].expected["o6"] == 0


def test_solver_portfolio_rejects_overbroad_claim_inputs() -> None:
    facts = portfolio_facts(supporting_reports())

    assert facts["negative_replay_ok"] == 1
    assert facts["ab_full_state_scope_ok"] == 1
    assert facts["cow_uncoupled_or_bounded_capacity_scope_ok"] == 1
    assert facts["advisory_model_only"] == 1
    assert facts["no_authority_effect"] == 1
