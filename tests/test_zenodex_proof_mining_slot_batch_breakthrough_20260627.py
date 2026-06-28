from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_proof_mining_slot_batch_breakthrough_20260627" / "report.json"
REPORT_MD = ROOT / "docs" / "research" / "ZENODEX_PROOF_MINING_SLOT_BATCH_BREAKTHROUGH_20260627.md"


def _run_replay() -> dict:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_proof_mining_slot_batch_breakthrough_20260627.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    return json.loads(REPORT_JSON.read_text(encoding="utf-8"))


def _load_report() -> dict:
    if not REPORT_JSON.exists():
        return _run_replay()
    return json.loads(REPORT_JSON.read_text(encoding="utf-8"))


def _case(report: dict, case_id: str) -> dict:
    for row in report["certificates"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing certificate case {case_id}")


def _tau_case(report: dict, case_id: str) -> dict:
    for row in report["tau"]["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing Tau case {case_id}")


def test_proof_mining_slot_batch_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = _run_replay()

    assert report["ok"] is True
    assert report["tau"]["ok"] is True
    assert len(report["certificates"]) == 5
    assert sum(1 for row in report["certificates"] if row["exact_beats_sequential"]) == 4
    assert all(row["verified"] for row in report["certificates"])
    assert all(check["ok"] and not check["accepted"] for check in report["mutation_checks"])
    assert REPORT_MD.exists()


def test_proof_mining_slot_batch_exact_assignment_lifts_collision_cases() -> None:
    report = _load_report()

    no_collision = _case(report, "no_collision_parity")
    interleaved = _case(report, "interleaved_collision_lift")
    wraparound = _case(report, "wraparound_tail_lift")
    six_pressure = _case(report, "six_proposal_pressure")

    assert no_collision["exact_beats_sequential"] is False
    assert no_collision["exact_objective_key"] == no_collision["sequential_objective_key"]
    assert interleaved["exact_objective_key"][0] < interleaved["sequential_objective_key"][0]
    assert wraparound["exact_objective_key"][0] < wraparound["sequential_objective_key"][0]
    assert six_pressure["candidate_count"] == 20_160
    assert six_pressure["exact_objective_key"][0] < six_pressure["sequential_objective_key"][0]


def test_proof_mining_slot_batch_tau_and_non_claim_boundaries() -> None:
    report = _load_report()
    markdown = REPORT_MD.read_text(encoding="utf-8")

    assert _tau_case(report, "slot_batch_pass")["got"]["o6"] == 1
    assert _tau_case(report, "objective_reject")["got"]["o6"] == 0
    assert _tau_case(report, "duplicate_reject")["got"]["o6"] == 0
    assert _tau_case(report, "authority_reject")["got"]["o6"] == 0
    assert "not wired into runtime proof payout flow" in markdown
    assert "bounded to the current 8-slot registry" in markdown
    assert "Tau does not compute hashes, enumerate assignments, or decide payouts" in markdown
