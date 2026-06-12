from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_rc1_candidate_plan_json_reports_blocked_current_tree() -> None:
    root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [sys.executable, "tools/rc1_candidate.py", "--plan", "--format", "json"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["schema"] == "zenodex/rc1-candidate-report/v1"
    assert payload["historical_release_label"] == "RC1"
    assert payload["active_candidate_label"] == "RC2"
    assert payload["blocked_before_run"] is True
    assert payload["readiness"]["overall_ok"] is False
    assert payload["results"] is None
    assert payload["steps"]


def test_rc1_candidate_plan_skip_flags_rewrite_prod_gate_step() -> None:
    root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate.py",
            "--plan",
            "--allow-blocked-readiness",
            "--skip-prod-gate-ui",
            "--skip-prod-gate-docker",
            "--format",
            "json",
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    prod_steps = [step for step in payload["steps"] if step[:2] == ["bash", "tools/prod_gate.sh"]]
    assert len(prod_steps) == 1
    assert "--skip-ui" in prod_steps[0]
    assert "--skip-docker" in prod_steps[0]


def test_rc1_candidate_plan_report_out_writes_receipt(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    report_path = tmp_path / "rc1_candidate_report.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate.py",
            "--plan",
            "--format",
            "json",
            "--report-out",
            str(report_path),
        ],
        cwd=root,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    stdout_payload = json.loads(proc.stdout)
    file_payload = json.loads(report_path.read_text(encoding="utf-8"))
    assert file_payload == stdout_payload
    assert file_payload["schema"] == "zenodex/rc1-candidate-report/v1"


def test_rc1_candidate_campaign_root_writes_stable_receipt_path(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    campaign_root = tmp_path / "rc1_candidates"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate.py",
            "--plan",
            "--format",
            "json",
            "--campaign-root",
            str(campaign_root),
            "--timestamp-utc",
            "20260327T120000Z",
            "--run-id",
            "rc1 smoke",
        ],
        cwd=root,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    expected = campaign_root / "20260327T120000Z_rc1-smoke" / "candidate_report.json"
    assert expected.is_file()
    payload = json.loads(expected.read_text(encoding="utf-8"))
    assert payload["schema"] == "zenodex/rc1-candidate-report/v1"
