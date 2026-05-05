from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_reporter_lifecycle_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_lifecycle_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 20
    assert receipt["rejected_case_count"] == 20
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "duplicate_reporter_registration" in names
    assert "bond_deposit_before_registration" in names
    assert "report_before_registration" in names
    assert "report_under_required_bond" in names
    assert "duplicate_report_id_survives" in names
    assert "dispute_for_unknown_report" in names
    assert "zero_dispute_bond_survives" in names
    assert "slash_without_open_dispute" in names
    assert "slash_exceeds_reporter_bond" in names
    assert "double_slash_same_dispute" in names
    assert "resolve_unknown_dispute" in names
    assert "unregister_with_open_dispute" in names
    assert "withdraw_while_active" in names
    assert "withdraw_with_open_dispute" in names
    assert "withdraw_exceeds_bond" in names
    assert "event_epoch_regression" in names
    assert "hidden_event_field_survives" in names
    assert "unknown_event_type_survives" in names
    assert "boolean_bond_amount_survives" in names
    assert "too_many_events_survive" in names


def test_zenodex_oracle_reporter_lifecycle_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-reporter-lifecycle-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_reporter_lifecycle_chaos.py",
            "--output",
            str(output),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.reporter_lifecycle_chaos_replay.v1"
    assert receipt["ok"] is True
