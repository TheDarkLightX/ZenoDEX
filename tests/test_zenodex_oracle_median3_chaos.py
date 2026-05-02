from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_median3_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_median3_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 18
    assert receipt["rejected_case_count"] == 18
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "aggregate_value_not_median" in names
    assert "aggregate_confidence_mismatch" in names
    assert "aggregate_deviation_mismatch" in names
    assert "aggregate_observed_epoch_mismatch" in names
    assert "report_query_id_mismatch" in names
    assert "stale_report_survives" in names
    assert "future_report_survives" in names
    assert "duplicate_reporter_survives" in names
    assert "duplicate_source_survives" in names
    assert "too_few_reports_survive" in names
    assert "too_many_reports_survive" in names
    assert "forged_report_id_survives" in names
    assert "forged_aggregate_id_survives" in names
    assert "deviation_policy_exceeded" in names
    assert "nonpositive_report_value_survives" in names
    assert "hidden_report_field_survives" in names
    assert "hidden_aggregate_field_survives" in names
    assert "wrong_schema_survives" in names


def test_zenodex_oracle_median3_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-median3-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_median3_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.median3_chaos_replay.v1"
    assert receipt["ok"] is True
