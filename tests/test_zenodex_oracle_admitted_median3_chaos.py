from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_admitted_median3_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_admitted_median3_chaos.py"],
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
    assert "aggregate_hash_forgery_survives" in names
    assert "wrong_median_value_survives" in names
    assert "wrong_confidence_survives" in names
    assert "wrong_deviation_survives" in names
    assert "wrong_observed_epoch_survives" in names
    assert "too_few_admissions_survive" in names
    assert "admission_rejection_survives" in names
    assert "duplicate_admission_survives" in names
    assert "duplicate_reporter_survives" in names
    assert "duplicate_source_survives" in names
    assert "admission_query_mismatch_survives" in names
    assert "admission_epoch_mismatch_survives" in names
    assert "admission_staleness_mismatch_survives" in names
    assert "multi_report_admission_survives" in names
    assert "deviation_policy_exceeded_survives" in names
    assert "hidden_top_level_field_survives" in names
    assert "hidden_aggregate_field_survives" in names
    assert "wrong_schema_survives" in names


def test_zenodex_oracle_admitted_median3_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-admitted-median3-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_admitted_median3_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.admitted_median3_chaos_replay.v1"
    assert receipt["ok"] is True
