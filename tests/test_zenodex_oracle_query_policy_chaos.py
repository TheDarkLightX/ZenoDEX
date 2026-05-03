from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_query_policy_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 19
    assert receipt["rejected_case_count"] == 19
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "staleness_downgrade_survives" in names
    assert "deviation_downgrade_survives" in names
    assert "evidence_floor_downgrade_survives" in names
    assert "source_quorum_downgrade_survives" in names
    assert "reporter_quorum_downgrade_survives" in names
    assert "aggregation_schema_drift_survives" in names
    assert "read_schema_drift_survives" in names
    assert "policy_content_hash_forgery_survives" in names
    assert "policy_query_mismatch_survives" in names
    assert "wrong_supersedes_survives" in names
    assert "version_skip_survives" in names
    assert "unknown_policy_binding_survives" in names
    assert "nonlatest_policy_binding_survives" in names
    assert "noncritical_binding_survives" in names
    assert "action_before_binding_survives" in names
    assert "hidden_policy_field_survives" in names
    assert "hidden_event_field_survives" in names
    assert "event_epoch_regression_survives" in names
    assert "wrong_schema_survives" in names


def test_zenodex_oracle_query_policy_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-query-policy-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_query_policy_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.query_policy_chaos_replay.v1"
    assert receipt["ok"] is True
