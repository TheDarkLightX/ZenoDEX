from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_aggregate_adapter_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_aggregate_adapter_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 16
    assert receipt["rejected_case_count"] == 16
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "bridge_hash_forgery_survives" in names
    assert "aggregate_read_rejection_survives" in names
    assert "action_query_mismatch_survives" in names
    assert "action_value_hash_mismatch_survives" in names
    assert "action_id_mismatch_survives" in names
    assert "action_read_receipt_mismatch_survives" in names
    assert "action_consumer_receipt_mismatch_survives" in names
    assert "profile_hash_forgery_survives" in names
    assert "profile_module_mismatch_survives" in names
    assert "action_freshness_exceeds_profile_survives" in names
    assert "action_not_critical_survives" in names
    assert "missing_aggregate_read_survives" in names
    assert "missing_action_survives" in names
    assert "missing_profile_survives" in names
    assert "hidden_top_level_field_survives" in names
    assert "wrong_schema_survives" in names


def test_zenodex_oracle_aggregate_adapter_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-aggregate-adapter-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_aggregate_adapter_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.aggregate_adapter_chaos_replay.v1"
    assert receipt["ok"] is True
