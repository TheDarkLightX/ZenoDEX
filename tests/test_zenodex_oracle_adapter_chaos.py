from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_adapter_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_adapter_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 17
    assert receipt["rejected_case_count"] == 17
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "unaccepted_bundle_survives" in names
    assert "consumer_module_mismatch_survives" in names
    assert "action_kind_mismatch_survives" in names
    assert "action_id_mismatch_survives" in names
    assert "action_epoch_mismatch_survives" in names
    assert "query_mismatch_survives" in names
    assert "value_mismatch_survives" in names
    assert "read_receipt_id_mismatch_survives" in names
    assert "consumer_action_receipt_id_mismatch_survives" in names
    assert "evidence_below_action_floor_survives" in names
    assert "freshness_window_exceeds_action_limit_survives" in names
    assert "noncritical_action_descriptor_survives" in names
    assert "weak_required_evidence_floor_survives" in names
    assert "hidden_action_field_survives" in names
    assert "wrong_action_schema_survives" in names
    assert "missing_action_id_survives" in names
    assert "boolean_action_epoch_survives" in names


def test_zenodex_oracle_adapter_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-adapter-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_adapter_chaos.py",
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
    assert receipt["schema"] == "zenodex.oracle.adapter_chaos_replay.v1"
    assert receipt["ok"] is True
