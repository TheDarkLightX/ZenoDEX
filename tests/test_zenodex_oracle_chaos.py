from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_chaos_replay_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 28
    assert receipt["rejected_case_count"] == 28
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "consumer_action_borrows_other_value" in names
    assert "emergency_oracle_bypass_flag_set" in names
    assert "duplicate_receipt_id_shadows_terminal" in names
    assert "stray_receipt_hides_unreachable_evidence" in names
    assert "unsupported_receipt_type_in_terminal_closure" in names
    assert "dependency_consumed_before_it_appears" in names
    assert "read_receipt_depends_on_itself" in names
    assert "read_receipt_depends_on_action_receipt" in names
    assert "action_depends_on_extra_reachable_read" in names
    assert "action_duplicates_read_dependency" in names
    assert "terminal_aliases_read_as_action" in names
    assert "unknown_top_level_field_survives" in names
    assert "unknown_terminal_field_survives" in names
    assert "unknown_read_receipt_field_survives" in names
    assert "unknown_action_receipt_field_survives" in names
    assert "consumer_action_replays_expired_read" in names
    assert "consumer_action_precedes_read_observation" in names
    assert "consumer_action_erases_consumer_identity" in names
    assert "receipt_id_forged_without_body_match" in names


def test_zenodex_oracle_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-chaos.json"
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_chaos.py", "--output", str(output)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.chaos_replay.v1"
    assert receipt["ok"] is True
