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
    assert receipt["case_count"] == 12
    assert receipt["rejected_case_count"] == 12
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "consumer_action_borrows_other_value" in names
    assert "emergency_oracle_bypass_flag_set" in names
    assert "duplicate_receipt_id_shadows_terminal" in names


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
