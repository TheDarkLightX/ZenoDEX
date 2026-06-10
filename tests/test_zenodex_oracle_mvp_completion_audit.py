from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_oracle_mvp_completion_audit_accepts_current_local_shell() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_mvp_completion_audit.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.mvp_completion_audit.v1"
    assert receipt["status"] == "accepted"
    assert receipt["criteria_count"] == 10
    assert receipt["accepted_criteria_count"] == 10
    by_id = {item["id"]: item for item in receipt["criteria"]}
    assert by_id[6]["ok"] is True
    assert by_id[8]["ok"] is True
    assert by_id[10]["ok"] is True
    assert any("not every future routing" in limit for limit in by_id[6]["residual_limits"])

    # Criterion 8 must be backed by a live, measured chaos closure, not just a
    # CI workflow file: every case rejects and none fail.
    chaos = receipt["chaos"]
    assert chaos["total_case_count"] == chaos["total_rejected_case_count"]
    assert chaos["total_failed_case_count"] == 0
    assert chaos["total_case_count"] > 0
    assert all(surface["closed"] is True for surface in chaos["surfaces"])
    assert any("measured chaos closure" in line for line in by_id[8]["evidence"])
