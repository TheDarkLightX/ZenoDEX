from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def test_oracle_mvp_completion_audit_reports_production_zusd_authority_blocker() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_mvp_completion_audit.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 2, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.mvp_completion_audit.v1"
    assert receipt["status"] == "rejected"
    assert receipt["criteria_count"] == 10
    assert receipt["accepted_criteria_count"] == sum(
        1 for criterion in receipt["criteria"] if criterion["ok"] is True
    )
    by_id = {item["id"]: item for item in receipt["criteria"]}
    assert by_id[6]["ok"] is False
    assert by_id[8]["ok"] is True
    assert by_id[10]["ok"] is True
    assert any("production zUSD" in limit for limit in by_id[6]["residual_limits"])
