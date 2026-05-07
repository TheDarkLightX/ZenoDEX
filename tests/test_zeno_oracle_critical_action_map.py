from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zeno_oracle_critical_action_map_matches_runtime_wiring() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_zeno_oracle_critical_action_map.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.critical_action_map_check.v1"
    assert receipt["status"] == "accepted"
    assert receipt["catalog_profile_count"] == 7
    assert receipt["runtime_wired_count"] == 7
    assert receipt["design_only_backlog_count"] == 0
    runtime_keys = {surface["key"] for surface in receipt["runtime_surfaces"]}
    assert runtime_keys == {
        "zenodex.perps:settle_epoch",
        "zenodex.perps:liquidate_account",
        "zenodex.zusd:mint",
        "zenodex.zusd:liquidate_vault",
        "zenodex.routing:guarded_quote",
        "zenodex.settlement:critical_settlement",
        "zenodex.trigger:execute_trigger",
    }
    backlog_keys = {item["key"] for item in receipt["design_only_backlog"]}
    assert backlog_keys == set()
