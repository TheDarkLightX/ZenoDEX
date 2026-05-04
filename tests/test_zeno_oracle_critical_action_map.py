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
    assert receipt["catalog_profile_count"] == 6
    assert receipt["runtime_wired_count"] == 4
    assert receipt["design_only_backlog_count"] == 2
    runtime_keys = {surface["key"] for surface in receipt["runtime_surfaces"]}
    assert runtime_keys == {
        "zenodex.perps:settle_epoch",
        "zenodex.zusd:mint",
        "zenodex.zusd:liquidate_vault",
        "zenodex.routing:guarded_quote",
    }
    surfaces = {surface["key"]: surface for surface in receipt["runtime_surfaces"]}
    assert "require_oracle_authorization_for_isolated_settle_epoch" in surfaces[
        "zenodex.perps:settle_epoch"
    ]["details"]["required_controls"]
    assert "ZUSD_ORACLE_AUTHORIZATION_REQUIRED" in surfaces["zenodex.zusd:mint"]["details"]["required_controls"]
    assert "ZUSD_ORACLE_AUTHORIZATION_REQUIRED" in surfaces[
        "zenodex.zusd:liquidate_vault"
    ]["details"]["required_controls"]
    assert "DEX_ROUTING_ORACLE_AUTHORIZATION_REQUIRED" in surfaces[
        "zenodex.routing:guarded_quote"
    ]["details"]["required_controls"]
    backlog_keys = {item["key"] for item in receipt["design_only_backlog"]}
    assert backlog_keys == {
        "zenodex.perps:liquidate_account",
        "zenodex.trigger:execute_trigger",
    }
