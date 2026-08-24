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
    assert receipt["fail_closed_config"]["status"] == "accepted"
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
    surfaces_by_key = {surface["key"]: surface for surface in receipt["runtime_surfaces"]}
    assert surfaces_by_key["zenodex.perps:settle_epoch"]["details"]["required_controls"] == [
        "require_oracle_adapter_for_isolated_settle_epoch",
        "require_oracle_adapter_for_clearinghouse_settle_epoch",
        "require_oracle_authorization_for_isolated_settle",
        "require_oracle_authorization_for_clearinghouse_settle_epoch",
    ]
    assert surfaces_by_key["zenodex.perps:settle_epoch"]["details"]["covered_runtime_actions"] == [
        "isolated_settle_epoch",
        "clearinghouse_2p_settle_epoch",
        "clearinghouse_3p_transfer_settle_epoch",
        "clearinghouse_np_run_or_settle_epoch",
    ]
    assert surfaces_by_key["zenodex.zusd:mint"]["details"]["required_controls"] == [
        "ZUSD_ORACLE_ADAPTER_REQUIRED",
        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
    ]
    assert surfaces_by_key["zenodex.zusd:liquidate_vault"]["details"]["required_controls"] == [
        "ZUSD_ORACLE_ADAPTER_REQUIRED",
        "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
    ]
    assert surfaces_by_key["zenodex.trigger:execute_trigger"]["details"]["required_controls"] == [
        "check_trigger_execute_oracle_adapter_bridge(required=True)",
        "check_trigger_execute_oracle_authorization",
    ]
    required_controls = set(receipt["fail_closed_config"]["required_controls"])
    covered_controls = set(receipt["fail_closed_config"]["covered_controls"])
    assert required_controls <= covered_controls
    backlog_keys = {item["key"] for item in receipt["design_only_backlog"]}
    assert backlog_keys == set()
