from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_perps_snapshot_gate import (
    build_report,
    settle_snapshot_roundtrip_case,
)

ROOT = Path(__file__).resolve().parents[1]


def test_perps_snapshot_gate_accepts_bounded_roundtrip_cases() -> None:
    report = build_report()

    assert report["schema"] == "zenodex.oracle.perps_snapshot_gate_check.v1"
    assert report["status"] == "accepted"
    assert report["case_count"] == 10
    assert report["accepted_case_count"] == 10
    assert report["error_count"] == 0
    assert "does_not_claim_general_perps_snapshot_theorem" in report["not_claimed"]
    cases = {case["name"]: case for case in report["cases"]}
    assert cases["isolated_settle_snapshot_runtime_facts_roundtrip"]["details"]["runtime_value_e8"] == 100_000_000
    stale_case = cases["isolated_settle_stale_action_id_rejected_after_snapshot_drift"]
    assert stale_case["details"]["stale_action_id"] != stale_case["details"]["fresh_action_id"]
    assert stale_case["details"]["rejection"] == "oracle_adapter_bridge action_id mismatch"
    assert cases["clearinghouse_2p_snapshot_action_id_roundtrip"]["details"]["action_id"].startswith("sha256:")
    assert cases["clearinghouse_2p_adapter_bridge_executes_after_snapshot"]["status"] == "accepted"
    assert cases["clearinghouse_3p_snapshot_action_id_roundtrip"]["details"]["action_id"].startswith("sha256:")
    assert cases["clearinghouse_3p_adapter_bridge_executes_after_snapshot"]["status"] == "accepted"
    assert cases["invalid_oracle_snapshot_shape_rejected"]["details"]["rejection"]
    assert "position_base_a + position_base_b" in cases["invalid_clearinghouse_snapshot_shape_rejected"]["details"]["rejection"]


def test_perps_snapshot_gate_detects_tampered_settle_snapshot() -> None:
    case = settle_snapshot_roundtrip_case(tamper_snapshot=True)

    assert case["status"] == "rejected"
    assert "settle_runtime_facts_changed_after_snapshot_roundtrip" in case["errors"]


def test_perps_snapshot_gate_cli_text_and_json() -> None:
    text = subprocess.run(
        [sys.executable, "tools/check_zeno_oracle_perps_snapshot_gate.py", "--format", "text"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert text.returncode == 0, text.stdout + text.stderr
    assert "status = accepted" in text.stdout
    assert "case_count = 10" in text.stdout

    json_run = subprocess.run(
        [sys.executable, "tools/check_zeno_oracle_perps_snapshot_gate.py"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert json_run.returncode == 0, json_run.stdout + json_run.stderr
    receipt = json.loads(json_run.stdout)
    assert receipt["status"] == "accepted"
