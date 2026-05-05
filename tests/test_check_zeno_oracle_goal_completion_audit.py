from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_goal_completion_audit import build_audit


ROOT = Path(__file__).resolve().parents[1]


def test_goal_completion_audit_maps_all_prompt_items_and_blocks_goal_closure() -> None:
    audit = build_audit()

    assert audit["schema"] == "zenodex.oracle.goal_completion_audit.v1"
    assert audit["status"] == "blocked"
    assert audit["goal_complete"] is False
    assert audit["item_count"] == 10
    assert {item["id"] for item in audit["items"]} == set(range(1, 11))
    assert audit["complete_item_count"] < audit["item_count"]
    assert "production_oracle_network_not_live" in audit["production_blockers"]
    assert "live_reporter_economics_settlement_not_complete" in audit["production_blockers"]
    assert "generalized_math_proofs_not_complete" in audit["production_blockers"]

    items = {item["id"]: item for item in audit["items"]}
    assert items[2]["status"] == "devnet_complete"
    assert items[3]["status"] == "devnet_complete"
    assert items[4]["status"] == "partial"
    assert "live_economics_policy_gate_is_production_candidate_only" in items[4]["blockers"]
    assert "tools/check_zeno_oracle_live_economics_policy.py" in items[4]["evidence_files"]
    assert audit["live_economics_policy_gate"]["status"] == "production_candidate_only"
    assert "tools/check_zeno_oracle_disaster_frontier.py" in items[5]["evidence_files"]
    assert "production_disaster_frontier_has_explicit_blockers" in items[5]["blockers"]
    assert audit["disaster_frontier_gate"]["status"] == "explicit_blocker_frontier"
    assert items[8]["complete"] is True
    assert items[9]["status"] == "local_v0_complete"
    assert items[9]["complete"] is False
    assert "zenoproof_production_governance_policy_gate_is_candidate_only" in items[9]["blockers"]
    assert "tools/check_zenoproof_production_governance_policy.py" in items[9]["evidence_files"]
    assert audit["zenoproof_production_governance_gate"]["status"] == "production_candidate_only"
    assert items[10]["status"] == "devnet_complete"


def test_goal_completion_audit_cli_fails_closed_and_can_expect_blocked() -> None:
    blocked = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_goal_completion_audit.py",
            "--format",
            "json",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert blocked.returncode == 1
    receipt = json.loads(blocked.stdout)
    assert receipt["status"] == "blocked"

    expected = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_goal_completion_audit.py",
            "--format",
            "text",
            "--expect-blocked",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert expected.returncode == 0, expected.stdout + expected.stderr
    assert "status = blocked" in expected.stdout
    assert "goal_complete = false" in expected.stdout
