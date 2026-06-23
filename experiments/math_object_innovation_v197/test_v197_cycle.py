#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def rows_by_id(report: dict) -> dict[str, dict]:
    return {row["quest_id"]: row for row in report["quest_rows"]}


def test_proof_gated_gamification_counts_and_audit() -> None:
    report = load_report()

    assert report["quest_count"] == 12
    assert report["accepted_count"] == 6
    assert report["accepted_token_reward_count"] == 5
    assert report["accepted_xp_only_count"] == 1
    assert report["rejected_count"] == 6
    assert report["model_audit"]["total_gamification_budget_invariant_failures"] == 0


def test_accepted_token_rewards_are_below_all_caps_and_have_gates() -> None:
    report = load_report()

    for row in report["quest_rows"]:
        if row["status"] != "accepted_token_reward":
            continue
        assert row["proof_gates_ok"] is True
        assert row["reward_tokens"] <= row["meet_cap"]
        assert row["reward_tokens"] <= row["verified_value"]
        assert row["reward_tokens"] <= row["budget_cap"]
        assert row["reward_tokens"] <= row["sybil_adjusted_cap"]
        assert row["reward_tokens"] <= row["treasury_cap"]
        assert row["net_verified_surplus"] >= 0


def test_xp_only_path_carries_no_token_reward() -> None:
    rows = rows_by_id(load_report())

    xp = rows["xp_only_learning_path"]
    assert xp["accepted"] is True
    assert xp["status"] == "accepted_xp_only"
    assert xp["reward_tokens"] == 0


def test_named_bad_quests_reject_for_expected_reason() -> None:
    rows = rows_by_id(load_report())

    assert rows["social_hype_no_value_bad"]["accepted"] is False
    assert "reward_exceeds_meet_cap" in rows["social_hype_no_value_bad"]["failures"]

    assert rows["wash_loop_engagement_bad"]["accepted"] is False
    assert "anti_sybil_missing" in rows["wash_loop_engagement_bad"]["failures"]

    assert rows["missing_proof_bad"]["accepted"] is False
    assert "proof_missing" in rows["missing_proof_bad"]["failures"]

    assert rows["over_budget_bad"]["accepted"] is False
    assert "reward_exceeds_meet_cap" in rows["over_budget_bad"]["failures"]

    assert rows["over_sybil_adjusted_bad"]["accepted"] is False
    assert "reward_exceeds_meet_cap" in rows["over_sybil_adjusted_bad"]["failures"]

    assert rows["stale_receipt_scope_bad"]["accepted"] is False
    assert "receipt_scope_missing" in rows["stale_receipt_scope_bad"]["failures"]
