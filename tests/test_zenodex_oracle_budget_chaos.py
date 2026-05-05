from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_budget_chaos_replay_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget_chaos.py"],
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
    assert "query_reward_exceeds_remaining_budget" in names
    assert "query_reward_from_zero_budget" in names
    assert "reporter_slash_exceeds_available_bond" in names
    assert "dispute_slash_exceeds_available_bond" in names
    assert "fee_split_spends_more_than_fee" in names
    assert "fee_split_spends_from_zero_fee" in names
    assert "hidden_mint_field_survives" in names
    assert "negative_reward_amount_survives" in names
    assert "boolean_burn_share_survives" in names
    assert "missing_fee_share_survives" in names
    assert "wrong_schema_survives" in names
    assert "string_budget_amount_survives" in names


def test_zenodex_oracle_budget_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-budget-chaos.json"
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget_chaos.py", "--output", str(output)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.budget_chaos_replay.v1"
    assert receipt["ok"] is True
