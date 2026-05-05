from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def test_zenodex_oracle_economic_security_chaos_rejects_all_mutants() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_economic_security_chaos.py"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["ok"] is True
    assert receipt["baseline_status"] == "accepted"
    assert receipt["case_count"] == 14
    assert receipt["rejected_case_count"] == 14
    assert receipt["failed_case_count"] == 0

    names = {case["name"] for case in receipt["cases"]}
    assert "extractable_above_notional_survives" in names
    assert "attack_cost_below_margin_survives" in names
    assert "reward_below_honest_cost_survives" in names
    assert "reporter_reward_budget_overspend_survives" in names
    assert "cheat_gain_above_extractable_survives" in names
    assert "weak_slash_deterrence_survives" in names
    assert "dispute_reward_budget_overspend_survives" in names
    assert "fee_split_overspend_survives" in names
    assert "hidden_mint_field_survives" in names
    assert "boolean_attack_cost_survives" in names
    assert "wrong_schema_survives" in names
    assert "zero_reporter_count_survives" in names
    assert "slash_fraction_over_100_percent_survives" in names
    assert "negative_fee_share_survives" in names


def test_zenodex_oracle_economic_security_chaos_writes_output_receipt(tmp_path: Path) -> None:
    output = tmp_path / "oracle-economic-security-chaos.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_economic_security_chaos.py",
            "--output",
            str(output),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    receipt = json.loads(output.read_text(encoding="utf-8"))
    assert receipt["schema"] == "zenodex.oracle.economic_security_chaos_replay.v1"
    assert receipt["ok"] is True
