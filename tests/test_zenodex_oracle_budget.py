from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]


def _budget(**overrides: int | str | bool) -> dict:
    obj = {
        "schema": "zenodex.oracle.budget_transition.v1",
        "query_budget_remaining": 1_000,
        "query_reward_paid": 250,
        "reporter_bond_available": 2_000,
        "reporter_slash_paid": 100,
        "dispute_bond_available": 500,
        "dispute_slash_paid": 50,
        "fee_paid": 300,
        "reporter_fee_share": 120,
        "treasury_fee_share": 90,
        "burn_fee_share": 90,
    }
    obj.update(overrides)
    return obj


def _run_verify(tmp_path: Path, obj: dict) -> tuple[int, dict]:
    path = tmp_path / "budget.json"
    path.write_text(json.dumps(obj, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_oracle_budget_accepts_minimal_safe_transition(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["fee_paid"] == 300
    assert result["fee_spend_total"] == 300
    assert result["query_reward_paid"] == 250
    assert result["errors"] == []
    assert "does_not_claim_token_price_appreciation" in result["not_claimed"]


def test_oracle_budget_rejects_query_reward_over_budget(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget(query_reward_paid=1_001))
    assert code == 2
    assert "query_reward_exceeds_budget" in result["errors"]


def test_oracle_budget_rejects_reporter_slash_over_bond(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget(reporter_slash_paid=2_001))
    assert code == 2
    assert "reporter_slash_exceeds_bond" in result["errors"]


def test_oracle_budget_rejects_dispute_slash_over_bond(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget(dispute_slash_paid=501))
    assert code == 2
    assert "dispute_slash_exceeds_bond" in result["errors"]


def test_oracle_budget_rejects_fee_shares_over_fee_paid(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget(burn_fee_share=91))
    assert code == 2
    assert result["fee_spend_total"] == 301
    assert "fee_shares_exceed_fee_paid" in result["errors"]


def test_oracle_budget_rejects_unknown_field(tmp_path: Path) -> None:
    obj = _budget()
    obj["hidden_mint"] = 1
    code, result = _run_verify(tmp_path, obj)
    assert code == 2
    assert "unknown_budget_field:hidden_mint" in result["errors"]


def test_oracle_budget_rejects_negative_and_bool_amounts(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, _budget(query_reward_paid=-1, burn_fee_share=True))
    assert code == 2
    assert "query_reward_paid_must_be_int_ge_0" in result["errors"]
    assert "burn_fee_share_must_be_int_ge_0" in result["errors"]


def test_oracle_budget_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-budget.json"
    path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("budget_load_failed:budget_file_too_large:") for error in result["errors"])


def test_oracle_budget_sample_cli_emits_verifiable_transition(tmp_path: Path) -> None:
    path = tmp_path / "sample-budget.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_budget.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
    assert result["fee_spend_total"] == result["fee_paid"]
