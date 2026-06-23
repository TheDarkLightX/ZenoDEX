from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_reporter_token_settlement_replay import sample_settlement_replay  # noqa: E402


def _run_verify(tmp_path: Path, replay: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    path = tmp_path / "reporter-token-settlement-replay.json"
    path.write_text(json.dumps(replay, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_token_settlement_replay.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_reporter_token_settlement_replay_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_settlement_replay())

    assert code == 0
    assert result["status"] == "accepted"
    assert result["governance_approved"] is True
    assert result["source_replay_accepted"] is True
    assert result["token_conservation_ok"] is True
    assert result["transfer_count"] == 14
    assert result["bond_deposit_settled_e8"] == 750_000_000_000
    assert result["report_reward_settled_e8"] == 90_000_000
    assert result["slash_settled_e8"] == 125_000_000_000
    assert result["withdrawal_settled_e8"] == 625_000_000_000
    assert result["fee_reward_pool_settled_e8"] == 90_000_000
    assert result["fee_treasury_settled_e8"] == 7_000_000
    assert result["fee_burn_settled_e8"] == 3_000_000
    assert result["final_balances_e8"]["oracle.bond_escrow"] == 0
    assert result["final_balances_e8"]["oracle.reporter_reward_pool"] == 0
    assert result["errors"] == []


def test_reporter_token_settlement_replay_rejects_unapproved_policy(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["policy"]["approved"] = False

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "policy_not_governance_approved" in result["errors"]
    assert "policy_content_hash_mismatch" in result["errors"]


def test_reporter_token_settlement_replay_rejects_missing_reward_payout(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["transfers"] = [
        transfer
        for transfer in replay["transfers"]
        if not (
            transfer["reason"] == "report_reward_payout"
            and transfer["credit"] == "reporter.gamma"
        )
    ]

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "settlement_total_mismatch:report_reward_payout:60000000!=90000000" in result["errors"]
    assert "report_reward_total_mismatch" in result["errors"]


def test_reporter_token_settlement_replay_rejects_slash_over_policy(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    for event in replay["economics_replay"]["events"]:
        if event["type"] == "slash_reporter":
            event["amount_e8"] = 125_000_000_001
            break
    for transfer in replay["transfers"]:
        if transfer["reason"] == "reporter_slash":
            transfer["amount_e8"] = 125_000_000_001
            break

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "economics_replay_not_accepted" in result["errors"]
    assert "slash_exceeds_governance_policy" in result["errors"]


def test_reporter_token_settlement_replay_rejects_policy_id_mismatch(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["transfers"][0]["policy_id"] = "sha256:" + "00" * 32

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "transfer_0_policy_id_mismatch" in result["errors"]


def test_reporter_token_settlement_replay_rejects_insufficient_balance(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["initial_balances_e8"]["consumer.fee_payer"] = 99_999_999

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "transfer_5_insufficient_balance:consumer.fee_payer" in result["errors"]


def test_reporter_token_settlement_replay_sample_cli_emits_verifiable_replay(tmp_path: Path) -> None:
    path = tmp_path / "sample-reporter-token-settlement-replay.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_reporter_token_settlement_replay.py",
            "sample",
            "--output",
            str(path),
        ],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_token_settlement_replay.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"


def test_reporter_token_settlement_replay_self_test_accepts() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_token_settlement_replay.py", "self-test"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    result = json.loads(proc.stdout)
    assert result["status"] == "accepted"


def test_reporter_token_settlement_replay_rejects_victim_funded_bond_deposit(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["initial_balances_e8"]["victim.whale"] = 750_000_000_000
    for reporter in ("reporter.alpha", "reporter.beta", "reporter.gamma"):
        replay["initial_balances_e8"][reporter] = 0
    for transfer in replay["transfers"]:
        if transfer["reason"] == "bond_deposit":
            transfer["debit"] = "victim.whale"

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "settlement_identity_mismatch:bond_deposit:victim.whale->oracle.bond_escrow:750000000000!=0" in result["errors"]
    assert "settlement_identity_mismatch:bond_deposit:reporter.alpha->oracle.bond_escrow:0!=250000000000" in result["errors"]
    assert "settlement_identity_mismatch:bond_deposit:reporter.beta->oracle.bond_escrow:0!=250000000000" in result["errors"]
    assert "settlement_identity_mismatch:bond_deposit:reporter.gamma->oracle.bond_escrow:0!=250000000000" in result["errors"]


def test_reporter_token_settlement_replay_rejects_attacker_credited_payouts(tmp_path: Path) -> None:
    replay = sample_settlement_replay()
    replay["initial_balances_e8"]["attacker.eve"] = 0
    for transfer in replay["transfers"]:
        if transfer["reason"] == "report_reward_payout" and transfer["credit"] == "reporter.alpha":
            transfer["credit"] = "attacker.eve"
        if transfer["reason"] == "bond_withdrawal" and transfer["credit"] == "reporter.alpha":
            transfer["credit"] = "attacker.eve"

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "settlement_identity_mismatch:report_reward_payout:oracle.reporter_reward_pool->attacker.eve:30000000!=0" in result["errors"]
    assert "settlement_identity_mismatch:report_reward_payout:oracle.reporter_reward_pool->reporter.alpha:0!=30000000" in result["errors"]
    assert "settlement_identity_mismatch:bond_withdrawal:oracle.bond_escrow->attacker.eve:125000000000!=0" in result["errors"]
    assert "settlement_identity_mismatch:bond_withdrawal:oracle.bond_escrow->reporter.alpha:0!=125000000000" in result["errors"]
