from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_reporter_token_settlement_replay import (  # noqa: E402
    POLICY_SCHEMA,
    SETTLEMENT_SCHEMA,
    _content_hash,
    sample_hash,
    sample_settlement_replay,
)


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


def _minimal_policy(*, required_bond_e8: int, max_report_reward_e8: int) -> dict[str, Any]:
    policy = {
        "schema": POLICY_SCHEMA,
        "policy_id": "",
        "governance_receipt_id": sample_hash("oracle.false-report-penalty.policy"),
        "approved": True,
        "authority_id": "governance.oracle-council.v1",
        "effective_epoch": 0,
        "expires_epoch": 100,
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "required_reporter_bond_e8": required_bond_e8,
        "reporter_reward_fee_bps": 10_000,
        "treasury_fee_bps": 0,
        "burn_fee_bps": 0,
        "max_report_reward_e8": max_report_reward_e8,
        "max_slash_bps": 10_000,
        "withdrawal_requires_inactive": True,
        "withdrawal_requires_no_open_dispute": True,
    }
    policy["policy_id"] = _content_hash(policy)
    return policy


def _upheld_report_settlement(
    *,
    reward_e8: int,
    slash_e8: int,
    clawback_e8: int = 0,
    withdrawal_e8: int,
) -> dict[str, Any]:
    policy = _minimal_policy(required_bond_e8=1, max_report_reward_e8=reward_e8)
    policy_id = policy["policy_id"]
    query_id = sample_hash("oracle.false-report-penalty.query")
    report_id = sample_hash("oracle.false-report-penalty.report")
    dispute_id = sample_hash("oracle.false-report-penalty.dispute")
    value_hash = sample_hash("oracle.false-report-penalty.value")
    events: list[dict[str, Any]] = [
        {"type": "register_reporter", "epoch": 1, "reporter_id": "reporter.alpha"},
        {"type": "deposit_bond", "epoch": 2, "reporter_id": "reporter.alpha", "amount_e8": 1},
        {
            "type": "fee_split",
            "epoch": 3,
            "fee_paid_e8": reward_e8,
            "reporter_reward_pool_delta_e8": reward_e8,
            "treasury_delta_e8": 0,
            "burn_delta_e8": 0,
        },
        {
            "type": "submit_report",
            "epoch": 4,
            "reporter_id": "reporter.alpha",
            "report_id": report_id,
            "query_id": query_id,
            "value_hash": value_hash,
            "reward_e8": reward_e8,
        },
        {
            "type": "open_dispute",
            "epoch": 5,
            "dispute_id": dispute_id,
            "report_id": report_id,
            "challenger_id": "challenger.alpha",
            "dispute_bond_e8": 1,
        },
    ]
    if slash_e8:
        events.append(
            {
                "type": "slash_reporter",
                "epoch": 6,
                "dispute_id": dispute_id,
                "reporter_id": "reporter.alpha",
                "amount_e8": slash_e8,
            }
        )
    if clawback_e8:
        events.append(
            {
                "type": "clawback_report_reward",
                "epoch": 6,
                "dispute_id": dispute_id,
                "reporter_id": "reporter.alpha",
                "amount_e8": clawback_e8,
            }
        )
    events.extend(
        [
            {"type": "resolve_dispute", "epoch": 7, "dispute_id": dispute_id, "outcome": "upheld"},
            {"type": "unregister_reporter", "epoch": 8, "reporter_id": "reporter.alpha"},
        ]
    )
    if withdrawal_e8:
        events.append(
            {
                "type": "withdraw_bond",
                "epoch": 9,
                "reporter_id": "reporter.alpha",
                "amount_e8": withdrawal_e8,
            }
        )

    transfers = [
        {
            "debit": "reporter.alpha",
            "credit": "oracle.bond_escrow",
            "amount_e8": 1,
            "reason": "bond_deposit",
            "policy_id": policy_id,
        },
        {
            "debit": "consumer.fee_payer",
            "credit": "oracle.reporter_reward_pool",
            "amount_e8": reward_e8,
            "reason": "fee_split_reporter_reward_pool",
            "policy_id": policy_id,
        },
        {
            "debit": "oracle.reporter_reward_pool",
            "credit": "reporter.alpha",
            "amount_e8": reward_e8,
            "reason": "report_reward_payout",
            "policy_id": policy_id,
        },
    ]
    if slash_e8:
        transfers.append(
            {
                "debit": "oracle.bond_escrow",
                "credit": "oracle.slash_pool",
                "amount_e8": slash_e8,
                "reason": "reporter_slash",
                "policy_id": policy_id,
            }
        )
    if clawback_e8:
        transfers.append(
            {
                "debit": "reporter.alpha",
                "credit": "oracle.reporter_reward_pool",
                "amount_e8": clawback_e8,
                "reason": "report_reward_clawback",
                "policy_id": policy_id,
            }
        )
    if withdrawal_e8:
        transfers.append(
            {
                "debit": "oracle.bond_escrow",
                "credit": "reporter.alpha",
                "amount_e8": withdrawal_e8,
                "reason": "bond_withdrawal",
                "policy_id": policy_id,
            }
        )

    return {
        "schema": SETTLEMENT_SCHEMA,
        "policy": policy,
        "economics_replay": {
            "schema": "zenodex.oracle.reporter_economics_replay.v1",
            "query_id": query_id,
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "required_reporter_bond_e8": 1,
            "initial_reward_pool_e8": 0,
            "initial_dispute_reward_pool_e8": 0,
            "initial_treasury_balance_e8": 0,
            "initial_burn_balance_e8": 0,
            "events": events,
        },
        "initial_balances_e8": {
            "reporter.alpha": 1,
            "consumer.fee_payer": reward_e8,
            "oracle.bond_escrow": 0,
            "oracle.reporter_reward_pool": 0,
            "oracle.treasury": 0,
            "oracle.burn": 0,
            "oracle.slash_pool": 0,
            "oracle.dispute_reward_pool": 0,
        },
        "transfers": transfers,
    }


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
    assert result["report_reward_clawback_settled_e8"] == 0
    assert result["slash_settled_e8"] == 125_000_000_000
    assert result["withdrawal_settled_e8"] == 625_000_000_000
    assert result["upheld_report_count"] == 1
    assert result["upheld_report_reward_e8"] == 30_000_000
    assert result["upheld_report_penalty_covered_e8"] == 125_000_000_000
    assert result["upheld_report_penalty_coverage_ok"] is True
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


def test_reporter_token_settlement_rejects_upheld_report_without_penalty(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _upheld_report_settlement(reward_e8=1, slash_e8=0, withdrawal_e8=1),
    )

    assert code == 2
    assert result["source_replay_accepted"] is True
    assert result["token_conservation_ok"] is True
    assert result["upheld_report_count"] == 1
    assert result["upheld_report_reward_e8"] == 1
    assert result["upheld_report_penalty_covered_e8"] == 0
    assert result["upheld_report_penalty_coverage_ok"] is False
    assert any(error.startswith("upheld_report_penalty_below_reward:") for error in result["errors"])


def test_reporter_token_settlement_rejects_upheld_report_under_penalty(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _upheld_report_settlement(reward_e8=2, slash_e8=1, withdrawal_e8=0),
    )

    assert code == 2
    assert result["source_replay_accepted"] is True
    assert result["token_conservation_ok"] is True
    assert result["upheld_report_count"] == 1
    assert result["upheld_report_reward_e8"] == 2
    assert result["upheld_report_penalty_covered_e8"] == 1
    assert result["upheld_report_penalty_coverage_ok"] is False
    assert any(error.startswith("upheld_report_penalty_below_reward:") for error in result["errors"])


def test_reporter_token_settlement_accepts_upheld_report_when_penalty_covers_reward(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _upheld_report_settlement(reward_e8=1, slash_e8=1, withdrawal_e8=0),
    )

    assert code == 0
    assert result["status"] == "accepted"
    assert result["upheld_report_count"] == 1
    assert result["upheld_report_reward_e8"] == 1
    assert result["upheld_report_penalty_covered_e8"] == 1
    assert result["upheld_report_penalty_coverage_ok"] is True
    assert result["errors"] == []


def test_reporter_token_settlement_accepts_upheld_report_when_clawback_covers_reward(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _upheld_report_settlement(
            reward_e8=2,
            slash_e8=0,
            clawback_e8=2,
            withdrawal_e8=1,
        ),
    )

    assert code == 0
    assert result["status"] == "accepted"
    assert result["source_replay_accepted"] is True
    assert result["token_conservation_ok"] is True
    assert result["report_reward_settled_e8"] == 2
    assert result["report_reward_clawback_settled_e8"] == 2
    assert result["slash_settled_e8"] == 0
    assert result["withdrawal_settled_e8"] == 1
    assert result["upheld_report_count"] == 1
    assert result["upheld_report_reward_e8"] == 2
    assert result["upheld_report_penalty_covered_e8"] == 2
    assert result["upheld_report_penalty_coverage_ok"] is True
    assert result["final_balances_e8"]["oracle.reporter_reward_pool"] == 2
    assert result["errors"] == []


def test_reporter_token_settlement_rejects_missing_clawback_transfer(tmp_path: Path) -> None:
    replay = _upheld_report_settlement(
        reward_e8=2,
        slash_e8=0,
        clawback_e8=2,
        withdrawal_e8=1,
    )
    replay["transfers"] = [
        transfer
        for transfer in replay["transfers"]
        if transfer["reason"] != "report_reward_clawback"
    ]

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert result["source_replay_accepted"] is True
    assert result["token_conservation_ok"] is True
    assert result["upheld_report_penalty_coverage_ok"] is True
    assert "settlement_total_mismatch:report_reward_clawback:0!=2" in result["errors"]
    assert "report_reward_clawback_total_mismatch" in result["errors"]
    assert "reward_pool_final_balance_mismatch" in result["errors"]


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
