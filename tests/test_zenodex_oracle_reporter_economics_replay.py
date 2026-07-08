from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_reporter_economics_replay import REPLAY_SCHEMA, sample_hash, sample_replay  # noqa: E402


def _run_verify(tmp_path: Path, replay: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    path = tmp_path / "reporter-economics-replay.json"
    path.write_text(json.dumps(replay, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_economics_replay.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def _single_report_clawback_replay(
    *,
    reward_e8: int,
    clawback_e8: int,
    outcome: str = "upheld",
    withdrawal_e8: int = 1,
) -> dict[str, Any]:
    query_id = sample_hash("oracle.reward-clawback.query")
    report_id = sample_hash("oracle.reward-clawback.report")
    dispute_id = sample_hash("oracle.reward-clawback.dispute")
    value_hash = sample_hash("oracle.reward-clawback.value")
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
        {
            "type": "clawback_report_reward",
            "epoch": 6,
            "dispute_id": dispute_id,
            "reporter_id": "reporter.alpha",
            "amount_e8": clawback_e8,
        },
        {"type": "resolve_dispute", "epoch": 7, "dispute_id": dispute_id, "outcome": outcome},
        {"type": "unregister_reporter", "epoch": 8, "reporter_id": "reporter.alpha"},
    ]
    if withdrawal_e8:
        events.append(
            {
                "type": "withdraw_bond",
                "epoch": 9,
                "reporter_id": "reporter.alpha",
                "amount_e8": withdrawal_e8,
            }
        )
    return {
        "schema": REPLAY_SCHEMA,
        "query_id": query_id,
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "required_reporter_bond_e8": 1,
        "initial_reward_pool_e8": 0,
        "initial_dispute_reward_pool_e8": 0,
        "initial_treasury_balance_e8": 0,
        "initial_burn_balance_e8": 0,
        "events": events,
    }


def test_reporter_economics_replay_accepts_sample(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_replay())

    assert code == 0
    assert result["status"] == "accepted"
    assert result["reporter_count"] == 3
    assert result["report_count"] == 3
    assert result["dispute_count"] == 1
    assert result["reward_pool_e8"] == 0
    assert result["dispute_reward_pool_e8"] == 10_000_000
    assert result["treasury_balance_e8"] == 7_000_000
    assert result["burn_balance_e8"] == 3_000_000
    assert result["total_bond_deposited_e8"] == 750_000_000_000
    assert result["bond_locked_e8"] == 0
    assert result["bond_conservation_ok"] is True
    assert result["total_rewards_paid_e8"] == 90_000_000
    assert result["total_rewards_clawed_back_e8"] == 0
    assert result["total_slashed_e8"] == 125_000_000_000
    assert result["total_withdrawn_e8"] == 625_000_000_000
    assert result["total_fees_paid_e8"] == 100_000_000
    assert result["errors"] == []


def test_reporter_economics_replay_rejects_reward_budget_overspend(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][6]["reporter_reward_pool_delta_e8"] = 89_999_999

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "reward_exceeds_query_budget" in result["errors"]


def test_reporter_economics_replay_rejects_fee_split_overspend(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][6]["burn_delta_e8"] += 1

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "fee_split_exceeds_fee_paid" in result["errors"]


def test_reporter_economics_replay_rejects_slash_over_bond(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][11]["amount_e8"] = 250_000_000_001

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "slash_exceeds_reporter_bond" in result["errors"]


def test_reporter_economics_replay_accepts_report_reward_clawback(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _single_report_clawback_replay(reward_e8=2, clawback_e8=2, withdrawal_e8=1),
    )

    assert code == 0
    assert result["status"] == "accepted"
    assert result["reward_pool_e8"] == 2
    assert result["total_rewards_paid_e8"] == 2
    assert result["total_rewards_clawed_back_e8"] == 2
    assert result["total_slashed_e8"] == 0
    assert result["total_withdrawn_e8"] == 1
    assert result["bond_conservation_ok"] is True
    assert result["errors"] == []


def test_reporter_economics_replay_rejects_clawback_over_reward(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _single_report_clawback_replay(reward_e8=2, clawback_e8=3, withdrawal_e8=1),
    )

    assert code == 2
    assert "clawback_exceeds_report_reward" in result["errors"]


def test_reporter_economics_replay_rejects_clawback_on_rejected_dispute(tmp_path: Path) -> None:
    code, result = _run_verify(
        tmp_path,
        _single_report_clawback_replay(
            reward_e8=2,
            clawback_e8=1,
            outcome="rejected",
            withdrawal_e8=1,
        ),
    )

    assert code == 2
    assert "rejected_dispute_cannot_have_slash_or_reward" in result["errors"]


def test_reporter_economics_replay_rejects_dispute_reward_budget_overspend(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][12]["amount_e8"] = 20_000_001

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "dispute_reward_exceeds_budget" in result["errors"]


def test_reporter_economics_replay_rejects_report_under_required_bond(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][3]["amount_e8"] = 249_999_999_999

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "report_submitted_under_required_bond" in result["errors"]


def test_reporter_economics_replay_rejects_withdraw_while_active(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][14] = {
        "type": "withdraw_bond",
        "epoch": 15,
        "reporter_id": "reporter.alpha",
        "amount_e8": 1,
    }

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "withdraw_while_reporter_active" in result["errors"]


def test_reporter_economics_replay_rejects_unknown_field(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][0]["admin_override"] = True

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "unknown_event_register_reporter_field:admin_override" in result["errors"]


def test_reporter_economics_replay_rejects_query_mismatch(tmp_path: Path) -> None:
    replay = sample_replay()
    replay["events"][7]["query_id"] = "sha256:" + "00" * 32

    code, result = _run_verify(tmp_path, replay)

    assert code == 2
    assert "report_query_mismatch" in result["errors"]


def test_reporter_economics_replay_sample_cli_emits_verifiable_replay(tmp_path: Path) -> None:
    path = tmp_path / "sample-reporter-economics-replay.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/zenodex_oracle_reporter_economics_replay.py",
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
        [sys.executable, "tools/zenodex_oracle_reporter_economics_replay.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"


def test_reporter_economics_replay_self_test_accepts() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_reporter_economics_replay.py", "self-test"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    result = json.loads(proc.stdout)
    assert result["status"] == "accepted"
