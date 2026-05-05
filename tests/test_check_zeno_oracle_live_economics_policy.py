from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_live_economics_policy import (
    check_policy,
    sample_policy,
    sample_replay,
)


ROOT = Path(__file__).resolve().parents[1]


def _event(replay: dict[str, object], event_type: str) -> dict[str, object]:
    events = replay["events"]
    assert isinstance(events, list)
    for event in events:
        assert isinstance(event, dict)
        if event.get("type") == event_type:
            return event
    raise AssertionError(f"missing event: {event_type}")


def test_live_economics_policy_accepts_sample_candidate() -> None:
    result = check_policy(sample_policy(), sample_replay())

    assert result["schema"] == "zenodex.oracle.live_economics_policy_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert "escrow_funding_receipt_not_verified_onchain" in result["go_live_blockers"]
    assert "does_not_claim_onchain_settlement_executed" in result["not_claimed"]


def test_live_economics_policy_rejects_fee_split_mismatch() -> None:
    replay = sample_replay()
    fee_split = _event(replay, "fee_split")
    fee_split["treasury_delta_e8"] = 6_000_000

    result = check_policy(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "fee_split_treasury_delta_e8_policy_mismatch" in result["errors"]
    assert "fee_split_total_policy_mismatch" in result["errors"]


def test_live_economics_policy_rejects_low_dispute_bond() -> None:
    replay = sample_replay()
    dispute = _event(replay, "open_dispute")
    dispute["dispute_bond_e8"] = 9_000_000

    result = check_policy(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "dispute_bond_below_policy" in result["errors"]


def test_live_economics_policy_rejects_slash_above_policy_cap() -> None:
    policy = sample_policy()
    policy["max_slash_bps"] = 4_000

    result = check_policy(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "policy_id_mismatch" in result["errors"]
    assert "reporter_slash_exceeds_policy:reporter.alpha" in result["errors"]


def test_live_economics_policy_rejects_early_withdrawal() -> None:
    replay = sample_replay()
    withdraw = _event(replay, "withdraw_bond")
    withdraw["epoch"] = 16

    result = check_policy(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "withdrawal_before_policy_delay" in result["errors"]


def test_live_economics_policy_rejects_disabled_live_settlement_and_bad_contracts() -> None:
    policy = sample_policy()
    policy["live_token_settlement_enabled"] = False
    policy["escrow_contract"] = "0xbad"
    policy["not_claimed"] = ["does_not_claim_reporter_honesty"]

    result = check_policy(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "live_token_settlement_enabled_must_be_true" in result["errors"]
    assert "escrow_contract_invalid" in result["errors"]
    assert "missing_not_claim:does_not_claim_escrow_funded_onchain" in result["errors"]


def test_live_economics_policy_rejects_unknown_policy_and_governance_fields() -> None:
    policy = copy.deepcopy(sample_policy())
    policy["surprise"] = True
    policy["governance"]["fast_path"] = True

    result = check_policy(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "unknown_policy_field:surprise" in result["errors"]
    assert "unknown_governance_field:fast_path" in result["errors"]


def test_live_economics_policy_cli_sample_and_require_live(tmp_path: Path) -> None:
    sample = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--sample-policy",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0
    policy_path = tmp_path / "live-economics-policy.json"
    policy_path.write_text(sample.stdout, encoding="utf-8")

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--policy",
            str(policy_path),
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--policy",
            str(policy_path),
            "--require-live",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_live.returncode == 1
    receipt = json.loads(require_live.stdout)
    assert receipt["status"] == "rejected"
    assert "go_live_blockers_present" in receipt["errors"]
