from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_live_economics_policy import (
    check_policy,
    receipt_content_hash,
    sample_policy,
    sample_receipt_bundle,
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


def _receipt(bundle: dict[str, object], kind: str) -> dict[str, object]:
    receipts = bundle["receipts"]
    assert isinstance(receipts, list)
    for receipt in receipts:
        assert isinstance(receipt, dict)
        if receipt.get("kind") == kind:
            return receipt
    raise AssertionError(f"missing receipt: {kind}")


def _check(policy: dict[str, object], replay: dict[str, object]) -> dict[str, object]:
    return check_policy(policy, replay, sample_receipt_bundle(policy, replay))


def test_live_economics_policy_accepts_sample_candidate() -> None:
    policy = sample_policy()
    replay = sample_replay()
    result = check_policy(policy, replay, sample_receipt_bundle(policy, replay))

    assert result["schema"] == "zenodex.oracle.live_economics_policy_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert result["receipt_bundle_status"] == "accepted"
    assert result["settlement_controls"]["governance_execution_receipt"] == policy["governance_execution_receipt"]
    assert result["settlement_controls"]["settlement_execution_receipt"] == policy["settlement_execution_receipt"]
    assert "escrow_funding_receipt_not_verified_onchain" in result["go_live_blockers"]
    assert "settlement_execution_receipt_not_verified_onchain" in result["go_live_blockers"]
    assert "does_not_claim_onchain_settlement_executed" in result["not_claimed"]


def test_live_economics_policy_rejects_fee_split_mismatch() -> None:
    replay = sample_replay()
    fee_split = _event(replay, "fee_split")
    fee_split["treasury_delta_e8"] = 6_000_000

    result = _check(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "fee_split_treasury_delta_e8_policy_mismatch" in result["errors"]
    assert "fee_split_total_policy_mismatch" in result["errors"]


def test_live_economics_policy_rejects_low_dispute_bond() -> None:
    replay = sample_replay()
    dispute = _event(replay, "open_dispute")
    dispute["dispute_bond_e8"] = 9_000_000

    result = _check(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "dispute_bond_below_policy" in result["errors"]


def test_live_economics_policy_rejects_slash_above_policy_cap() -> None:
    policy = sample_policy()
    policy["max_slash_bps"] = 4_000

    result = _check(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "policy_id_mismatch" in result["errors"]
    assert "reporter_slash_exceeds_policy:reporter.alpha" in result["errors"]


def test_live_economics_policy_rejects_early_withdrawal() -> None:
    replay = sample_replay()
    withdraw = _event(replay, "withdraw_bond")
    withdraw["epoch"] = 16

    result = _check(sample_policy(), replay)

    assert result["status"] == "rejected"
    assert "withdrawal_before_policy_delay" in result["errors"]


def test_live_economics_policy_rejects_disabled_live_settlement_and_bad_contracts() -> None:
    policy = sample_policy()
    policy["live_token_settlement_enabled"] = False
    policy["escrow_contract"] = "0xbad"
    policy["not_claimed"] = ["does_not_claim_reporter_honesty"]

    result = _check(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "live_token_settlement_enabled_must_be_true" in result["errors"]
    assert "escrow_contract_invalid" in result["errors"]
    assert "missing_not_claim:does_not_claim_escrow_funded_onchain" in result["errors"]


def test_live_economics_policy_rejects_unknown_policy_and_governance_fields() -> None:
    policy = copy.deepcopy(sample_policy())
    policy["surprise"] = True
    policy["governance"]["fast_path"] = True

    result = _check(policy, sample_replay())

    assert result["status"] == "rejected"
    assert "unknown_policy_field:surprise" in result["errors"]
    assert "unknown_governance_field:fast_path" in result["errors"]


def test_live_economics_policy_rejects_missing_receipt_bundle() -> None:
    result = check_policy(sample_policy(), sample_replay(), None)

    assert result["status"] == "rejected"
    assert result["receipt_bundle_status"] == "rejected"
    assert "receipt_bundle_rejected" in result["errors"]
    assert "receipt:receipt_bundle_required" in result["errors"]


def test_live_economics_policy_rejects_governance_execution_before_timelock() -> None:
    policy = sample_policy()
    replay = sample_replay()
    bundle = sample_receipt_bundle(policy, replay)
    execution = _receipt(bundle, "governance_execution")
    payload = execution["payload"]
    assert isinstance(payload, dict)
    payload["executed_at_timestamp"] = int(payload["executable_after_timestamp"]) - 1
    execution["receipt_id"] = receipt_content_hash(execution)

    result = check_policy(policy, replay, bundle)

    assert result["status"] == "rejected"
    assert "receipt:governance_execution_before_timelock" in result["errors"]


def test_live_economics_policy_rejects_escrow_funding_below_replay_floor() -> None:
    policy = sample_policy()
    replay = sample_replay()
    bundle = sample_receipt_bundle(policy, replay)
    funding = _receipt(bundle, "escrow_funding")
    payload = funding["payload"]
    assert isinstance(payload, dict)
    payload["balance_e8"] = int(payload["required_escrow_floor_e8"]) - 1
    funding["receipt_id"] = receipt_content_hash(funding)

    result = check_policy(policy, replay, bundle)

    assert result["status"] == "rejected"
    assert "receipt:escrow_funding_below_replay_floor" in result["errors"]


def test_live_economics_policy_rejects_settlement_execution_total_drift() -> None:
    policy = sample_policy()
    replay = sample_replay()
    bundle = sample_receipt_bundle(policy, replay)
    settlement = _receipt(bundle, "settlement_execution")
    payload = settlement["payload"]
    assert isinstance(payload, dict)
    payload["report_reward_paid_e8"] = int(payload["report_reward_paid_e8"]) - 1
    settlement["receipt_id"] = receipt_content_hash(settlement)

    result = check_policy(policy, replay, bundle)

    assert result["status"] == "rejected"
    assert "receipt:settlement_execution_report_reward_paid_e8_mismatch" in result["errors"]


def test_live_economics_policy_rejects_settlement_execution_query_drift() -> None:
    policy = sample_policy()
    replay = sample_replay()
    bundle = sample_receipt_bundle(policy, replay)
    settlement = _receipt(bundle, "settlement_execution")
    payload = settlement["payload"]
    assert isinstance(payload, dict)
    payload["query_id"] = "sha256:" + "4" * 64
    settlement["receipt_id"] = receipt_content_hash(settlement)

    result = check_policy(policy, replay, bundle)

    assert result["status"] == "rejected"
    assert "receipt:settlement_execution_query_id_mismatch" in result["errors"]


def test_live_economics_policy_rejects_receipt_order_drift() -> None:
    policy = sample_policy()
    replay = sample_replay()
    bundle = sample_receipt_bundle(policy, replay)
    funding = _receipt(bundle, "escrow_funding")
    settlement = _receipt(bundle, "settlement_execution")
    settlement["block_number"] = int(funding["block_number"]) - 1
    settlement["receipt_id"] = receipt_content_hash(settlement)

    result = check_policy(policy, replay, bundle)

    assert result["status"] == "rejected"
    assert "receipt:receipt_order_invalid:escrow_funding->settlement_execution" in result["errors"]


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
    sample_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--sample-receipts",
            "--policy",
            str(policy_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample_receipts.returncode == 0
    receipts_path = tmp_path / "live-economics-receipts.json"
    receipts_path.write_text(sample_receipts.stdout, encoding="utf-8")

    missing_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--policy",
            str(policy_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing_receipts.returncode == 1
    missing_receipts_obj = json.loads(missing_receipts.stdout)
    assert "receipt:receipt_bundle_required" in missing_receipts_obj["errors"]

    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--policy",
            str(policy_path),
            "--receipts",
            str(receipts_path),
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
    assert "receipt_bundle_status = accepted" in accepted.stdout

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_live_economics_policy.py",
            "--policy",
            str(policy_path),
            "--receipts",
            str(receipts_path),
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
