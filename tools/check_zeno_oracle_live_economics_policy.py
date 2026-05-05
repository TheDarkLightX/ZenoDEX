#!/usr/bin/env python3
"""Check a production-candidate live ZenoOracle reporter economics policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))

from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    sample_replay,
    verify_reporter_economics_replay,
)


POLICY_SCHEMA = "zenodex.oracle.live_economics_policy.v1"
REPORT_SCHEMA = "zenodex.oracle.live_economics_policy_check.v1"
BPS_DENOM = 10_000
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
SHA_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_escrow_funded_onchain",
    "does_not_claim_onchain_settlement_executed",
    "does_not_claim_governance_vote_executed",
    "does_not_claim_reporter_honesty",
    "does_not_claim_market_price_truth",
}
GO_LIVE_BLOCKERS = [
    "onchain_receipts_not_replayed_against_live_chain_state",
    "escrow_funding_receipt_not_verified_onchain",
    "governance_execution_not_verified_onchain",
    "settlement_contract_deployment_not_verified_by_this_checker",
    "public_reporting_soak_not_completed",
]
TOP_LEVEL_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "settlement_mode",
    "settlement_asset",
    "token_contract",
    "escrow_contract",
    "governance_contract",
    "governance",
    "governance_approval_receipt",
    "escrow_funding_receipt",
    "live_token_settlement_enabled",
    "required_reporter_bond_e8",
    "max_report_reward_e8",
    "min_dispute_bond_e8",
    "max_slash_bps",
    "withdrawal_delay_epochs",
    "fee_split_bps",
    "settlement_receipt_required",
    "not_claimed",
}
GOVERNANCE_KEYS = {
    "timelock_seconds",
    "dispute_window_epochs",
    "slash_delay_epochs",
    "emergency_pause_role",
}
FEE_SPLIT_KEYS = {"reporter_reward", "treasury", "burn"}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _is_address(value: Any) -> bool:
    return isinstance(value, str) and ADDRESS_RE.fullmatch(value) is not None


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _int_field(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int | None = None,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
    if maximum is not None and value > maximum:
        errors.append(f"{key}_above_max:{maximum}")
    return int(value)


def _obj_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any]:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return {}
    return value


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _bool_true(obj: Mapping[str, Any], key: str, errors: list[str]) -> None:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{key}_must_be_bool")
    elif value is not True:
        errors.append(f"{key}_must_be_true")


def _events_by_type(replay: Mapping[str, Any], event_type: str) -> list[Mapping[str, Any]]:
    raw = replay.get("events")
    if not isinstance(raw, list):
        return []
    return [event for event in raw if isinstance(event, Mapping) and event.get("type") == event_type]


def sample_policy() -> dict[str, Any]:
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_name": "zeno-oracle-live-economics-production-candidate-1",
        "settlement_mode": "production-candidate",
        "settlement_asset": "ZENO",
        "token_contract": "0x2222222222222222222222222222222222222222",
        "escrow_contract": "0x3333333333333333333333333333333333333333",
        "governance_contract": "0x4444444444444444444444444444444444444444",
        "governance": {
            "timelock_seconds": 172_800,
            "dispute_window_epochs": 32,
            "slash_delay_epochs": 2,
            "emergency_pause_role": "oracle-economics-guardian-1",
        },
        "governance_approval_receipt": _sha("zenodex.oracle.live_economics.governance_approval"),
        "escrow_funding_receipt": _sha("zenodex.oracle.live_economics.escrow_funding"),
        "live_token_settlement_enabled": True,
        "required_reporter_bond_e8": 250_000_000_000,
        "max_report_reward_e8": 30_000_000,
        "min_dispute_bond_e8": 10_000_000,
        "max_slash_bps": 5_000,
        "withdrawal_delay_epochs": 2,
        "fee_split_bps": {
            "reporter_reward": 9_000,
            "treasury": 700,
            "burn": 300,
        },
        "settlement_receipt_required": True,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def check_policy(policy: Mapping[str, Any], replay: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    _unknown_fields(policy, allowed=TOP_LEVEL_KEYS, label="policy", errors=errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    expected_policy_id = policy_content_hash(policy)
    if policy.get("policy_id") != expected_policy_id:
        errors.append("policy_id_mismatch")
    if policy.get("settlement_mode") != "production-candidate":
        errors.append("settlement_mode_must_be_production_candidate")
    if policy.get("settlement_asset") in {None, "", "DEV", "dev"}:
        errors.append("settlement_asset_must_be_production_asset")
    for key in ("token_contract", "escrow_contract", "governance_contract"):
        if not _is_address(policy.get(key)):
            errors.append(f"{key}_invalid")
    for key in ("governance_approval_receipt", "escrow_funding_receipt"):
        if not _is_sha(policy.get(key)):
            errors.append(f"{key}_must_be_sha256")
    _bool_true(policy, "live_token_settlement_enabled", errors)
    _bool_true(policy, "settlement_receipt_required", errors)

    governance = _obj_field(policy, "governance", errors)
    if governance:
        _unknown_fields(governance, allowed=GOVERNANCE_KEYS, label="governance", errors=errors)
        _int_field(governance, "timelock_seconds", errors, minimum=86_400)
        _int_field(governance, "dispute_window_epochs", errors, minimum=1)
        _int_field(governance, "slash_delay_epochs", errors, minimum=1)
        pause_role = governance.get("emergency_pause_role")
        if not isinstance(pause_role, str) or not pause_role.strip():
            errors.append("emergency_pause_role_required")

    required_bond = _int_field(policy, "required_reporter_bond_e8", errors, minimum=1)
    max_report_reward = _int_field(policy, "max_report_reward_e8", errors, minimum=1)
    min_dispute_bond = _int_field(policy, "min_dispute_bond_e8", errors, minimum=1)
    max_slash_bps = _int_field(policy, "max_slash_bps", errors, minimum=1, maximum=BPS_DENOM)
    withdrawal_delay = _int_field(policy, "withdrawal_delay_epochs", errors, minimum=1)
    fee_split = _obj_field(policy, "fee_split_bps", errors)
    if fee_split:
        _unknown_fields(fee_split, allowed=FEE_SPLIT_KEYS, label="fee_split_bps", errors=errors)
    reporter_bps = _int_field(fee_split, "reporter_reward", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    treasury_bps = _int_field(fee_split, "treasury", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    burn_bps = _int_field(fee_split, "burn", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    if None not in (reporter_bps, treasury_bps, burn_bps):
        if int(reporter_bps) + int(treasury_bps) + int(burn_bps) != BPS_DENOM:
            errors.append("fee_split_bps_must_sum_to_10000")

    not_claimed = policy.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_not_claim:{item}" for item in sorted(REQUIRED_NOT_CLAIMS - values))

    replay_result = verify_reporter_economics_replay(replay).to_json_obj()
    if replay_result["status"] != "accepted":
        errors.append("reporter_economics_replay_rejected")
        errors.extend(f"replay:{error}" for error in replay_result.get("errors", []))

    if required_bond is not None and replay.get("required_reporter_bond_e8") != required_bond:
        errors.append("required_reporter_bond_mismatch")

    for event in _events_by_type(replay, "fee_split"):
        fee_paid = event.get("fee_paid_e8")
        if not isinstance(fee_paid, int) or isinstance(fee_paid, bool) or fee_paid <= 0:
            errors.append("fee_split_fee_paid_invalid")
            continue
        if None in (reporter_bps, treasury_bps, burn_bps):
            continue
        expected = {
            "reporter_reward_pool_delta_e8": int(reporter_bps),
            "treasury_delta_e8": int(treasury_bps),
            "burn_delta_e8": int(burn_bps),
        }
        total_delta = 0
        for key, bps in expected.items():
            actual = event.get(key)
            if not isinstance(actual, int) or isinstance(actual, bool):
                errors.append(f"fee_split_{key}_invalid")
                continue
            total_delta += int(actual)
            if int(actual) * BPS_DENOM != fee_paid * bps:
                errors.append(f"fee_split_{key}_policy_mismatch")
        if total_delta != fee_paid:
            errors.append("fee_split_total_policy_mismatch")

    for event in _events_by_type(replay, "submit_report"):
        reward = event.get("reward_e8")
        if isinstance(max_report_reward, int) and (
            not isinstance(reward, int) or isinstance(reward, bool) or reward > max_report_reward
        ):
            errors.append("report_reward_exceeds_policy")

    for event in _events_by_type(replay, "open_dispute"):
        bond = event.get("dispute_bond_e8")
        if isinstance(min_dispute_bond, int) and (
            not isinstance(bond, int) or isinstance(bond, bool) or bond < min_dispute_bond
        ):
            errors.append("dispute_bond_below_policy")

    slash_by_reporter: dict[str, int] = {}
    unregister_epoch: dict[str, int] = {}
    for event in replay.get("events", []) if isinstance(replay.get("events"), list) else []:
        if not isinstance(event, Mapping):
            continue
        if event.get("type") == "slash_reporter":
            reporter_id = str(event.get("reporter_id", ""))
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                slash_by_reporter[reporter_id] = slash_by_reporter.get(reporter_id, 0) + int(amount)
        if event.get("type") == "unregister_reporter":
            reporter_id = str(event.get("reporter_id", ""))
            epoch = event.get("epoch")
            if isinstance(epoch, int) and not isinstance(epoch, bool):
                unregister_epoch[reporter_id] = int(epoch)
        if event.get("type") == "withdraw_bond":
            reporter_id = str(event.get("reporter_id", ""))
            epoch = event.get("epoch")
            if isinstance(withdrawal_delay, int) and isinstance(epoch, int) and not isinstance(epoch, bool):
                if reporter_id not in unregister_epoch:
                    errors.append("withdraw_without_unregister")
                elif int(epoch) - int(unregister_epoch[reporter_id]) < withdrawal_delay:
                    errors.append("withdrawal_before_policy_delay")

    if isinstance(max_slash_bps, int) and isinstance(required_bond, int):
        max_slash = (required_bond * max_slash_bps) // BPS_DENOM
        for reporter_id, amount in slash_by_reporter.items():
            if amount > max_slash:
                errors.append(f"reporter_slash_exceeds_policy:{reporter_id}")

    status = "accepted" if not errors else "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "policy_id": expected_policy_id,
        "replay_status": replay_result["status"],
        "error_count": len(errors),
        "errors": errors,
        "settlement_controls": {
            "live_token_settlement_enabled": bool(policy.get("live_token_settlement_enabled") is True),
            "settlement_receipt_required": bool(policy.get("settlement_receipt_required") is True),
            "governance_approval_receipt": policy.get("governance_approval_receipt"),
            "escrow_funding_receipt": policy.get("escrow_funding_receipt"),
        },
        "go_live_blockers": list(GO_LIVE_BLOCKERS),
        "deployment_blockers": list(GO_LIVE_BLOCKERS),
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, help="policy JSON; defaults to built-in sample policy")
    parser.add_argument("--replay", type=Path, help="reporter economics replay JSON; defaults to built-in sample replay")
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.sample_policy:
        print(json.dumps(sample_policy(), indent=2, sort_keys=True))
        return 0
    policy = _load_json(args.policy) if args.policy else sample_policy()
    replay = _load_json(args.replay) if args.replay else sample_replay()
    result = check_policy(policy, replay)
    if args.require_live and result["go_live_blockers"]:
        result = dict(result)
        result["ok"] = False
        result["status"] = "rejected"
        result["errors"] = [*result["errors"], "go_live_blockers_present"]
        result["error_count"] = len(result["errors"])
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"replay_status = {result['replay_status']}")
        print(f"error_count = {result['error_count']}")
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"policy_id = {result['policy_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
