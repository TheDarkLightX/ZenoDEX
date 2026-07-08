#!/usr/bin/env python3
"""Replay a first-shell ZenoOracle reporter economics event ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPLAY_SCHEMA = "zenodex.oracle.reporter_economics_replay.v1"
RESULT_SCHEMA = "zenodex.oracle.reporter_economics_replay_result.v1"
MAX_REPLAY_BYTES = 500_000
MAX_EVENTS = 256
MAX_AMOUNT = 10**30
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
TOP_LEVEL_KEYS = {
    "schema",
    "query_id",
    "consumer_module",
    "action_kind",
    "required_reporter_bond_e8",
    "initial_reward_pool_e8",
    "initial_dispute_reward_pool_e8",
    "initial_treasury_balance_e8",
    "initial_burn_balance_e8",
    "events",
}
EVENT_KEYS_BY_TYPE = {
    "register_reporter": {"type", "epoch", "reporter_id"},
    "deposit_bond": {"type", "epoch", "reporter_id", "amount_e8"},
    "fee_split": {
        "type",
        "epoch",
        "fee_paid_e8",
        "reporter_reward_pool_delta_e8",
        "treasury_delta_e8",
        "burn_delta_e8",
    },
    "submit_report": {
        "type",
        "epoch",
        "reporter_id",
        "report_id",
        "query_id",
        "value_hash",
        "reward_e8",
    },
    "open_dispute": {
        "type",
        "epoch",
        "dispute_id",
        "report_id",
        "challenger_id",
        "dispute_bond_e8",
    },
    "slash_reporter": {"type", "epoch", "dispute_id", "reporter_id", "amount_e8"},
    "clawback_report_reward": {"type", "epoch", "dispute_id", "reporter_id", "amount_e8"},
    "pay_dispute_reward": {"type", "epoch", "dispute_id", "recipient_id", "amount_e8"},
    "resolve_dispute": {"type", "epoch", "dispute_id", "outcome"},
    "unregister_reporter": {"type", "epoch", "reporter_id"},
    "withdraw_bond": {"type", "epoch", "reporter_id", "amount_e8"},
}
DISPUTE_OUTCOMES = {"upheld", "rejected"}
NOT_CLAIMED = [
    "does_not_claim_production_token_settlement",
    "does_not_claim_reporter_honesty",
    "does_not_claim_oracle_truth",
    "does_not_claim_onchain_governance_live",
]


@dataclass(frozen=True)
class ReporterEconomicsReplayResult:
    status: str
    errors: list[str]
    reporter_count: int | None = None
    report_count: int | None = None
    dispute_count: int | None = None
    reward_pool_e8: int | None = None
    dispute_reward_pool_e8: int | None = None
    treasury_balance_e8: int | None = None
    burn_balance_e8: int | None = None
    total_bond_deposited_e8: int | None = None
    bond_locked_e8: int | None = None
    bond_conservation_ok: bool | None = None
    total_rewards_paid_e8: int | None = None
    total_rewards_clawed_back_e8: int | None = None
    total_slashed_e8: int | None = None
    total_withdrawn_e8: int | None = None
    total_fees_paid_e8: int | None = None
    last_epoch: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "reporter_count": self.reporter_count,
            "report_count": self.report_count,
            "dispute_count": self.dispute_count,
            "reward_pool_e8": self.reward_pool_e8,
            "dispute_reward_pool_e8": self.dispute_reward_pool_e8,
            "treasury_balance_e8": self.treasury_balance_e8,
            "burn_balance_e8": self.burn_balance_e8,
            "total_bond_deposited_e8": self.total_bond_deposited_e8,
            "bond_locked_e8": self.bond_locked_e8,
            "bond_conservation_ok": self.bond_conservation_ok,
            "total_rewards_paid_e8": self.total_rewards_paid_e8,
            "total_rewards_clawed_back_e8": self.total_rewards_clawed_back_e8,
            "total_slashed_e8": self.total_slashed_e8,
            "total_withdrawn_e8": self.total_withdrawn_e8,
            "total_fees_paid_e8": self.total_fees_paid_e8,
            "last_epoch": self.last_epoch,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_replay() -> dict[str, Any]:
    query_id = sample_hash("zenodex.oracle.query.perps.index_price_e8")
    reports = {
        "reporter.alpha": sample_hash("zenodex.oracle.report.alpha"),
        "reporter.beta": sample_hash("zenodex.oracle.report.beta"),
        "reporter.gamma": sample_hash("zenodex.oracle.report.gamma"),
    }
    dispute_id = sample_hash("zenodex.oracle.dispute.alpha")
    value_hash = sample_hash("zenodex.oracle.value.perps.index.100")
    events: list[dict[str, Any]] = []
    for epoch, reporter_id in enumerate(sorted(reports), start=1):
        events.append({"type": "register_reporter", "epoch": epoch, "reporter_id": reporter_id})
    for epoch, reporter_id in enumerate(sorted(reports), start=4):
        events.append(
            {
                "type": "deposit_bond",
                "epoch": epoch,
                "reporter_id": reporter_id,
                "amount_e8": 250_000_000_000,
            }
        )
    events.append(
        {
            "type": "fee_split",
            "epoch": 7,
            "fee_paid_e8": 100_000_000,
            "reporter_reward_pool_delta_e8": 90_000_000,
            "treasury_delta_e8": 7_000_000,
            "burn_delta_e8": 3_000_000,
        }
    )
    for epoch, reporter_id in enumerate(sorted(reports), start=8):
        events.append(
            {
                "type": "submit_report",
                "epoch": epoch,
                "reporter_id": reporter_id,
                "report_id": reports[reporter_id],
                "query_id": query_id,
                "value_hash": value_hash,
                "reward_e8": 30_000_000,
            }
        )
    events.extend(
        [
            {
                "type": "open_dispute",
                "epoch": 11,
                "dispute_id": dispute_id,
                "report_id": reports["reporter.alpha"],
                "challenger_id": "challenger.sample",
                "dispute_bond_e8": 10_000_000,
            },
            {
                "type": "slash_reporter",
                "epoch": 12,
                "dispute_id": dispute_id,
                "reporter_id": "reporter.alpha",
                "amount_e8": 125_000_000_000,
            },
            {
                "type": "pay_dispute_reward",
                "epoch": 13,
                "dispute_id": dispute_id,
                "recipient_id": "challenger.sample",
                "amount_e8": 10_000_000,
            },
            {"type": "resolve_dispute", "epoch": 14, "dispute_id": dispute_id, "outcome": "upheld"},
        ]
    )
    for epoch, reporter_id in enumerate(sorted(reports), start=15):
        events.append({"type": "unregister_reporter", "epoch": epoch, "reporter_id": reporter_id})
    events.extend(
        [
            {"type": "withdraw_bond", "epoch": 18, "reporter_id": "reporter.alpha", "amount_e8": 125_000_000_000},
            {"type": "withdraw_bond", "epoch": 19, "reporter_id": "reporter.beta", "amount_e8": 250_000_000_000},
            {"type": "withdraw_bond", "epoch": 20, "reporter_id": "reporter.gamma", "amount_e8": 250_000_000_000},
        ]
    )
    return {
        "schema": REPLAY_SCHEMA,
        "query_id": query_id,
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "required_reporter_bond_e8": 250_000_000_000,
        "initial_reward_pool_e8": 0,
        "initial_dispute_reward_pool_e8": 20_000_000,
        "initial_treasury_balance_e8": 0,
        "initial_burn_balance_e8": 0,
        "events": events,
    }


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _amount(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_AMOUNT:
        errors.append(f"{key}_must_be_int_between_0_and_{MAX_AMOUNT}")
        return None
    return int(value)


def _epoch(obj: Mapping[str, Any], errors: list[str]) -> int | None:
    value = obj.get("epoch")
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append("epoch_must_be_int_ge_0")
        return None
    return int(value)


def _events(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("events")
    if not isinstance(raw, list):
        errors.append("events_must_be_list")
        return []
    if len(raw) > MAX_EVENTS:
        errors.append(f"events_exceed_max:{len(raw)}>{MAX_EVENTS}")
    events: list[Mapping[str, Any]] = []
    for pos, event in enumerate(raw[:MAX_EVENTS]):
        if not isinstance(event, Mapping):
            errors.append(f"event_{pos}_must_be_object")
            continue
        events.append(event)
    return events


def verify_reporter_economics_replay(obj: Mapping[str, Any]) -> ReporterEconomicsReplayResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="economics_replay", errors=errors)
    if obj.get("schema") != REPLAY_SCHEMA:
        errors.append("economics_replay_schema_mismatch")
    query_id = _hash(obj, "query_id", errors)
    _token(obj, "consumer_module", errors)
    _token(obj, "action_kind", errors)
    required_bond = _amount(obj, "required_reporter_bond_e8", errors)
    reward_pool = _amount(obj, "initial_reward_pool_e8", errors)
    dispute_reward_pool = _amount(obj, "initial_dispute_reward_pool_e8", errors)
    treasury_balance = _amount(obj, "initial_treasury_balance_e8", errors)
    burn_balance = _amount(obj, "initial_burn_balance_e8", errors)
    events = _events(obj, errors)

    reward_pool = int(reward_pool or 0)
    dispute_reward_pool = int(dispute_reward_pool or 0)
    treasury_balance = int(treasury_balance or 0)
    burn_balance = int(burn_balance or 0)
    required_bond = int(required_bond or 0)

    reporters: dict[str, dict[str, Any]] = {}
    reports: dict[str, dict[str, Any]] = {}
    disputes: dict[str, dict[str, Any]] = {}
    total_bond_deposited = 0
    total_rewards_paid = 0
    total_rewards_clawed_back = 0
    total_slashed = 0
    total_withdrawn = 0
    total_fees_paid = 0
    last_epoch: int | None = None

    for pos, event in enumerate(events):
        event_type = event.get("type")
        if not isinstance(event_type, str):
            errors.append(f"event_{pos}_type_must_be_string")
            continue
        allowed = EVENT_KEYS_BY_TYPE.get(event_type)
        if allowed is None:
            errors.append(f"unsupported_event_type:{event_type}")
            continue
        _unknown_fields(event, allowed=allowed, label=f"event_{event_type}", errors=errors)

        epoch = _epoch(event, errors)
        if epoch is not None:
            if last_epoch is not None and epoch < last_epoch:
                errors.append(f"event_epoch_regression:{pos}")
            last_epoch = epoch if last_epoch is None else max(last_epoch, epoch)

        if event_type == "register_reporter":
            reporter_id = _token(event, "reporter_id", errors)
            if reporter_id is None:
                continue
            reporter = reporters.setdefault(
                reporter_id,
                {"active": False, "bond": 0, "registered": False},
            )
            if reporter["active"]:
                errors.append("reporter_already_active")
            if reporter["registered"]:
                errors.append("reporter_duplicate_registration")
            reporter["active"] = True
            reporter["registered"] = True
        elif event_type == "deposit_bond":
            reporter_id = _token(event, "reporter_id", errors)
            amount = _amount(event, "amount_e8", errors)
            reporter = reporters.get(reporter_id or "")
            if reporter is None:
                errors.append("bond_deposit_for_unknown_reporter")
            elif amount is not None:
                reporter["bond"] += amount
                total_bond_deposited += amount
        elif event_type == "fee_split":
            fee_paid = _amount(event, "fee_paid_e8", errors)
            reporter_delta = _amount(event, "reporter_reward_pool_delta_e8", errors)
            treasury_delta = _amount(event, "treasury_delta_e8", errors)
            burn_delta = _amount(event, "burn_delta_e8", errors)
            if None not in (fee_paid, reporter_delta, treasury_delta, burn_delta):
                split_total = int(reporter_delta) + int(treasury_delta) + int(burn_delta)
                if split_total > int(fee_paid):
                    errors.append("fee_split_exceeds_fee_paid")
                else:
                    reward_pool += int(reporter_delta)
                    treasury_balance += int(treasury_delta)
                    burn_balance += int(burn_delta)
                    total_fees_paid += int(fee_paid)
        elif event_type == "submit_report":
            reporter_id = _token(event, "reporter_id", errors)
            report_id = _hash(event, "report_id", errors)
            event_query_id = _hash(event, "query_id", errors)
            _hash(event, "value_hash", errors)
            reward = _amount(event, "reward_e8", errors)
            reporter = reporters.get(reporter_id or "")
            if reporter is None or not reporter["active"]:
                errors.append("report_submitted_by_inactive_reporter")
            elif int(reporter["bond"]) < required_bond:
                errors.append("report_submitted_under_required_bond")
            if query_id is not None and event_query_id is not None and event_query_id != query_id:
                errors.append("report_query_mismatch")
            if report_id is not None:
                if report_id in reports:
                    errors.append(f"duplicate_report_id:{report_id}")
                elif reporter_id is not None:
                    reports[report_id] = {
                        "reporter_id": reporter_id,
                        "reward_e8": int(reward or 0),
                        "clawed_back_e8": 0,
                    }
            if reward is not None:
                if reward > reward_pool:
                    errors.append("reward_exceeds_query_budget")
                else:
                    reward_pool -= reward
                    total_rewards_paid += reward
        elif event_type == "open_dispute":
            dispute_id = _hash(event, "dispute_id", errors)
            report_id = _hash(event, "report_id", errors)
            _token(event, "challenger_id", errors)
            dispute_bond = _amount(event, "dispute_bond_e8", errors)
            if report_id is not None and report_id not in reports:
                errors.append("dispute_for_unknown_report")
            if dispute_bond == 0:
                errors.append("dispute_bond_required")
            if dispute_id is not None:
                if dispute_id in disputes:
                    errors.append(f"duplicate_dispute_id:{dispute_id}")
                else:
                    disputes[dispute_id] = {
                        "open": True,
                        "resolved": False,
                        "report_id": report_id,
                        "slashed": False,
                        "reward_clawed_back_e8": 0,
                        "reward_paid": False,
                    }
        elif event_type == "slash_reporter":
            dispute_id = _hash(event, "dispute_id", errors)
            reporter_id = _token(event, "reporter_id", errors)
            amount = _amount(event, "amount_e8", errors)
            dispute = disputes.get(dispute_id or "")
            reporter = reporters.get(reporter_id or "")
            if dispute is None or not dispute["open"] or dispute["resolved"]:
                errors.append("slash_without_open_dispute")
            elif dispute["slashed"]:
                errors.append("dispute_already_slashed")
            elif reporter_id is not None:
                report = reports.get(str(dispute.get("report_id")))
                if report is None or report.get("reporter_id") != reporter_id:
                    errors.append("slash_reporter_mismatch")
            if reporter is None:
                errors.append("slash_unknown_reporter")
            elif amount is not None:
                if amount == 0:
                    errors.append("slash_amount_required")
                elif amount > int(reporter["bond"]):
                    errors.append("slash_exceeds_reporter_bond")
                elif dispute is not None and dispute["open"] and not dispute["resolved"]:
                    reporter["bond"] -= amount
                    dispute["slashed"] = True
                    total_slashed += amount
        elif event_type == "clawback_report_reward":
            dispute_id = _hash(event, "dispute_id", errors)
            reporter_id = _token(event, "reporter_id", errors)
            amount = _amount(event, "amount_e8", errors)
            dispute = disputes.get(dispute_id or "")
            reporter = reporters.get(reporter_id or "")
            report = reports.get(str(dispute.get("report_id"))) if dispute is not None else None
            if dispute is None or not dispute["open"] or dispute["resolved"]:
                errors.append("clawback_without_open_dispute")
            elif reporter_id is not None and (report is None or report.get("reporter_id") != reporter_id):
                errors.append("clawback_reporter_mismatch")
            if reporter is None:
                errors.append("clawback_unknown_reporter")
            elif amount is not None:
                if amount == 0:
                    errors.append("clawback_amount_required")
                elif report is None:
                    errors.append("clawback_without_report")
                else:
                    remaining_reward = int(report.get("reward_e8", 0)) - int(report.get("clawed_back_e8", 0))
                    if amount > remaining_reward:
                        errors.append("clawback_exceeds_report_reward")
                    elif dispute is not None and dispute["open"] and not dispute["resolved"]:
                        report["clawed_back_e8"] = int(report.get("clawed_back_e8", 0)) + amount
                        dispute["reward_clawed_back_e8"] = int(dispute.get("reward_clawed_back_e8", 0)) + amount
                        reward_pool += amount
                        total_rewards_clawed_back += amount
        elif event_type == "pay_dispute_reward":
            dispute_id = _hash(event, "dispute_id", errors)
            _token(event, "recipient_id", errors)
            amount = _amount(event, "amount_e8", errors)
            dispute = disputes.get(dispute_id or "")
            if dispute is None or not dispute["open"] or dispute["resolved"]:
                errors.append("dispute_reward_without_open_dispute")
            elif dispute["reward_paid"]:
                errors.append("dispute_reward_already_paid")
            if amount is not None:
                if amount == 0:
                    errors.append("dispute_reward_amount_required")
                elif amount > dispute_reward_pool:
                    errors.append("dispute_reward_exceeds_budget")
                elif dispute is not None and dispute["open"] and not dispute["resolved"]:
                    dispute_reward_pool -= amount
                    dispute["reward_paid"] = True
        elif event_type == "resolve_dispute":
            dispute_id = _hash(event, "dispute_id", errors)
            outcome = event.get("outcome")
            if outcome not in DISPUTE_OUTCOMES:
                errors.append("dispute_outcome_invalid")
            dispute = disputes.get(dispute_id or "")
            if dispute is None or not dispute["open"] or dispute["resolved"]:
                errors.append("resolve_unknown_or_closed_dispute")
            else:
                if outcome == "rejected" and (
                    dispute["slashed"]
                    or dispute["reward_paid"]
                    or int(dispute.get("reward_clawed_back_e8", 0)) > 0
                ):
                    errors.append("rejected_dispute_cannot_have_slash_or_reward")
                dispute["open"] = False
                dispute["resolved"] = True
        elif event_type == "unregister_reporter":
            reporter_id = _token(event, "reporter_id", errors)
            reporter = reporters.get(reporter_id or "")
            if reporter is None or not reporter["active"]:
                errors.append("unregister_inactive_reporter")
            elif _reporter_has_open_dispute(reporter_id, reports, disputes):
                errors.append("unregister_with_open_dispute")
            else:
                reporter["active"] = False
        elif event_type == "withdraw_bond":
            reporter_id = _token(event, "reporter_id", errors)
            amount = _amount(event, "amount_e8", errors)
            reporter = reporters.get(reporter_id or "")
            if reporter is None:
                errors.append("withdraw_unknown_reporter")
            elif reporter["active"]:
                errors.append("withdraw_while_reporter_active")
            elif _reporter_has_open_dispute(reporter_id, reports, disputes):
                errors.append("withdraw_with_open_dispute")
            elif amount is not None:
                if amount == 0:
                    errors.append("withdraw_amount_required")
                elif amount > int(reporter["bond"]):
                    errors.append("withdraw_exceeds_bond")
                else:
                    reporter["bond"] -= amount
                    total_withdrawn += amount

    bond_locked = sum(int(reporter["bond"]) for reporter in reporters.values())
    bond_conservation_ok = total_bond_deposited == total_slashed + total_withdrawn + bond_locked
    if not bond_conservation_ok:
        errors.append("bond_conservation_mismatch")

    return ReporterEconomicsReplayResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        reporter_count=len(reporters),
        report_count=len(reports),
        dispute_count=len(disputes),
        reward_pool_e8=reward_pool,
        dispute_reward_pool_e8=dispute_reward_pool,
        treasury_balance_e8=treasury_balance,
        burn_balance_e8=burn_balance,
        total_bond_deposited_e8=total_bond_deposited,
        bond_locked_e8=bond_locked,
        bond_conservation_ok=bond_conservation_ok,
        total_rewards_paid_e8=total_rewards_paid,
        total_rewards_clawed_back_e8=total_rewards_clawed_back,
        total_slashed_e8=total_slashed,
        total_withdrawn_e8=total_withdrawn,
        total_fees_paid_e8=total_fees_paid,
        last_epoch=last_epoch,
    )


def _reporter_has_open_dispute(
    reporter_id: str | None,
    reports: Mapping[str, Mapping[str, Any]],
    disputes: Mapping[str, Mapping[str, Any]],
) -> bool:
    if reporter_id is None:
        return False
    for dispute in disputes.values():
        if not bool(dispute.get("open")):
            continue
        report = reports.get(str(dispute.get("report_id")))
        if report is not None and report.get("reporter_id") == reporter_id:
            return True
    return False


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_REPLAY_BYTES:
        raise ValueError(f"reporter_economics_replay_file_too_large:{size}>{MAX_REPLAY_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("reporter economics replay root must be a JSON object")
    return obj


def _write_json(payload: Mapping[str, Any], output: Path | None) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        replay = _load_json(Path(args.replay))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = ReporterEconomicsReplayResult(
            status="inconclusive",
            errors=[f"reporter_economics_replay_load_failed:{exc}"],
        )
        _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
        return 3
    result = verify_reporter_economics_replay(replay)
    _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    _write_json(sample_replay(), Path(args.output) if args.output else None)
    return 0


def cmd_self_test(args: argparse.Namespace) -> int:
    result = verify_reporter_economics_replay(sample_replay())
    _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    verify = sub.add_parser("verify", help="verify a reporter economics replay JSON file")
    verify.add_argument("replay")
    verify.add_argument("--output")
    verify.set_defaults(func=cmd_verify)

    sample = sub.add_parser("sample", help="emit a sample accepted reporter economics replay")
    sample.add_argument("--output")
    sample.set_defaults(func=cmd_sample)

    self_test = sub.add_parser("self-test", help="run the built-in reporter economics replay check")
    self_test.add_argument("--output")
    self_test.set_defaults(func=cmd_self_test)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
